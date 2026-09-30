-- Prove2me | solution 1 for UnderstandingML.sgd_learns_convex_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:49:05.013654+00:00
-- url     : https://prove2.me/submissions/4b245b58-2f00-49e9-93b8-0cb6f5be759a

import Theorems.Thm_UnderstandingML_gd_lemma
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

lemma integral_indep_coord {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {T : ℕ} (i : Fin T) (Ψ : (Fin T → Z) → Z → ℝ)
    (hΨm : Measurable (Function.uncurry Ψ)) (C : ℝ) (hΨb : ∀ S z, |Ψ S z| ≤ C)
    (hΨi : ∀ S z', Ψ (Function.update S i z') = Ψ S) :
    ∫ S, Ψ S (S i) ∂(Measure.pi fun _ => D) = ∫ S, ∫ z, Ψ S z ∂D ∂(Measure.pi fun _ => D) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by have := i.pos; omega⟩
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) i with he
  have hmp : MeasurePreserving e (Measure.pi fun _ => D)
      (D.prod (Measure.pi fun _ : Fin n => D)) := measurePreserving_piFinSuccAbove (fun _ => D) i
  have hmp' := hmp.symm
  rw [← hmp'.integral_comp' (fun S => Ψ S (S i)), ← hmp'.integral_comp' (fun S => ∫ z, Ψ S z ∂D)]
  have hsymm : ∀ p : Z × (Fin n → Z), e.symm p = i.insertNth p.1 p.2 := fun p => rfl
  have key : ∀ (z z' : Z) (S' : Fin n → Z), Ψ (i.insertNth z S') = Ψ (i.insertNth z' S') := by
    intro z z' S'
    have := hΨi (i.insertNth z' S') z
    rwa [@Fin.update_insertNth n (fun _ => Z) i z' z S'] at this
  set K : (Fin n → Z) → Z → ℝ := fun S' z => Ψ (i.insertNth z S') z with hK
  have hKm : Measurable (Function.uncurry K) := by
    have : Measurable fun q : (Fin n → Z) × Z => (e.symm (q.2, q.1), q.2) :=
      (e.symm.measurable.comp (measurable_snd.prodMk measurable_fst)).prodMk measurable_snd
    exact hΨm.comp this
  have h1 : ∀ p : Z × (Fin n → Z), Ψ (e.symm p) ((e.symm p) i) = K p.2 p.1 := by
    intro p; simp [hsymm, hK]
  have h2 : ∀ p : Z × (Fin n → Z), ∫ z, Ψ (e.symm p) z ∂D = ∫ z, K p.2 z ∂D := by
    intro p
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hsymm, hK]; rw [key p.1 z p.2]
  simp_rw [h1, h2]
  have hint1 : Integrable (fun p : Z × (Fin n → Z) => K p.2 p.1)
      (D.prod (Measure.pi fun _ : Fin n => D)) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => ?_)
    · exact (hKm.comp (measurable_snd.prodMk measurable_fst)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hΨb _ _
  have hGm : StronglyMeasurable fun S' : Fin n → Z => ∫ z, K S' z ∂D :=
    hKm.stronglyMeasurable.integral_prod_right'
  have hint2 : Integrable (fun p : Z × (Fin n → Z) => ∫ z, K p.2 z ∂D)
      (D.prod (Measure.pi fun _ : Fin n => D)) := by
    refine Integrable.of_bound (hGm.comp_measurable measurable_snd).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => ?_)
    have := norm_integral_le_of_norm_le_const (μ := D) (f := fun z => K p.2 z) (C := C)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hΨb _ _)
    simpa using this
  rw [integral_prod_symm _ hint1, integral_prod _ hint2]
  simp


section SGDCommon

variable {d : ℕ} {Z : Type*}

/-- The direction used by SGD at step `t` on sample `S` (zero after `T` steps). -/
noncomputable def sgdDir (η : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) (t : ℕ) :
    Vec d :=
  if h : t < T then g (sgdIterates η g S t) (S ⟨t, h⟩) else 0

lemma sgdIterates_eq_gdIterates (η : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) :
    ∀ t, sgdIterates η g S t = gdIterates η (sgdDir η g S) t
  | 0 => rfl
  | t + 1 => by
    simp only [sgdIterates, gdIterates, sgdDir]
    rw [← sgdIterates_eq_gdIterates η g S t]

lemma sgdIterates_update (η : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) (i : Fin T)
    (z : Z) : ∀ t, t ≤ i.val → sgdIterates η g (Function.update S i z) t = sgdIterates η g S t
  | 0, _ => rfl
  | t + 1, ht => by
    simp only [sgdIterates]
    rw [sgdIterates_update η g S i z t (by omega)]
    congr 2
    split_ifs with h
    · rw [Function.update_of_ne]
      intro hti; rw [← hti] at ht; simp at ht
    · rfl

lemma measurable_sgdIterates [MeasurableSpace Z] (η : ℝ) (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (T : ℕ) :
    ∀ t, Measurable fun S : Fin T → Z => sgdIterates η g S t
  | 0 => measurable_const
  | t + 1 => by
    simp only [sgdIterates]
    have ih := measurable_sgdIterates η g hg T t
    by_cases h : t < T
    · simp only [h, dite_true]
      exact ih.sub ((hg.comp (ih.prodMk (measurable_pi_apply (⟨t, h⟩ : Fin T)))).const_smul η)
    · simp only [h, dite_false, smul_zero, sub_zero]; exact ih

lemma norm_sgdIterates_le (η : ℝ) (hη : 0 ≤ η) (g : Vec d → Z → Vec d) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hgb : ∀ w z, ‖g w z‖ ≤ ρ) {T : ℕ} (S : Fin T → Z) :
    ∀ t, ‖sgdIterates η g S t‖ ≤ t * (η * ρ)
  | 0 => by simp [sgdIterates]
  | t + 1 => by
    have ih := norm_sgdIterates_le η hη g hρ hgb S t
    simp only [sgdIterates]
    have hdir : ‖(if h : t < T then g (sgdIterates η g S t) (S ⟨t, h⟩) else 0)‖ ≤ ρ := by
      split_ifs
      · exact hgb _ _
      · simpa using hρ
    calc _ ≤ ‖sgdIterates η g S t‖ + ‖η • (if h : t < T then g (sgdIterates η g S t)
            (S ⟨t, h⟩) else 0)‖ := norm_sub_le _ _
      _ ≤ t * (η * ρ) + η * ρ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
          gcongr
      _ = ((t + 1 : ℕ) : ℝ) * (η * ρ) := by push_cast; ring

end SGDCommon

section Master

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- Integrability of a bounded measurable real function under a probability measure. -/
lemma integrable_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {F : α → ℝ} (hF : Measurable F) (K : ℝ) (hK : ∀ a, |F a| ≤ K) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hK a)

lemma risk_convexOn (loss : Vec d → Z → ℝ) (D : Measure Z)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z))
    (hint : ∀ u, Integrable (loss u) D) : ConvexOn ℝ Set.univ (risk loss D) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [risk, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hint x).const_mul a)
    ((hint y).const_mul b)]
  refine integral_mono (hint _) (((hint x).const_mul a).add ((hint y).const_mul b)) fun z => ?_
  have := (hconv z).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simpa [smul_eq_mul] using this

/-- **Master bound for SGD in expectation.** If along every sample path
`κ ∑ᵢ ℓ(w⁽ⁱ⁾, zᵢ) ≤ ∑ᵢ ℓ(w, zᵢ) + c`, then `E[L_D(w̄)] ≤ (L_D(w) + c/T)/κ`. -/
lemma sgd_expectation_master (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) (hnonneg : ∀ w z, 0 ≤ loss w z)
    (hmeas : Measurable (Function.uncurry loss))
    (hbd : ∀ R : ℝ, ∃ K : ℝ, ∀ u : Vec d, ‖u‖ ≤ R → ∀ z, loss u z ≤ K)
    (g : Vec d → Z → Vec d) (hg : Measurable (Function.uncurry g)) (η : ℝ) (T : ℕ)
    (hT : 0 < T) (D : Measure Z) [IsProbabilityMeasure D]
    (hiter : ∀ t, ∃ R : ℝ, ∀ S : Fin T → Z, ‖sgdIterates η g S t‖ ≤ R)
    (w : Vec d) (κ c : ℝ) (hκ : 0 < κ)
    (hpt : ∀ S : Fin T → Z,
      κ * ∑ i : Fin T, loss (sgdIterates η g S i) (S i) ≤ ∑ i : Fin T, loss w (S i) + c) :
    ∫ S, risk loss D (sgdAverage η g S) ∂(iidLaw D T) ≤ (risk loss D w + c / T) / κ := by
  have hμ : IsProbabilityMeasure (iidLaw D T) := by unfold iidLaw; infer_instance
  set μ := iidLaw D T with hμdef
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  -- measurability and bounds
  have hWm : ∀ t, Measurable fun S : Fin T → Z => sgdIterates η g S t :=
    measurable_sgdIterates η g hg T
  have hlossint : ∀ u, Integrable (loss u) D := by
    intro u
    obtain ⟨K, hK⟩ := hbd ‖u‖
    refine integrable_of_bdd D hmeas.of_uncurry_left K fun z => ?_
    rw [abs_of_nonneg (hnonneg u z)]; exact hK u le_rfl z
  have hPsi : ∀ t, ∃ K, ∀ S : Fin T → Z, ∀ z, |loss (sgdIterates η g S t) z| ≤ K := by
    intro t
    obtain ⟨R, hR⟩ := hiter t
    obtain ⟨K, hK⟩ := hbd R
    exact ⟨K, fun S z => by rw [abs_of_nonneg (hnonneg _ _)]; exact hK _ (hR S) z⟩
  have hPsim : ∀ t, Measurable (Function.uncurry fun (S : Fin T → Z) z =>
      loss (sgdIterates η g S t) z) := fun t =>
    hmeas.comp (((hWm t).comp measurable_fst).prodMk measurable_snd)
  have hriskm : ∀ t, Measurable fun S : Fin T → Z => risk loss D (sgdIterates η g S t) :=
    fun t => ((hPsim t).stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hriskb : ∀ t, ∃ K, ∀ S : Fin T → Z, |risk loss D (sgdIterates η g S t)| ≤ K := by
    intro t
    obtain ⟨K, hK⟩ := hPsi t
    refine ⟨K, fun S => ?_⟩
    have := norm_integral_le_of_norm_le_const (μ := D) (f := fun z => loss (sgdIterates η g S t) z)
      (C := K) (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hK S z)
    simpa [risk] using this
  -- integrability of the three families
  have hfint : ∀ i : Fin T, Integrable (fun S : Fin T → Z => loss (sgdIterates η g S i) (S i)) μ := by
    intro i
    obtain ⟨K, hK⟩ := hPsi i
    exact integrable_of_bdd μ (hmeas.comp ((hWm i).prodMk (measurable_pi_apply i))) K
      fun S => hK S (S i)
  have hhint : ∀ i : Fin T, Integrable (fun S : Fin T → Z => loss w (S i)) μ := by
    intro i
    obtain ⟨K, hK⟩ := hbd ‖w‖
    exact integrable_of_bdd μ (hmeas.of_uncurry_left.comp (measurable_pi_apply i)) K
      fun S => by rw [abs_of_nonneg (hnonneg _ _)]; exact hK w le_rfl _
  have hrint : ∀ i : Fin T, Integrable (fun S : Fin T → Z => risk loss D (sgdIterates η g S i)) μ := by
    intro i
    obtain ⟨K, hK⟩ := hriskb i
    exact integrable_of_bdd μ (hriskm i) K hK
  -- independence
  have hf_eq : ∀ i : Fin T, ∫ S, loss (sgdIterates η g S i) (S i) ∂μ =
      ∫ S, risk loss D (sgdIterates η g S i) ∂μ := by
    intro i
    obtain ⟨K, hK⟩ := hPsi i
    exact integral_indep_coord D i (fun S z => loss (sgdIterates η g S i) z) (hPsim i) K hK
      fun S z' => by rw [sgdIterates_update η g S i z' i le_rfl]
  have hh_eq : ∀ i : Fin T, ∫ S, loss w (S i) ∂μ = risk loss D w := by
    intro i
    obtain ⟨K, hK⟩ := hbd ‖w‖
    have := integral_indep_coord D i (fun _ z => loss w z)
      (hmeas.of_uncurry_left.comp measurable_snd) K
      (fun S z => by rw [abs_of_nonneg (hnonneg _ _)]; exact hK w le_rfl _) (fun _ _ => rfl)
    rw [hμdef, iidLaw, this, integral_const, probReal_univ, one_smul]; rfl
  -- integrate the pathwise inequality
  have hint_pt : κ * ∑ i : Fin T, ∫ S, risk loss D (sgdIterates η g S i) ∂μ ≤
      T * risk loss D w + c := by
    have hmono := integral_mono (μ := μ)
      (f := fun S => κ * ∑ i : Fin T, loss (sgdIterates η g S i) (S i))
      (g := fun S => ∑ i : Fin T, loss w (S i) + c)
      ((integrable_finsetSum _ fun i _ => hfint i).const_mul κ)
      ((integrable_finsetSum _ fun i _ => hhint i).add (integrable_const c)) hpt
    have e1 : ∫ S, κ * ∑ i : Fin T, loss (sgdIterates η g S i) (S i) ∂μ =
        κ * ∑ i : Fin T, ∫ S, risk loss D (sgdIterates η g S i) ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ fun i _ => hfint i]
      simp only [hf_eq]
    have e2 : ∫ S, (∑ i : Fin T, loss w (S i) + c) ∂μ = T * risk loss D w + c := by
      rw [integral_add (integrable_finsetSum _ fun i _ => hhint i) (integrable_const c),
        integral_finsetSum _ fun i _ => hhint i, integral_const, probReal_univ, one_smul]
      simp only [hh_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [e1, e2] at hmono
    exact hmono
  -- Jensen for the risk
  have hjensen : ∀ S : Fin T → Z, risk loss D (sgdAverage η g S) ≤
      (T : ℝ)⁻¹ * ∑ i : Fin T, risk loss D (sgdIterates η g S i) := by
    intro S
    have := (risk_convexOn loss D hconv hlossint).map_sum_le (t := Finset.range T)
      (w := fun _ => (T : ℝ)⁻¹) (p := fun t => sgdIterates η g S t) (fun _ _ => by positivity)
      (by simp [Finset.card_range]; field_simp) (fun _ _ => Set.mem_univ _)
    rw [Fin.sum_univ_eq_sum_range (fun t => risk loss D (sgdIterates η g S t)) T,
      Finset.mul_sum]
    simpa [sgdAverage, Finset.smul_sum] using this
  have hrisknn : ∀ u, 0 ≤ risk loss D u := fun u => integral_nonneg fun z => hnonneg u z
  calc ∫ S, risk loss D (sgdAverage η g S) ∂μ
      ≤ ∫ S, (T : ℝ)⁻¹ * ∑ i : Fin T, risk loss D (sgdIterates η g S i) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun S => hrisknn _)
          ((integrable_finsetSum _ fun i _ => hrint i).const_mul _)
          (Filter.Eventually.of_forall hjensen)
    _ = (T : ℝ)⁻¹ * ∑ i : Fin T, ∫ S, risk loss D (sgdIterates η g S i) ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hrint i]
    _ ≤ (risk loss D w + c / T) / κ := by
        rw [le_div_iff₀ hκ]
        have : (T : ℝ)⁻¹ * (κ * ∑ i : Fin T, ∫ S, risk loss D (sgdIterates η g S i) ∂μ) ≤
            (T : ℝ)⁻¹ * (T * risk loss D w + c) := by gcongr
        calc _ = (T : ℝ)⁻¹ * (κ * ∑ i : Fin T, ∫ S, risk loss D (sgdIterates η g S i) ∂μ) := by
              ring
          _ ≤ _ := this
          _ = _ := by field_simp

end Master

/-- A subgradient of a `ρ`-Lipschitz function has norm at most `ρ`. -/
lemma norm_le_of_isSubgradient_of_lipschitz {d : ℕ} {f : Vec d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlip : ∀ u v, |f u - f v| ≤ ρ * ‖u - v‖) {w v : Vec d} (hv : IsSubgradient f w v) :
    ‖v‖ ≤ ρ := by
  have h1 := hv (w + v)
  have h2 := hlip (w + v) w
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1 h2
  have h3 : f (w + v) - f w ≤ ρ * ‖v‖ := le_trans (le_abs_self _) h2
  have h4 : ‖v‖ ^ 2 ≤ ρ * ‖v‖ := by linarith
  rcases (norm_nonneg v).eq_or_lt with h | h
  · rw [← h]; exact hρ
  · nlinarith

theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (H : Set (Vec d))
    (loss : Vec d → Z → ℝ) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hprob : ConvexLipschitzBounded H loss ρ B) (hmeas : Measurable (Function.uncurry loss))
    (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ} (hC : ∀ z, loss 0 z ≤ C) (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (hsel : IsLossSubgradientSelector loss g) (ε : ℝ)
    (hε : 0 < ε) (T : ℕ) (hT : B ^ 2 * ρ ^ 2 / ε ^ 2 ≤ T) (D : Measure Z)
    [IsProbabilityMeasure D] :
    ∀ w ∈ H, ∫ S, risk loss D (sgdAverage (B / (ρ * Real.sqrt T)) g S) ∂(iidLaw D T) ≤
      risk loss D w + ε := by
  intro w hw
  obtain ⟨-, hHB, hconv, hlip⟩ := hprob
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT
  have hT0 : 0 < T := by exact_mod_cast hTpos
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  set η := B / (ρ * Real.sqrt T) with hηdef
  have hη : 0 < η := by positivity
  have hgb : ∀ u z, ‖g u z‖ ≤ ρ := fun u z =>
    norm_le_of_isSubgradient_of_lipschitz hρ.le (fun a b => hlip z a b) (hsel u z)
  have hbd : ∀ R : ℝ, ∃ K : ℝ, ∀ u : Vec d, ‖u‖ ≤ R → ∀ z, loss u z ≤ K := by
    intro R
    refine ⟨C + ρ * R, fun u hu z => ?_⟩
    have h1 := le_trans (le_abs_self _) (hlip z u 0)
    rw [sub_zero] at h1
    have := hC z
    nlinarith
  have hiter : ∀ t, ∃ R : ℝ, ∀ S : Fin T → Z, ‖sgdIterates η g S t‖ ≤ R := fun t =>
    ⟨t * (η * ρ), fun S => norm_sgdIterates_le η hη.le g hρ.le hgb S t⟩
  have hεb : B * ρ / Real.sqrt T ≤ ε := by
    rw [div_le_iff₀ hs]
    have : B * ρ / ε ≤ Real.sqrt T := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, mul_pow]; exact hT
    rw [div_le_iff₀ hε] at this
    linarith
  have hpt : ∀ S : Fin T → Z, 1 * ∑ i : Fin T, loss (sgdIterates η g S i) (S i) ≤
      ∑ i : Fin T, loss w (S i) + T * ε := by
    intro S
    have hvb : ∀ t < T, ‖sgdDir η g S t‖ ≤ ρ := by
      intro t ht; simp only [sgdDir, ht, dite_true]; exact hgb _ _
    have hgd := (UnderstandingML.gd_lemma (sgdDir η g S) T w).2 B ρ hB hρ hvb (hHB w hw) hT0
    rw [← Fin.sum_univ_eq_sum_range] at hgd
    have hdir : ∀ i : Fin T, sgdDir η g S i = g (sgdIterates η g S i) (S i) := by
      intro i; simp [sgdDir, i.2]
    rw [← hηdef] at hgd
    simp only [← sgdIterates_eq_gdIterates, hdir] at hgd
    have hsub : ∀ i : Fin T, loss (sgdIterates η g S i) (S i) - loss w (S i) ≤
        ⟪sgdIterates η g S i - w, g (sgdIterates η g S i) (S i)⟫_ℝ := by
      intro i
      have := hsel (sgdIterates η g S i) (S i) w
      have e : ⟪w - sgdIterates η g S i, g (sgdIterates η g S i) (S i)⟫_ℝ =
          -⟪sgdIterates η g S i - w, g (sgdIterates η g S i) (S i)⟫_ℝ := by
        rw [← inner_neg_left, neg_sub]
      simp only at this
      linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hsub i
    rw [Finset.sum_sub_distrib] at hsum
    rw [div_le_iff₀ hTpos] at hgd
    have : B * ρ / Real.sqrt T * T ≤ ε * T := by gcongr
    linarith
  have := sgd_expectation_master loss hconv hnonneg hmeas hbd g hg η T hT0 D hiter w 1 (T * ε)
    one_pos hpt
  rwa [mul_div_cancel_left₀ _ hTpos.ne', div_one] at this
