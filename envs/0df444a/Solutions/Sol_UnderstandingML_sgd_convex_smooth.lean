-- Prove2me | solution 1 for UnderstandingML.sgd_convex_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:52:27.061786+00:00
-- url     : https://prove2.me/submissions/d8ecb409-54a1-42c6-8911-5cf0dbb044e3

import Theorems.Thm_UnderstandingML_gd_lemma
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
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


section Smooth

variable {d : ℕ}

lemma hasDerivAt_along_line {f : Vec d → ℝ} (hf : Differentiable ℝ f) (x v : Vec d) (s : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪gradient f (x + s • v), v⟫_ℝ s := by
  have h1 := (hf (x + s • v)).hasGradientAt
  have h2 : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have := h1.hasFDerivAt.comp_hasDerivAt s h2
  simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this

/-- The descent lemma for a function with `β`-Lipschitz gradient. -/
lemma descent_lemma {f : Vec d → ℝ} (hf : Differentiable ℝ f) {β : ℝ}
    (hL : ∀ u w, ‖gradient f u - gradient f w‖ ≤ β * ‖u - w‖) (x y : Vec d) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + β / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  set ψ : ℝ → ℝ := fun s => f (x + s • v) - s * ⟪gradient f x, v⟫_ℝ - β / 2 * s ^ 2 * ‖v‖ ^ 2
    with hψ
  set ψ' : ℝ → ℝ := fun s => ⟪gradient f (x + s • v), v⟫_ℝ - ⟪gradient f x, v⟫_ℝ -
    β * s * ‖v‖ ^ 2 with hψ'
  have hder : ∀ s, HasDerivAt ψ (ψ' s) s := by
    intro s
    have h1 := hasDerivAt_along_line hf x v s
    have h2 := (hasDerivAt_id s).mul_const ⟪gradient f x, v⟫_ℝ
    have h3 := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
    have h := ((h1.sub h2).sub h3).congr_deriv (show _ = ψ' s by simp only [hψ']; ring)
    exact h
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun s _ => (hder s).continuousAt.continuousWithinAt)
      (fun s _ => (hder s).hasDerivWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    have hs0 : 0 ≤ s := hs.1.le
    simp only [hψ']
    have hc : ⟪gradient f (x + s • v) - gradient f x, v⟫_ℝ ≤
        ‖gradient f (x + s • v) - gradient f x‖ * ‖v‖ := real_inner_le_norm _ _
    have hl := hL (x + s • v) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0] at hl
    rw [inner_sub_left] at hc
    have : ‖gradient f (x + s • v) - gradient f x‖ * ‖v‖ ≤ β * (s * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  rw [hv, add_sub_cancel] at this
  linarith

/-- Self-boundedness of nonnegative smooth functions: `‖∇f(x)‖² ≤ 2β f(x)`. -/
lemma sq_norm_gradient_le {f : Vec d → ℝ} (hf : Differentiable ℝ f) {β : ℝ} (hβ : 0 ≤ β)
    (hL : ∀ u w, ‖gradient f u - gradient f w‖ ≤ β * ‖u - w‖) (hpos : ∀ u, 0 ≤ f u) (x : Vec d) :
    ‖gradient f x‖ ^ 2 ≤ 2 * β * f x := by
  set G := gradient f x
  have key : ∀ t : ℝ, 0 ≤ f x - t * ‖G‖ ^ 2 + β / 2 * t ^ 2 * ‖G‖ ^ 2 := by
    intro t
    have h := descent_lemma hf hL x (x - t • G)
    have e1 : x - t • G - x = -(t • G) := by abel
    rw [e1, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    have := hpos (x - t • G)
    nlinarith
  rcases hβ.eq_or_lt with h0 | hβpos
  · subst h0
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have hG : 0 < ‖G‖ ^ 2 := by nlinarith [hpos x]
    have := key ((f x + 1) / ‖G‖ ^ 2)
    rw [div_mul_cancel₀ _ hG.ne'] at this
    nlinarith
  · have := key (1 / β)
    have e : f x - 1 / β * ‖G‖ ^ 2 + β / 2 * (1 / β) ^ 2 * ‖G‖ ^ 2 = f x - ‖G‖ ^ 2 / (2 * β) := by
      field_simp; ring
    rw [e] at this
    have : ‖G‖ ^ 2 / (2 * β) ≤ f x := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at this

/-- For a differentiable convex function, the gradient is a subgradient. -/
lemma isSubgradient_gradient {f : Vec d → ℝ} (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) (x : Vec d) : IsSubgradient f x (gradient f x) := by
  intro y
  set v := y - x
  set φ : ℝ → ℝ := fun s => f (x + s • v)
  have hφc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, fun a _ b _ p q hp hq hpq => ?_⟩
    have e : x + (p • a + q • b) • v = p • (x + a • v) + q • (x + b • v) := by
      rw [smul_add, smul_add, smul_smul, smul_smul, add_smul]
      have : x = p • x + q • x := by rw [← add_smul, hpq, one_smul]
      nth_rewrite 1 [this]; abel
    simp only [φ, smul_eq_mul]
    rw [show (p * a + q * b) = p • a + q • b from rfl, e]
    exact hconv.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
  have hd := hasDerivAt_along_line hf x v 0
  simp only [zero_smul, add_zero] at hd
  have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  simp only [slope, φ, zero_smul, add_zero, one_smul, sub_zero, inv_one, smul_eq_mul, one_mul, vsub_eq_sub] at this
  rw [add_sub_cancel] at this
  rw [real_inner_comm]
  linarith

end Smooth

theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) (hnonneg : ∀ w z, 0 ≤ loss w z)
    {β : ℝ} (hβ : 0 ≤ β) (hsmooth : IsSmoothLoss β loss)
    (hmeas : Measurable (Function.uncurry loss))
    (hgrad : Measurable (Function.uncurry fun w z ↦ gradient (fun w ↦ loss w z) w)) {C : ℝ}
    (hC : ∀ z, loss 0 z ≤ C) {η : ℝ} (hη : 0 < η) (hηβ : η * β < 1) (T : ℕ) (hT : 0 < T)
    (D : Measure Z) [IsProbabilityMeasure D] (wstar : Vec d) :
    ∫ S, risk loss D (sgdAverage η (fun w z ↦ gradient (fun w ↦ loss w z) w) S) ∂(iidLaw D T) ≤
      1 / (1 - η * β) * (risk loss D wstar + ‖wstar‖ ^ 2 / (2 * η * T)) := by
  set G : Vec d → Z → Vec d := fun w z ↦ gradient (fun w ↦ loss w z) w with hGdef
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hdiff : ∀ z, Differentiable ℝ (fun w ↦ loss w z) := fun z => (hsmooth z).1
  have hLip : ∀ z u w, ‖G u z - G w z‖ ≤ β * ‖u - w‖ := fun z => (hsmooth z).2
  have hsb : ∀ w z, ‖G w z‖ ^ 2 ≤ 2 * β * loss w z := fun w z =>
    sq_norm_gradient_le (hdiff z) hβ (hLip z) (fun u => hnonneg u z) w
  have hsg : ∀ w z, IsSubgradient (fun w ↦ loss w z) w (G w z) := fun w z =>
    isSubgradient_gradient (hdiff z) (hconv z) w
  set Gc : ℝ := 1 + 2 * β * max C 0 with hGc
  have hGc0 : 0 ≤ Gc := by positivity
  have hG0 : ∀ z, ‖G 0 z‖ ≤ Gc := by
    intro z
    have h1 := hsb 0 z
    have h2 : 2 * β * loss 0 z ≤ 2 * β * max C 0 :=
      mul_le_mul_of_nonneg_left ((hC z).trans (le_max_left _ _)) (by positivity)
    nlinarith [norm_nonneg (G 0 z)]
  have hGw : ∀ w z, ‖G w z‖ ≤ Gc + β * ‖w‖ := by
    intro w z
    have := hLip z w 0
    rw [sub_zero] at this
    calc ‖G w z‖ = ‖(G w z - G 0 z) + G 0 z‖ := by rw [sub_add_cancel]
      _ ≤ ‖G w z - G 0 z‖ + ‖G 0 z‖ := norm_add_le _ _
      _ ≤ Gc + β * ‖w‖ := by linarith [hG0 z]
  have hbd : ∀ R : ℝ, ∃ K : ℝ, ∀ u : Vec d, ‖u‖ ≤ R → ∀ z, loss u z ≤ K := by
    intro R
    refine ⟨C + Gc * R + β / 2 * R ^ 2, fun u hu z => ?_⟩
    have h := descent_lemma (hdiff z) (hLip z) 0 u
    simp only [sub_zero] at h
    have hi : ⟪G 0 z, u⟫_ℝ ≤ ‖G 0 z‖ * ‖u‖ := real_inner_le_norm _ _
    have h1 : ‖G 0 z‖ * ‖u‖ ≤ Gc * R :=
      mul_le_mul (hG0 z) hu (norm_nonneg _) hGc0
    have h2 : ‖u‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
    have h3 : β / 2 * ‖u‖ ^ 2 ≤ β / 2 * R ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    have := hC z
    simp only [hGdef] at hi
    linarith
  have hiter' : ∀ t, ∃ R : ℝ, 0 ≤ R ∧ ∀ S : Fin T → Z, ‖sgdIterates η G S t‖ ≤ R := by
    intro t
    induction t with
    | zero => exact ⟨0, le_rfl, fun S => by simp [sgdIterates]⟩
    | succ t ih =>
      obtain ⟨R, hR0, hR⟩ := ih
      refine ⟨R + η * (Gc + β * R), by positivity, fun S => ?_⟩
      simp only [sgdIterates]
      have hdir : ‖(if h : t < T then G (sgdIterates η G S t) (S ⟨t, h⟩) else 0)‖ ≤
          Gc + β * R := by
        split_ifs
        · exact (hGw _ _).trans (by gcongr; exact hR S)
        · simp only [norm_zero]; positivity
      calc _ ≤ ‖sgdIterates η G S t‖ + ‖η • (if h : t < T then G (sgdIterates η G S t)
            (S ⟨t, h⟩) else 0)‖ := norm_sub_le _ _
        _ ≤ R + η * (Gc + β * R) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
          gcongr
          exact hR S
  have hiter : ∀ t, ∃ R : ℝ, ∀ S : Fin T → Z, ‖sgdIterates η G S t‖ ≤ R := fun t =>
    let ⟨R, _, hR⟩ := hiter' t; ⟨R, hR⟩
  have hκ : 0 < 1 - η * β := by linarith
  have hpt : ∀ S : Fin T → Z, (1 - η * β) * ∑ i : Fin T, loss (sgdIterates η G S i) (S i) ≤
      ∑ i : Fin T, loss wstar (S i) + ‖wstar‖ ^ 2 / (2 * η) := by
    intro S
    have hgd := (UnderstandingML.gd_lemma (sgdDir η G S) T wstar).1 η hη
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hgd
    have hdir : ∀ i : Fin T, sgdDir η G S i = G (sgdIterates η G S i) (S i) := by
      intro i; simp [sgdDir, i.2]
    simp only [← sgdIterates_eq_gdIterates, hdir] at hgd
    have hsub : ∀ i : Fin T, loss (sgdIterates η G S i) (S i) - loss wstar (S i) ≤
        ⟪sgdIterates η G S i - wstar, G (sgdIterates η G S i) (S i)⟫_ℝ := by
      intro i
      have := hsg (sgdIterates η G S i) (S i) wstar
      have e : ⟪wstar - sgdIterates η G S i, G (sgdIterates η G S i) (S i)⟫_ℝ =
          -⟪sgdIterates η G S i - wstar, G (sgdIterates η G S i) (S i)⟫_ℝ := by
        rw [← inner_neg_left, neg_sub]
      simp only at this
      linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hsub i
    rw [Finset.sum_sub_distrib] at hsum
    have hsq : ∑ i : Fin T, ‖G (sgdIterates η G S i) (S i)‖ ^ 2 ≤
        2 * β * ∑ i : Fin T, loss (sgdIterates η G S i) (S i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hsb _ _
    have hsq' := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ η / 2)
    nlinarith
  have := sgd_expectation_master loss hconv hnonneg hmeas hbd G hgrad η T hT D hiter wstar
    (1 - η * β) (‖wstar‖ ^ 2 / (2 * η)) hκ hpt
  rw [div_div, div_eq_inv_mul, ← one_div] at this
  exact this
