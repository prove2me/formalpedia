-- Prove2me | solution 1 for SampleMechDesign.theorem_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T16:05:50.089923+00:00
-- url     : https://prove2.me/submissions/2456b7d5-5c7f-48ab-8bc9-03cf3717f919

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Theorems.Thm_UnderstandingML_rademacher_generalization
import Theorems.Thm_UnderstandingML_chaining_corollary
import Theorems.Thm_SampleMechDesign_pdim_l1_packing

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace SampleMechDesign.T38Aux

open FoundationsML.Regression BartlettBousquetMendelson.LocalRad UnderstandingML

/-- Clamp to `[0, U]`. -/
noncomputable def clampU (U y : ℝ) : ℝ := max 0 (min U y)

lemma clampU_mem {U : ℝ} (hU : 0 ≤ U) (y : ℝ) : clampU U y ∈ Set.Icc 0 U :=
  ⟨le_max_left _ _, max_le hU (min_le_left _ _)⟩

lemma clampU_of_mem {U y : ℝ} (h : y ∈ Set.Icc 0 U) : clampU U y = y := by
  unfold clampU; rw [min_eq_right h.2, max_eq_right h.1]

lemma clampU_lt_iff {U t y : ℝ} (ht0 : 0 ≤ t) (htU : t < U) : t < clampU U y ↔ t < y := by
  unfold clampU
  constructor
  · intro h
    by_contra hy; push Not at hy
    have : max 0 (min U y) ≤ t := max_le ht0 (le_trans (min_le_right _ _) hy)
    linarith
  · intro h
    exact lt_of_lt_of_le (lt_min htU h) (le_max_right _ _)

lemma continuous_clampU (U : ℝ) : Continuous (clampU U) := by
  unfold clampU; fun_prop

/-- The loss used for the two one-sided bounds. -/
noncomputable def lossS {X : Type*} (U s : ℝ) (f : X → ℝ) (z : X) : ℝ := s * (clampU U (f z) - U / 2)

lemma abs_lossS_le {X : Type*} {U s : ℝ} (hU : 0 ≤ U) (hs : |s| = 1) (f : X → ℝ) (z : X) :
    |lossS U s f z| ≤ U / 2 := by
  unfold lossS
  rw [abs_mul, hs, one_mul, abs_le]
  have := clampU_mem hU (f z)
  constructor <;> linarith [this.1, this.2]

lemma measurable_lossS {X : Type*} [MeasurableSpace X] (U s : ℝ) {f : X → ℝ}
    (hf : Measurable f) : Measurable (lossS U s f) := by
  unfold lossS
  exact measurable_const.mul (((continuous_clampU U).measurable.comp hf).sub measurable_const)

/-- Pseudo-dimension does not grow under clamping. -/
lemma shatters_of_clamp {X : Type*} {F : Set (X → ℝ)} {U : ℝ} {m : ℕ} (z : Fin m → X)
    (h : Shatters ((fun f : X → ℝ => fun x => clampU U (f x)) '' F) z) : Shatters F z := by
  obtain ⟨t, ht⟩ := h
  have hbnd : ∀ i, 0 ≤ t i ∧ t i < U := by
    intro i
    obtain ⟨g, ⟨f, -, rfl⟩, hg⟩ := ht (fun _ => true)
    obtain ⟨g', ⟨f', -, rfl⟩, hg'⟩ := ht (fun _ => false)
    have h1 : t i < max 0 (min U (f (z i))) := (hg i).1 rfl
    have h3 : ¬ t i < max 0 (min U (f' (z i))) := fun h => absurd ((hg' i).2 h) (by simp)
    push Not at h3
    have h0 : 0 ≤ t i := le_trans (le_max_left _ _) h3
    refine ⟨h0, ?_⟩
    rcases lt_max_iff.1 h1 with h | h
    · linarith
    · exact lt_of_lt_of_le h (min_le_left _ _)
  refine ⟨t, fun b => ?_⟩
  obtain ⟨g, ⟨f, hfF, rfl⟩, hg⟩ := ht b
  refine ⟨f, hfF, fun i => ?_⟩
  rw [hg i]
  exact clampU_lt_iff (hbnd i).1 (hbnd i).2

/-- A supremum over `F` equals the supremum over a pointwise-dense subclass `F₀`. -/
lemma iSup_eq_of_approx {ι : Type*} {F F₀ : Set ι} (hF₀ : F₀ ⊆ F) (φ : ι → ℝ) (C : ℝ)
    (hC : ∀ h ∈ F, φ h ≤ C)
    (happ : ∀ f ∈ F, ∃ u : ℕ → ι, (∀ k, u k ∈ F₀) ∧ Tendsto (fun k => φ (u k)) atTop (𝓝 (φ f))) :
    ⨆ h : F, φ h = ⨆ h : F₀, φ h := by
  rcases isEmpty_or_nonempty F with hE | ⟨⟨f, hf⟩⟩
  · have : IsEmpty F₀ := ⟨fun x => hE.false ⟨x.1, hF₀ x.2⟩⟩
    rw [iSup_of_empty', iSup_of_empty']
  · obtain ⟨u, hu, -⟩ := happ f hf
    have : Nonempty F₀ := ⟨⟨u 0, hu 0⟩⟩
    have : Nonempty F := ⟨⟨f, hf⟩⟩
    have hbF : BddAbove (Set.range fun h : F => φ h) := ⟨C, by
      rintro _ ⟨h, rfl⟩; exact hC h.1 h.2⟩
    have hbF₀ : BddAbove (Set.range fun h : F₀ => φ h) := ⟨C, by
      rintro _ ⟨h, rfl⟩; exact hC h.1 (hF₀ h.2)⟩
    apply le_antisymm
    · apply ciSup_le
      rintro ⟨g, hg⟩
      obtain ⟨v, hv, hlim⟩ := happ g hg
      exact le_of_tendsto' hlim (fun k => le_ciSup hbF₀ ⟨v k, hv k⟩)
    · apply ciSup_le
      rintro ⟨g, hg⟩
      exact le_ciSup hbF ⟨g, hF₀ hg⟩

lemma iSup_evalSet_lossClass {Z Hyp : Type*} (loss : Hyp → Z → ℝ) (H : Set Hyp) {m : ℕ}
    (S : Fin m → Z) (ψ : (Fin m → ℝ) → ℝ) :
    ⨆ a : evalSet (lossClass loss H) S, ψ a = ⨆ h : H, ψ (fun i => loss h (S i)) := by
  let g : H → evalSet (lossClass loss H) S := fun h =>
    ⟨fun i => loss h (S i), ⟨loss h, ⟨h, h.2, rfl⟩, rfl⟩⟩
  have hg : Function.Surjective g := by
    rintro ⟨a, ⟨f, ⟨h, hh, rfl⟩, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  exact (hg.iSup_comp (fun a => ψ a)).symm

/-- Every `a` in `A` is within `r` of a maximal `r`-separated finite subset. -/
lemma coveringNumber_le_of_sep {m : ℕ} (A : Set (Fin m → ℝ)) (r : ℝ) (hr : 0 ≤ r) (M : ℕ)
    (hM : ∀ P : Finset (Fin m → ℝ), (∀ a ∈ P, a ∈ A) →
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → r < eucNorm (a - b)) → P.card ≤ M) :
    ∃ P : Finset (Fin m → ℝ), IsCover r A P ∧ P.card ≤ M := by
  classical
  let T : Set ℕ := {n | ∃ P : Finset (Fin m → ℝ), (∀ a ∈ P, a ∈ A) ∧
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → r < eucNorm (a - b)) ∧ P.card = n}
  have hT0 : (0 : ℕ) ∈ T := ⟨∅, by simp, by simp, rfl⟩
  have hTb : BddAbove T := ⟨M, by rintro n ⟨P, h1, h2, rfl⟩; exact hM P h1 h2⟩
  obtain ⟨P, hPA, hPs, hPc⟩ := Nat.sSup_mem ⟨0, hT0⟩ hTb
  refine ⟨P, ?_, hPc ▸ hM P hPA hPs⟩
  intro a ha
  by_contra hcon
  push Not at hcon
  have hnot : a ∉ P := by
    intro haP
    have := hcon a haP
    simp [eucNorm] at this
    linarith
  have hsymm : ∀ x y : Fin m → ℝ, eucNorm (x - y) = eucNorm (y - x) := by
    intro x y; unfold eucNorm; congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_); simp only [Pi.sub_apply]; ring
  have hmem : (insert a P).card ∈ T := by
    refine ⟨insert a P, ?_, ?_, rfl⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · exact hPA x hx
    · intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact (hxy (hx.trans hy.symm)).elim
      · subst hx; exact hcon y hy
      · subst hy; rw [hsymm]; exact hcon x hx
      · exact hPs x hx y hy hxy
  have := le_csSup hTb hmem
  rw [Finset.card_insert_of_notMem hnot, hPc] at this
  omega


lemma abs_empRisk_le {X : Type*} {U s : ℝ} (hU : 0 ≤ U) (hs : |s| = 1) {m : ℕ} (S : Fin m → X)
    (f : X → ℝ) : |empRisk (lossS U s) S f| ≤ U / 2 := by
  unfold empRisk
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp; positivity
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rw [abs_div, Nat.abs_cast, div_le_iff₀ hm']
    calc |∑ i, lossS U s f (S i)| ≤ ∑ i, |lossS U s f (S i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, U / 2 := Finset.sum_le_sum (fun i _ => abs_lossS_le hU hs f (S i))
      _ = U / 2 * m := by simp [mul_comm]

lemma abs_risk_le {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    {U s : ℝ} (hU : 0 ≤ U) (hs : |s| = 1) {f : X → ℝ} (hf : Measurable f) :
    |risk (lossS U s) D f| ≤ U / 2 := by
  unfold risk
  have hint : Integrable (lossS U s f) D :=
    Integrable.of_bound (measurable_lossS U s hf).aestronglyMeasurable (U / 2)
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact abs_lossS_le hU hs f z))
  rw [abs_le]
  constructor
  · have := integral_mono (integrable_const (-(U / 2))) hint
      (fun z => (abs_le.1 (abs_lossS_le hU hs f z)).1)
    simpa using this
  · have := integral_mono hint (integrable_const (U / 2))
      (fun z => (abs_le.1 (abs_lossS_le hU hs f z)).2)
    simpa using this

/-- Measurability hypotheses of `rademacher_generalization` for the clamped losses. -/
lemma meas_glue {X : Type*} [MeasurableSpace X] {F : Set (X → ℝ)} (hF : ∀ f ∈ F, Measurable f)
    (hpm : IsPointwiseMeasurableClass F) (D : Measure X) [IsProbabilityMeasure D] {U s : ℝ}
    (hU : 0 ≤ U) (hs : |s| = 1) (m : ℕ) :
    Measurable (fun S : Fin m → X ↦ representativeness (lossS U s) F D S) ∧
    Measurable (fun S : Fin m → X ↦ rademacher (evalSet (lossClass (lossS U s) F) S)) ∧
    Measurable (fun p : (Fin m → X) × (Fin m → X) ↦
      ⨆ h : F, (empRisk (lossS U s) p.2 (h : X → ℝ) - empRisk (lossS U s) p.1 (h : X → ℝ))) := by
  obtain ⟨F₀, hF₀F, hF₀c, happ⟩ := hpm
  have : Countable F₀ := hF₀c.to_subtype
  have hψ : Continuous fun y => s * (clampU U y - U / 2) :=
    continuous_const.mul ((continuous_clampU U).sub continuous_const)
  -- pointwise convergence of the losses along the approximating sequences
  have hL : ∀ f ∈ F, ∃ u : ℕ → X → ℝ, (∀ k, u k ∈ F₀) ∧
      ∀ z, Tendsto (fun k => lossS U s (u k) z) atTop (𝓝 (lossS U s f z)) := by
    intro f hf
    obtain ⟨u, hu, hlim⟩ := happ f hf
    exact ⟨u, hu, fun z => (hψ.tendsto _).comp (hlim z)⟩
  have hE : ∀ {u : ℕ → X → ℝ} {f : X → ℝ}, (∀ z, Tendsto (fun k => lossS U s (u k) z) atTop
      (𝓝 (lossS U s f z))) → ∀ (S : Fin m → X),
      Tendsto (fun k => empRisk (lossS U s) S (u k)) atTop (𝓝 (empRisk (lossS U s) S f)) := by
    intro u f h S
    unfold empRisk
    exact (tendsto_finsetSum _ (fun i _ => h (S i))).div_const _
  have hR : ∀ {u : ℕ → X → ℝ} {f : X → ℝ}, (∀ k, u k ∈ F₀) → (∀ z, Tendsto
      (fun k => lossS U s (u k) z) atTop (𝓝 (lossS U s f z))) →
      Tendsto (fun k => risk (lossS U s) D (u k)) atTop (𝓝 (risk (lossS U s) D f)) := by
    intro u f hu h
    unfold risk
    exact tendsto_integral_of_dominated_convergence (fun _ => U / 2)
      (fun k => (measurable_lossS U s (hF _ (hF₀F (hu k)))).aestronglyMeasurable)
      (integrable_const _)
      (fun k => ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact abs_lossS_le hU hs _ z))
      (ae_of_all _ h)
  have hmE : ∀ h : F₀, Measurable (fun S : Fin m → X => empRisk (lossS U s) S (h : X → ℝ)) := by
    intro h
    unfold empRisk
    exact (Finset.measurable_sum _ (fun i _ =>
      (measurable_lossS U s (hF _ (hF₀F h.2))).comp (measurable_pi_apply i))).div_const _
  refine ⟨?_, ?_, ?_⟩
  · have heq : (fun S : Fin m → X ↦ representativeness (lossS U s) F D S) =
        fun S => ⨆ h : F₀, (risk (lossS U s) D (h : X → ℝ) - empRisk (lossS U s) S (h : X → ℝ)) := by
      funext S
      unfold representativeness
      refine iSup_eq_of_approx hF₀F (fun h => risk (lossS U s) D h - empRisk (lossS U s) S h)
        (U / 2 + U / 2) ?_ ?_
      · intro h hh
        have h1 := abs_le.1 (abs_risk_le D hU hs (hF h hh))
        have h2 := abs_le.1 (abs_empRisk_le hU hs S h)
        linarith [h1.2, h2.1]
      · intro f hf
        obtain ⟨u, hu, hlim⟩ := hL f hf
        exact ⟨u, hu, (hR hu hlim).sub (hE hlim S)⟩
    rw [heq]
    exact Measurable.iSup (fun h => measurable_const.sub (hmE h))
  · have heq : (fun S : Fin m → X ↦ rademacher (evalSet (lossClass (lossS U s) F) S)) =
        fun S => (1 / (m : ℝ)) * ((1 / 2 ^ m) * ∑ σ : Fin m → Bool,
          ⨆ h : F₀, ∑ i, signVec σ i * lossS U s (h : X → ℝ) (S i)) := by
      funext S
      unfold rademacher
      congr 2
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [iSup_evalSet_lossClass (lossS U s) F S (fun a => ∑ i, signVec σ i * a i)]
      refine iSup_eq_of_approx hF₀F (fun h => ∑ i, signVec σ i * lossS U s h (S i))
        (∑ _i : Fin m, U / 2) ?_ ?_
      · intro h _
        refine Finset.sum_le_sum (fun i _ => ?_)
        have := abs_le.1 (abs_lossS_le hU hs h (S i))
        unfold signVec
        split_ifs <;> linarith [this.1, this.2]
      · intro f hf
        obtain ⟨u, hu, hlim⟩ := hL f hf
        exact ⟨u, hu, tendsto_finsetSum _ (fun i _ => (hlim (S i)).const_mul _)⟩
    rw [heq]
    exact measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ (fun σ _ =>
      Measurable.iSup (fun h => Finset.measurable_sum _ (fun i _ => measurable_const.mul
        ((measurable_lossS U s (hF _ (hF₀F h.2))).comp (measurable_pi_apply i)))))))
  · have heq : (fun p : (Fin m → X) × (Fin m → X) ↦
        ⨆ h : F, (empRisk (lossS U s) p.2 (h : X → ℝ) - empRisk (lossS U s) p.1 (h : X → ℝ))) =
        fun p => ⨆ h : F₀, (empRisk (lossS U s) p.2 (h : X → ℝ) -
          empRisk (lossS U s) p.1 (h : X → ℝ)) := by
      funext p
      refine iSup_eq_of_approx hF₀F (fun h => empRisk (lossS U s) p.2 h -
        empRisk (lossS U s) p.1 h) (U / 2 + U / 2) ?_ ?_
      · intro h _
        have h1 := abs_le.1 (abs_empRisk_le hU hs p.2 h)
        have h2 := abs_le.1 (abs_empRisk_le hU hs p.1 h)
        linarith [h1.2, h2.1]
      · intro f hf
        obtain ⟨u, hu, hlim⟩ := hL f hf
        exact ⟨u, hu, (hE hlim p.2).sub (hE hlim p.1)⟩
    rw [heq]
    exact Measurable.iSup (fun h => ((hmE h).comp measurable_snd).sub ((hmE h).comp measurable_fst))

lemma log_bound (k : ℕ) :
    2 * Real.log (5 * Real.exp 1 * 4 ^ (k + 1)) ≤ (3 + 2 * (k : ℝ)) ^ 2 := by
  have h2 := Real.log_two_lt_d9
  have h20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h5 : Real.log 5 ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_exp, Real.log_pow, h4]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  nlinarith

/-- Dudley chaining + pseudo-dimension packing: `R(ℓ ∘ F ∘ S) ≤ 21 U √d / √N`. -/
lemma rad_bound {X : Type*} {F : Set (X → ℝ)} (hFne : F.Nonempty) {U : ℝ} (hU : 0 ≤ U) {s : ℝ}
    (hs : |s| = 1) {d : ℕ} (hd : ∀ (m : ℕ) (z : Fin m → X), Shatters F z → m ≤ d)
    {N : ℕ} (hN : 0 < N) (S : Fin N → X) :
    rademacher (evalSet (lossClass (lossS U s) F) S) ≤ 21 * U * Real.sqrt d / Real.sqrt N := by
  classical
  set A := evalSet (lossClass (lossS U s) F) S with hAdef
  set G : Set (X → ℝ) := (fun f : X → ℝ => fun x => clampU U (f x)) '' F with hGdef
  have hdG : ∀ (m : ℕ) (z : Fin m → X), Shatters G z → m ≤ d :=
    fun m z h => hd m z (shatters_of_clamp z h)
  have hGB : ∀ g ∈ G, ∀ i, g (S i) ∈ Set.Icc 0 U := by
    rintro g ⟨f, -, rfl⟩ i; exact clampU_mem hU _
  have hAne : A.Nonempty := by
    obtain ⟨f, hf⟩ := hFne
    exact ⟨_, lossS U s f, ⟨f, hf, rfl⟩, rfl⟩
  have hArep : ∀ a ∈ A, ∃ g ∈ G, a = fun i => s * (g (S i) - U / 2) := by
    rintro a ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set sN := Real.sqrt (N : ℝ) with hsN
  have hsN0 : 0 < sN := Real.sqrt_pos.2 hNr
  have hsN2 : sN ^ 2 = N := Real.sq_sqrt hNr.le
  set c : ℝ := U / 2 * sN with hc
  have hc0 : 0 ≤ c := by positivity
  have hcA : ∀ a ∈ A, eucNorm (a - 0) ≤ c := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := hArep a ha
    unfold eucNorm
    have : c = Real.sqrt (N * (U / 2) ^ 2) := by
      rw [Real.sqrt_mul hNr.le, Real.sqrt_sq (by positivity), hc]; ring
    rw [this]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ((fun i => s * (g (S i) - U / 2)) - 0) i ^ 2 ≤ ∑ _i : Fin N, (U / 2) ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
          have hm := hGB g hg i
          rw [mul_pow, hs2, one_mul]
          apply sq_le_sq' <;> linarith [hm.1, hm.2]
      _ = N * (U / 2) ^ 2 := by simp
  -- covering numbers
  have hcov : ∀ k : ℕ, Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat) ≤
      d * (3 + 2 * (k : ℝ)) ^ 2 := by
    intro k
    have hrhs : 0 ≤ (d : ℝ) * (3 + 2 * (k : ℝ)) ^ 2 := by positivity
    have hr0 : 0 ≤ c * (2 : ℝ)⁻¹ ^ k := by positivity
    -- a cover of bounded size gives the bound
    have key : ∀ (M : ℕ), (∀ P : Finset (Fin N → ℝ), (∀ a ∈ P, a ∈ A) →
        (∀ a ∈ P, ∀ b ∈ P, a ≠ b → c * (2 : ℝ)⁻¹ ^ k < eucNorm (a - b)) → P.card ≤ M) →
        Real.log M ≤ d * (3 + 2 * (k : ℝ)) ^ 2 →
        Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat) ≤ d * (3 + 2 * (k : ℝ)) ^ 2 := by
      intro M hM hlog
      obtain ⟨P, hPc, hPM⟩ := coveringNumber_le_of_sep A _ hr0 M hM
      have hle : (coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat ≤ M := by
        apply ENat.toNat_le_of_le_natCast
        calc coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A ≤ (P.card : ℕ∞) := iInf₂_le P hPc
          _ ≤ M := by exact_mod_cast hPM
      rcases Nat.eq_zero_or_pos (coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat with h0 | hpos
      · rw [h0]; simpa using hrhs
      · exact le_trans (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)) hlog
    rcases hU.eq_or_lt with hU0 | hUpos
    · -- `U = 0`: all loss vectors coincide
      refine key 1 ?_ (by simpa using hrhs)
      intro P hPA hPs
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      apply hab
      obtain ⟨g, hg, rfl⟩ := hArep a (hPA a ha)
      obtain ⟨g', hg', rfl⟩ := hArep b (hPA b hb)
      funext i
      have h1 := hGB g hg i
      have h2 := hGB g' hg' i
      rw [← hU0] at h1 h2
      have e1 : g (S i) = 0 := le_antisymm h1.2 h1.1
      have e2 : g' (S i) = 0 := le_antisymm h2.2 h2.1
      simp only [e1, e2]
    · set ε : ℝ := U * (4 : ℝ)⁻¹ ^ (k + 1) with hε
      have hε0 : 0 < ε := by positivity
      have hεU : ε ≤ U := by
        rw [hε]
        have : (4 : ℝ)⁻¹ ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      set L : ℝ := 2 * d * Real.log (5 * Real.exp 1 * U / ε) with hL
      have hratio : 5 * Real.exp 1 * U / ε = 5 * Real.exp 1 * 4 ^ (k + 1) := by
        rw [hε, inv_pow]; field_simp
      have hLb : L ≤ d * (3 + 2 * (k : ℝ)) ^ 2 := by
        rw [hL, hratio]
        have := log_bound k
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith
      have hr2 : (c * (2 : ℝ)⁻¹ ^ k) ^ 2 = N * U * ε := by
        have h4 : ((2 : ℝ)⁻¹ ^ k) ^ 2 = (4 : ℝ)⁻¹ ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [mul_pow, h4, hc, mul_pow, hsN2, hε, pow_succ]
        ring
      refine key ⌊Real.exp L⌋₊ ?_ ?_
      · intro P hPA hPs
        let φ : (Fin N → ℝ) → (X → ℝ) := fun a =>
          if h : a ∈ A then Classical.choose (hArep a h) else 0
        have hφ : ∀ a ∈ A, φ a ∈ G ∧ a = fun i => s * (φ a (S i) - U / 2) := by
          intro a ha
          simp only [φ, dif_pos ha]
          exact Classical.choose_spec (hArep a ha)
        have hinj : Set.InjOn φ P := by
          intro a ha b hb hab
          rw [(hφ a (hPA a ha)).2, (hφ b (hPA b hb)).2, hab]
        have hcard : (P.image φ).card = P.card := Finset.card_image_of_injOn hinj
        have hpack := SampleMechDesign.pdim_l1_packing hdG S hGB hε0 hεU (P.image φ)
          (by
            intro f hf
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hf
            exact (hφ a (hPA a ha)).1)
          (by
            intro f hf g hg hfg
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hf
            obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hg
            have hab : a ≠ b := fun h => hfg (by rw [h])
            have hsep := hPs a ha b hb hab
            unfold eucNorm at hsep
            rw [Real.lt_sqrt hr0, hr2] at hsep
            have ea : ∀ i, a i = s * (φ a (S i) - U / 2) := fun i => congrFun (hφ a (hPA a ha)).2 i
            have eb : ∀ i, b i = s * (φ b (S i) - U / 2) := fun i => congrFun (hφ b (hPA b hb)).2 i
            have hsq : ∀ i, (a - b) i ^ 2 ≤ U * |φ a (S i) - φ b (S i)| := by
              intro i
              have h1 := hGB _ (hφ a (hPA a ha)).1 i
              have h2 := hGB _ (hφ b (hPA b hb)).1 i
              have hx : |φ a (S i) - φ b (S i)| ≤ U := by
                rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
              have e : (a - b) i = s * (φ a (S i) - φ b (S i)) := by
                rw [Pi.sub_apply, ea i, eb i]; ring
              rw [e, mul_pow, hs2, one_mul, ← sq_abs]
              nlinarith [abs_nonneg (φ a (S i) - φ b (S i))]
            have hsum : ∑ i, (a - b) i ^ 2 ≤ U * ∑ i, |φ a (S i) - φ b (S i)| := by
              rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => hsq i)
            rw [one_div, ← div_eq_inv_mul, lt_div_iff₀ hNr]
            have h3 : U * (ε * N) < U * ∑ i, |φ a (S i) - φ b (S i)| := by
              have := lt_of_lt_of_le hsep hsum
              linarith
            exact lt_of_mul_lt_mul_left h3 hUpos.le)
        rw [hcard] at hpack
        rcases Nat.eq_zero_or_pos P.card with h0 | hpos
        · rw [h0]; exact Nat.zero_le _
        · apply Nat.le_floor
          have hpos' : (0 : ℝ) < P.card := by exact_mod_cast hpos
          rw [← Real.exp_log hpos']
          exact Real.exp_le_exp.2 hpack
      · rcases Nat.eq_zero_or_pos ⌊Real.exp L⌋₊ with h0 | hpos
        · rw [h0]; simpa using hrhs
        · have hpos' : (0 : ℝ) < ⌊Real.exp L⌋₊ := by exact_mod_cast hpos
          calc Real.log ⌊Real.exp L⌋₊ ≤ Real.log (Real.exp L) :=
                Real.log_le_log hpos' (Nat.floor_le (Real.exp_pos L).le)
            _ = L := Real.log_exp L
            _ ≤ _ := hLb
  -- chaining with α = 3√d + η, β = 2√d + η, then η → 0
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hchain : ∀ η : ℝ, 0 < η →
      rademacher A ≤ 6 * c / N * ((3 * Real.sqrt d + η) + 2 * (2 * Real.sqrt d + η)) := by
    intro η hη
    refine chaining_corollary hN A hAne c 0 hcA _ _ (by positivity) (by positivity) ?_
    intro k _
    calc Real.sqrt (Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat))
        ≤ Real.sqrt (d * (3 + 2 * (k : ℝ)) ^ 2) := Real.sqrt_le_sqrt (hcov k)
      _ = Real.sqrt d * (3 + 2 * (k : ℝ)) := by
          rw [Real.sqrt_mul hd0, Real.sqrt_sq (by positivity)]
      _ ≤ (3 * Real.sqrt d + η) + (2 * Real.sqrt d + η) * k := by
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
  have hK : 0 ≤ 18 * c / N := by positivity
  have hfin : rademacher A ≤ 6 * c / N * (7 * Real.sqrt d) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hη : 0 < ε / (18 * c / N + 1) := by positivity
    have h1 := hchain _ hη
    have h2 : 18 * c / N * (ε / (18 * c / N + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have h3 : 6 * c / N * ((3 * Real.sqrt d + ε / (18 * c / N + 1)) +
        2 * (2 * Real.sqrt d + ε / (18 * c / N + 1))) =
        6 * c / N * (7 * Real.sqrt d) + 18 * c / N * (ε / (18 * c / N + 1)) := by ring
    linarith
  calc rademacher A ≤ 6 * c / N * (7 * Real.sqrt d) := hfin
    _ = 21 * U * Real.sqrt d / sN := by
        rw [hc, ← hsN2]
        field_simp
        ring

end SampleMechDesign.T38Aux

open SampleMechDesign.T38Aux FoundationsML.Regression BartlettBousquetMendelson.LocalRad in
theorem solution {X : Type*} [MeasurableSpace X] {F : Set (X → ℝ)}
    (hF : ∀ f ∈ F, Measurable f) (hpm : IsPointwiseMeasurableClass F)
    {k : ℝ} (hk : ∀ (m : ℕ) (z : Fin m → X), Shatters F z → (m : ℝ) ≤ k)
    (D : Measure X) [IsProbabilityMeasure D] {U : ℝ}
    (hU : ∀ᵐ v ∂D, ∀ f ∈ F, f v ∈ Set.Icc 0 U)
    {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Measure.pi (fun _ : Fin N => D)
      {S : Fin N → X | ∃ f ∈ F,
        120 * U * √(k / (N : ℝ)) + 4 * U * √(2 * Real.log (4 / δ) / (N : ℝ)) <
          |(1 / (N : ℝ)) * ∑ i, f (S i) - ∫ v, f v ∂D|} < ENNReal.ofReal δ := by
  classical
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · subst hFe
    simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false, measure_empty]
    exact ENNReal.ofReal_pos.2 hδ0
  set Good : Set X := {v | ∀ f ∈ F, f v ∈ Set.Icc 0 U} with hGood
  have hbad : D Goodᶜ = 0 := ae_iff.1 hU
  obtain ⟨f₀, hf₀⟩ := hFne
  have hU0 : 0 ≤ U := by
    by_contra hneg
    push Not at hneg
    have : Goodᶜ = Set.univ := by
      ext v
      simp only [Set.mem_compl_iff, Set.mem_univ, iff_true]
      intro hv
      have := hv f₀ hf₀
      exact absurd (this.1.trans this.2) (not_le.2 hneg)
    rw [this, measure_univ] at hbad
    exact one_ne_zero hbad
  have hk0 : 0 ≤ k := by
    have := hk 0 Fin.elim0 ⟨Fin.elim0, fun b => ⟨f₀, hf₀, fun i => i.elim0⟩⟩
    simpa using this
  set d : ℕ := ⌊k⌋₊ with hd_def
  have hd : ∀ (m : ℕ) (z : Fin m → X), Shatters F z → m ≤ d :=
    fun m z h => Nat.le_floor (hk m z h)
  have hdk : (d : ℝ) ≤ k := Nat.floor_le hk0
  have hNpos : 0 < N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hδ3 : 0 < δ / 3 := by positivity
  set E : ℝ → Set (Fin N → X) := fun s => {S | ∃ h ∈ F,
    2 * UnderstandingML.rademacher (UnderstandingML.evalSet (UnderstandingML.lossClass (lossS U s) F) S) +
      4 * (U / 2) * Real.sqrt (2 * Real.log (4 / (δ / 3)) / N) <
      UnderstandingML.risk (lossS U s) D h - UnderstandingML.empRisk (lossS U s) S h} with hE
  have one_side : ∀ s : ℝ, |s| = 1 → Measure.pi (fun _ : Fin N => D) (E s) ≤ ENNReal.ofReal (δ / 3) := by
    intro s hs
    exact (UnderstandingML.rademacher_generalization (lossS U s) F ⟨f₀, hf₀⟩ (U / 2)
      (fun h _ z => abs_lossS_le hU0 hs h z) (fun h hh => measurable_lossS U s (hF h hh))
      D N hNpos (meas_glue hF hpm D hU0 hs N).1 (meas_glue hF hpm D hU0 hs N).2.1
      (meas_glue hF hpm D hU0 hs N).2.2 (δ / 3) hδ3 (by linarith)).2.1
  -- the threshold dominates the bound of part 2 for both signs
  have hlog : Real.log (4 / (δ / 3)) ≤ 4 * Real.log (4 / δ) := by
    have e : 4 / (δ / 3) = 3 * (4 / δ) := by field_simp
    have h4 : 1 < 4 / δ := by rw [lt_div_iff₀ hδ0]; linarith
    rw [e, Real.log_mul (by norm_num) (by positivity)]
    have h3 : Real.log 3 ≤ Real.log (4 / δ) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ0]; linarith)
    have : 0 ≤ Real.log (4 / δ) := Real.log_nonneg h4.le
    linarith
  have hsqrt2 : Real.sqrt (2 * Real.log (4 / (δ / 3)) / N) ≤
      2 * Real.sqrt (2 * Real.log (4 / δ) / N) := by
    have e : (2 : ℝ) * Real.sqrt (2 * Real.log (4 / δ) / N) =
        Real.sqrt (4 * (2 * Real.log (4 / δ) / N)) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [e]
    apply Real.sqrt_le_sqrt
    calc 2 * Real.log (4 / (δ / 3)) / N ≤ 4 * (2 * Real.log (4 / δ)) / N :=
          div_le_div_of_nonneg_right (by linarith) hNr.le
      _ = 4 * (2 * Real.log (4 / δ) / N) := by ring
  have hthr : ∀ s : ℝ, |s| = 1 → ∀ S : Fin N → X,
      2 * UnderstandingML.rademacher (UnderstandingML.evalSet (UnderstandingML.lossClass (lossS U s) F) S) +
        4 * (U / 2) * Real.sqrt (2 * Real.log (4 / (δ / 3)) / N) ≤
      120 * U * √(k / (N : ℝ)) + 4 * U * √(2 * Real.log (4 / δ) / (N : ℝ)) := by
    intro s hs S
    have hr := rad_bound ⟨f₀, hf₀⟩ hU0 hs hd hNpos S
    have hsk : Real.sqrt d ≤ Real.sqrt k := Real.sqrt_le_sqrt hdk
    have hkN : √(k / (N : ℝ)) = Real.sqrt k / Real.sqrt N := Real.sqrt_div' k hNr.le
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    have h1 : 2 * (21 * U * Real.sqrt d / Real.sqrt N) ≤ 120 * U * √(k / (N : ℝ)) := by
      rw [hkN, mul_div_assoc', ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hsN.le
      nlinarith [mul_le_mul_of_nonneg_left hsk hU0, Real.sqrt_nonneg (d : ℝ)]
    have h2 : 4 * (U / 2) * Real.sqrt (2 * Real.log (4 / (δ / 3)) / N) ≤
        4 * U * √(2 * Real.log (4 / δ) / (N : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrt2 hU0]
    linarith
  -- empirical and true means of the clamped losses on good samples
  have hint : ∀ f ∈ F, Integrable f D := fun f hf =>
    Integrable.of_bound (hF f hf).aestronglyMeasurable U (hU.mono fun v hv => by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hv f hf).1], (hv f hf).2⟩)
  have hrisk : ∀ s : ℝ, ∀ f ∈ F, UnderstandingML.risk (lossS U s) D f =
      s * (∫ v, f v ∂D) - s * (U / 2) := by
    intro s f hf
    unfold UnderstandingML.risk
    have hae : (fun v => lossS U s f v) =ᵐ[D] fun v => s * f v - s * (U / 2) := by
      filter_upwards [hU] with v hv
      unfold lossS
      rw [clampU_of_mem (hv f hf)]
      ring
    rw [integral_congr_ae hae, integral_sub ((hint f hf).const_mul s) (integrable_const _),
      integral_const_mul]
    simp
  have hemp : ∀ s : ℝ, ∀ S : Fin N → X, (∀ i, S i ∈ Good) → ∀ f ∈ F,
      UnderstandingML.empRisk (lossS U s) S f = s * ((1 / (N : ℝ)) * ∑ i, f (S i)) - s * (U / 2) := by
    intro s S hS f hf
    have e1 : ∀ i, lossS U s f (S i) = s * f (S i) - s * (U / 2) := by
      intro i
      unfold lossS
      rw [clampU_of_mem (hS i f hf)]
      ring
    unfold UnderstandingML.empRisk
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  set Bad : Set (Fin N → X) := ⋃ i, Function.eval i ⁻¹' Goodᶜ with hBad
  have hBad0 : Measure.pi (fun _ : Fin N => D) Bad = 0 :=
    measure_iUnion_null (fun i => Measure.pi_eval_preimage_null (μ := fun _ : Fin N => D) hbad)
  have hsub : {S : Fin N → X | ∃ f ∈ F,
        120 * U * √(k / (N : ℝ)) + 4 * U * √(2 * Real.log (4 / δ) / (N : ℝ)) <
          |(1 / (N : ℝ)) * ∑ i, f (S i) - ∫ v, f v ∂D|} ⊆ (E 1 ∪ E (-1)) ∪ Bad := by
    intro S ⟨f, hf, hlt⟩
    by_cases hS : ∀ i, S i ∈ Good
    · left
      rcases lt_abs.1 hlt with h | h
      · right
        refine ⟨f, hf, lt_of_le_of_lt (hthr (-1) (by simp) S) ?_⟩
        rw [hrisk (-1) f hf, hemp (-1) S hS f hf]
        linarith
      · left
        refine ⟨f, hf, lt_of_le_of_lt (hthr 1 (by simp) S) ?_⟩
        rw [hrisk 1 f hf, hemp 1 S hS f hf]
        linarith
    · right
      push Not at hS
      obtain ⟨i, hi⟩ := hS
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  calc Measure.pi (fun _ : Fin N => D) _ ≤ Measure.pi (fun _ : Fin N => D) ((E 1 ∪ E (-1)) ∪ Bad) :=
        measure_mono hsub
    _ ≤ Measure.pi (fun _ : Fin N => D) (E 1) + Measure.pi (fun _ : Fin N => D) (E (-1)) +
        Measure.pi (fun _ : Fin N => D) Bad :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + 0 := by
        rw [hBad0]
        exact add_le_add (add_le_add (one_side 1 (by simp)) (one_side (-1) (by simp))) le_rfl
    _ < ENNReal.ofReal δ := by
        rw [add_zero, ← ENNReal.ofReal_add hδ3.le hδ3.le]
        exact (ENNReal.ofReal_lt_ofReal_iff hδ0).2 (by linarith)
