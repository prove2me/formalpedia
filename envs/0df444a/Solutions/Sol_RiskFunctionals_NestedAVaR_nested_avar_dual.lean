-- Prove2me | solution 1 for RiskFunctionals.NestedAVaR.nested_avar_dual
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:39:45.458585+00:00
-- url     : https://prove2.me/submissions/a61e0ef1-d641-4c15-8d6b-61291a4f58dc

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_AverageValueAtRisk
import Theorems.Thm_RiskFunctionals_NestedAVaR_condAVaR_pairing

open RiskFunctionals.NestedAVaR MeasureTheory

theorem nav_rn {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Set Ω → ℝ) (h0 : ν ∅ = 0)
    (hσ : ∀ f : ℕ → Set Ω, (∀ i, MeasurableSet (f i)) → Pairwise (Function.onFun Disjoint f) →
      HasSum (fun i => ν (f i)) (ν (⋃ i, f i)))
    (hac : ∀ B, MeasurableSet B → μ B = 0 → ν B = 0) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧ ∀ B, MeasurableSet B → ∫ x in B, g x ∂μ = ν B := by
  classical
  let s : SignedMeasure Ω :=
    { measureOf' := fun B => if MeasurableSet B then ν B else 0
      empty' := by simp [h0]
      not_measurable' := fun B hB => by simp [hB]
      m_iUnion' := fun f hf hd => by
        simp only [hf, if_true, MeasurableSet.iUnion hf]
        exact hσ f hf hd }
  have hs : ∀ B, MeasurableSet B → s B = ν B := fun B hB => by
    show (if MeasurableSet B then ν B else 0) = ν B
    simp [hB]
  have hac' : s ≪ᵥ μ.toENNRealVectorMeasure := by
    intro B hB
    by_cases hBm : MeasurableSet B
    · rw [Measure.toENNRealVectorMeasure_apply_measurable hBm] at hB
      rw [hs B hBm]; exact hac B hBm hB
    · exact s.not_measurable hBm
  refine ⟨s.rnDeriv μ, SignedMeasure.measurable_rnDeriv _ _, SignedMeasure.integrable_rnDeriv _ _,
    fun B hB => ?_⟩
  have := SignedMeasure.withDensityᵥ_rnDeriv_eq s μ hac'
  rw [← hs B hB]
  conv_rhs => rw [← this]
  rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hB]

def navFeas {Ω : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (α : ℝ) (B : Set Ω) (Z : Ω → ℝ) : Prop :=
  Measurable Z ∧ (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ B.indicator (fun _ => 1 / α) ω) ∧
    P[Z|m] =ᵐ[P] B.indicator (fun _ => (1 : ℝ))

noncomputable def navNu {Ω : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) (α : ℝ) (X : Ω → ℝ) (B : Set Ω) : ℝ :=
  sInf {r | ∃ Z, navFeas m P α B Z ∧ ∫ ω, X ω * Z ω ∂P = r}

section
variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]
  {α : ℝ} {X : Ω → ℝ}

theorem navFeas_int (hα₀ : 0 < α) (hX : Integrable X P) {B : Set Ω} {Z : Ω → ℝ}
    (h : navFeas m P α B Z) : Integrable Z P ∧ Integrable (fun ω => X ω * Z ω) P := by
  have hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1 / α := h.2.1.mono fun ω hω => by
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    refine hω.2.trans ?_
    by_cases hB : ω ∈ B
    · simp [Set.indicator_of_mem hB]
    · simp only [Set.indicator_of_notMem hB]; positivity
  exact ⟨(integrable_const (1 / α)).mono' h.1.aestronglyMeasurable hb,
    hX.mul_bdd h.1.aestronglyMeasurable hb⟩

theorem navFeas_lower (hm : m ≤ mΩ) (hα₀ : 0 < α) (hX : Integrable X P) {B : Set Ω}
    (hB : MeasurableSet[m] B) {Z : Ω → ℝ} (h : navFeas m P α B Z) :
    -(1 / α * ∫ ω in B, |X ω| ∂P) ≤ ∫ ω, X ω * Z ω ∂P := by
  have hi := navFeas_int hα₀ hX h
  rw [← integral_const_mul, ← integral_indicator (hm B hB), ← integral_neg]
  refine integral_mono_ae ((hX.abs.const_mul (1 / α)).indicator (hm B hB)).neg hi.2 ?_
  filter_upwards [h.2.1] with ω hω
  have hα' : 0 < 1 / α := by positivity
  by_cases hb : ω ∈ B
  · simp only [Set.indicator_of_mem hb] at hω ⊢
    have h1 := neg_abs_le (X ω)
    have h2 := le_abs_self (X ω)
    nlinarith [abs_nonneg (X ω), hω.1, hω.2]
  · simp only [Set.indicator_of_notMem hb] at hω ⊢
    have : Z ω = 0 := le_antisymm hω.2 hω.1
    simp [this]

theorem navFeas_one (hm : m ≤ mΩ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) {B : Set Ω}
    (hB : MeasurableSet[m] B) : navFeas m P α B (B.indicator (fun _ => 1)) := by
  refine ⟨measurable_const.indicator (hm B hB), Filter.Eventually.of_forall fun ω => ?_, ?_⟩
  · by_cases hb : ω ∈ B
    · simp only [Set.indicator_of_mem hb]; exact ⟨zero_le_one, one_le_one_div hα₀ hα₁⟩
    · simp [Set.indicator_of_notMem hb]
  · exact (condExp_of_stronglyMeasurable hm (stronglyMeasurable_const.indicator hB)
      ((integrable_const 1).indicator (hm B hB))).eventuallyEq

theorem navNu_bdd (hm : m ≤ mΩ) (hα₀ : 0 < α) (hX : Integrable X P) {B : Set Ω}
    (hB : MeasurableSet[m] B) :
    BddBelow {r | ∃ Z, navFeas m P α B Z ∧ ∫ ω, X ω * Z ω ∂P = r} :=
  ⟨_, fun r ⟨Z, hZ, hr⟩ => hr ▸ navFeas_lower hm hα₀ hX hB hZ⟩

theorem navNu_le (hm : m ≤ mΩ) (hα₀ : 0 < α) (hX : Integrable X P) {B : Set Ω}
    (hB : MeasurableSet[m] B) {Z : Ω → ℝ} (h : navFeas m P α B Z) :
    navNu m P α X B ≤ ∫ ω, X ω * Z ω ∂P :=
  csInf_le (navNu_bdd hm hα₀ hX hB) ⟨Z, h, rfl⟩

theorem navNu_ge (hm : m ≤ mΩ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) {B : Set Ω}
    (hB : MeasurableSet[m] B) {c : ℝ}
    (h : ∀ Z, navFeas m P α B Z → c ≤ ∫ ω, X ω * Z ω ∂P) : c ≤ navNu m P α X B :=
  le_csInf ⟨_, _, navFeas_one hm hα₀ hα₁ hB, rfl⟩ fun r ⟨Z, hZ, hr⟩ => hr ▸ h Z hZ

theorem navNu_approx (hm : m ≤ mΩ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) {B : Set Ω}
    (hB : MeasurableSet[m] B) {ε : ℝ} (hε : 0 < ε) :
    ∃ Z, navFeas m P α B Z ∧ ∫ ω, X ω * Z ω ∂P < navNu m P α X B + ε := by
  obtain ⟨r, ⟨Z, hZ, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
    (⟨_, _, navFeas_one hm hα₀ hα₁ hB, rfl⟩ : Set.Nonempty
      {r | ∃ Z, navFeas m P α B Z ∧ ∫ ω, X ω * Z ω ∂P = r})
    (lt_add_of_pos_right (navNu m P α X B) hε)
  exact ⟨Z, hZ, hr⟩

theorem navNu_abs (hm : m ≤ mΩ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hX : Integrable X P) {B : Set Ω}
    (hB : MeasurableSet[m] B) : |navNu m P α X B| ≤ 1 / α * ∫ ω in B, |X ω| ∂P := by
  rw [abs_le]
  constructor
  · exact navNu_ge hm hα₀ hα₁ hB fun Z hZ => navFeas_lower hm hα₀ hX hB hZ
  · have h1 := navNu_le hm hα₀ hX hB (navFeas_one (P := P) hm hα₀ hα₁ hB)
    have h2 : ∫ ω, X ω * B.indicator (fun _ => (1 : ℝ)) ω ∂P = ∫ ω in B, X ω ∂P := by
      rw [← integral_indicator (hm B hB)]
      congr 1; funext ω
      by_cases hb : ω ∈ B
      · simp [Set.indicator_of_mem hb]
      · simp [Set.indicator_of_notMem hb]
    have h3 : ∫ ω in B, X ω ∂P ≤ ∫ ω in B, |X ω| ∂P :=
      integral_mono hX.integrableOn hX.abs.integrableOn fun ω => le_abs_self _
    have h4 : 0 ≤ ∫ ω in B, |X ω| ∂P := integral_nonneg fun ω => abs_nonneg _
    have h5 : 1 ≤ 1 / α := one_le_one_div hα₀ hα₁
    nlinarith

theorem navNu_add (hm : m ≤ mΩ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hX : Integrable X P)
    {B₁ B₂ : Set Ω} (h₁ : MeasurableSet[m] B₁) (h₂ : MeasurableSet[m] B₂) (hd : Disjoint B₁ B₂) :
    navNu m P α X (B₁ ∪ B₂) = navNu m P α X B₁ + navNu m P α X B₂ := by
  have h12 : MeasurableSet[m] (B₁ ∪ B₂) := h₁.union h₂
  apply le_antisymm
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨Z₁, hZ₁, hl₁⟩ := navNu_approx (X := X) (P := P) hm hα₀ hα₁ h₁ (half_pos hε)
    obtain ⟨Z₂, hZ₂, hl₂⟩ := navNu_approx (X := X) (P := P) hm hα₀ hα₁ h₂ (half_pos hε)
    have i₁ := navFeas_int hα₀ hX hZ₁
    have i₂ := navFeas_int hα₀ hX hZ₂
    have hf : navFeas m P α (B₁ ∪ B₂) (Z₁ + Z₂) := by
      refine ⟨hZ₁.1.add hZ₂.1, ?_, ?_⟩
      · filter_upwards [hZ₁.2.1, hZ₂.2.1] with ω a b
        rw [Set.indicator_union_of_disjoint hd]
        simp only [Pi.add_apply]
        exact ⟨add_nonneg a.1 b.1, add_le_add a.2 b.2⟩
      · filter_upwards [condExp_add i₁.1 i₂.1 m, hZ₁.2.2, hZ₂.2.2] with ω a b c
        rw [a, Set.indicator_union_of_disjoint hd]
        simp only [Pi.add_apply, b, c]
    have := navNu_le hm hα₀ hX h12 hf
    have e : ∫ ω, X ω * (Z₁ + Z₂) ω ∂P = ∫ ω, X ω * Z₁ ω ∂P + ∫ ω, X ω * Z₂ ω ∂P := by
      rw [← integral_add i₁.2 i₂.2]; congr 1; funext ω; simp only [Pi.add_apply]; ring
    linarith
  · refine navNu_ge hm hα₀ hα₁ h12 fun Z hZ => ?_
    have iZ := navFeas_int hα₀ hX hZ
    have hf : ∀ B, MeasurableSet[m] B → B ⊆ B₁ ∪ B₂ → navFeas m P α B (B.indicator Z) := by
      intro B hB hsub
      refine ⟨hZ.1.indicator (hm B hB), ?_, ?_⟩
      · filter_upwards [hZ.2.1] with ω a
        by_cases hb : ω ∈ B
        · simp only [Set.indicator_of_mem hb]
          simpa [Set.indicator_of_mem (hsub hb)] using a
        · simp [Set.indicator_of_notMem hb]
      · filter_upwards [condExp_indicator iZ.1 hB, hZ.2.2] with ω a b
        rw [a]
        by_cases hb : ω ∈ B
        · simp only [Set.indicator_of_mem hb, b, Set.indicator_of_mem (hsub hb)]
        · simp only [Set.indicator_of_notMem hb]
    have f₁ := hf B₁ h₁ Set.subset_union_left
    have f₂ := hf B₂ h₂ Set.subset_union_right
    have l₁ := navNu_le hm hα₀ hX h₁ f₁
    have l₂ := navNu_le hm hα₀ hX h₂ f₂
    have e : ∫ ω, X ω * Z ω ∂P =
        ∫ ω, X ω * B₁.indicator Z ω ∂P + ∫ ω, X ω * B₂.indicator Z ω ∂P := by
      rw [← integral_add (navFeas_int hα₀ hX f₁).2 (navFeas_int hα₀ hX f₂).2]
      refine integral_congr_ae ?_
      filter_upwards [hZ.2.1] with ω a
      by_cases hb1 : ω ∈ B₁
      · have hb2 : ω ∉ B₂ := fun h => Set.disjoint_left.1 hd hb1 h
        simp [Set.indicator_of_mem hb1, Set.indicator_of_notMem hb2]
      · by_cases hb2 : ω ∈ B₂
        · simp [Set.indicator_of_mem hb2, Set.indicator_of_notMem hb1]
        · have hn : ω ∉ B₁ ∪ B₂ := by simp [hb1, hb2]
          simp only [Set.indicator_of_notMem hn] at a
          have : Z ω = 0 := le_antisymm a.2 a.1
          simp [this, Set.indicator_of_notMem hb1, Set.indicator_of_notMem hb2]
    linarith

theorem navNu_zero (hm : m ≤ mΩ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hX : Integrable X P) {B : Set Ω}
    (hB : MeasurableSet[m] B) (h0 : P B = 0) : navNu m P α X B = 0 := by
  have := navNu_abs hm hα₀ hα₁ hX hB
  rw [setIntegral_measure_zero _ h0, mul_zero] at this
  exact abs_nonpos_iff.1 this

theorem navNu_sigma (hm : m ≤ mΩ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hX : Integrable X P)
    (f : ℕ → Set Ω) (hf : ∀ i, MeasurableSet[m] (f i)) (hd : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun i => navNu m P α X (f i)) (navNu m P α X (⋃ i, f i)) := by
  set c := 1 / α
  have hA : ∀ n, MeasurableSet[m] (Set.accumulate f n) := fun n => by
    rw [Set.accumulate_def]; exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ => hf y
  have hU : MeasurableSet[m] (⋃ i, f i) := MeasurableSet.iUnion hf
  have hfin : ∀ n, navNu m P α X (Set.accumulate f n) =
      ∑ i ∈ Finset.range (n + 1), navNu m P α X (f i) := by
    intro n
    induction n with
    | zero => simp [Set.accumulate_zero_nat]
    | succ n ih =>
      rw [Set.accumulate_succ, navNu_add hm hα₀ hα₁ hX (hA n) (hf _) ?_, ih,
        Finset.sum_range_succ _ (n + 1)]
      rw [Set.disjoint_left]
      intro x hx hx'
      obtain ⟨y, hy, hxy⟩ := Set.mem_accumulate.1 hx
      exact Set.disjoint_left.1 (hd (show y ≠ n + 1 by omega)) hxy hx'
  have hs : HasSum (fun i => ∫ ω in f i, |X ω| ∂P) (∫ ω in ⋃ i, f i, |X ω| ∂P) :=
    hasSum_integral_iUnion (fun i => hm _ (hf i)) hd hX.abs.integrableOn
  have hsum : Summable (fun i => navNu m P α X (f i)) :=
    Summable.of_norm_bounded (hs.summable.mul_left c) fun i => by
      rw [Real.norm_eq_abs]; exact navNu_abs hm hα₀ hα₁ hX (hf i)
  rw [hsum.hasSum_iff_tendsto_nat, ← Filter.tendsto_add_atTop_iff_nat 1]
  simp_rw [← hfin]
  have hT := tendsto_setIntegral_of_monotone (μ := P) (f := fun ω => |X ω|)
    (fun n => hm _ (hA n)) Set.monotone_accumulate (by rw [Set.iUnion_accumulate]; exact hX.abs.integrableOn)
  rw [Set.iUnion_accumulate] at hT
  have hT' := (hT.const_sub (∫ ω in ⋃ i, f i, |X ω| ∂P)).const_mul c
  rw [sub_self, mul_zero] at hT'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hT'
  have hsub : Set.accumulate f n ⊆ ⋃ i, f i := by
    rw [← Set.iUnion_accumulate]; exact Set.subset_iUnion _ _
  have he : ⋃ i, f i = Set.accumulate f n ∪ ((⋃ i, f i) \ Set.accumulate f n) :=
    (Set.union_sdiff_cancel hsub).symm
  have hadd := navNu_add hm hα₀ hα₁ hX (hA n) (hU.diff (hA n)) Set.disjoint_sdiff_right
  rw [← he] at hadd
  have hb := navNu_abs hm hα₀ hα₁ hX (hU.diff (hA n))
  rw [setIntegral_sdiff (hm _ (hA n)) hX.abs.integrableOn hsub] at hb
  simp only [Real.norm_eq_abs]
  rw [hadd, abs_sub_comm]
  convert hb using 2
  ring

theorem nav_exists (hm : m ≤ mΩ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hX : Integrable X P) :
    ∃ V, IsConditionalAVaR m P α X V := by
  obtain ⟨g, hgm, hgi, hg⟩ := @nav_rn Ω m (P.trim hm) _ (navNu m P α X)
    (by simpa using navNu_zero (X := X) hm hα₀ hα₁ hX (@MeasurableSet.empty Ω m) (by simp))
    (fun f hf hd => navNu_sigma hm hα₀ hα₁ hX f hf hd)
    (fun B hB h0 => navNu_zero hm hα₀ hα₁ hX hB (by rwa [trim_measurableSet_eq hm hB] at h0))
  refine ⟨g, hgm, integrable_of_integrable_trim hm hgi, fun B hB => ?_⟩
  rw [setIntegral_trim hm hgm.stronglyMeasurable hB, hg B hB]
  show _ = ⨅ (Z : Ω → ℝ) (_ : navFeas m P α B Z), ((∫ ω, X ω * Z ω ∂P : ℝ) : EReal)
  apply le_antisymm
  · refine le_iInf₂ fun Z hZ => ?_
    exact_mod_cast navNu_le hm hα₀ hX hB hZ
  · by_contra hcon
    push Not at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hr2' : navNu m P α X B < r := by exact_mod_cast hr1
    obtain ⟨Z, hZ, hlt⟩ := navNu_approx (X := X) (P := P) hm hα₀ hα₁ hB (sub_pos.2 hr2')
    have h1 := iInf₂_le (f := fun (Z : Ω → ℝ) (_ : navFeas m P α B Z) =>
      ((∫ ω, X ω * Z ω ∂P : ℝ) : EReal)) Z hZ
    have h2 : ((∫ ω, X ω * Z ω ∂P : ℝ) : EReal) < r := by exact_mod_cast (by linarith : ∫ ω, X ω * Z ω ∂P < r)
    exact absurd (lt_of_le_of_lt h1 h2) (not_lt.2 hr2.le)

end

theorem nav_step {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P] (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (U₁ U₀ : Ω → ℝ) (hU₁ : Integrable U₁ P) (hU₁m : Measurable[m₂] U₁)
    (hV : IsConditionalAVaR m₁ P α U₁ U₀) (W : Ω → ℝ) (hWm : Measurable[m₁] W) (C : ℝ)
    (hWb : ∀ᵐ ω ∂P, |W ω| ≤ C) (hWn : ∀ᵐ ω ∂P, 0 ≤ W ω) (ε : ℝ) (hε : 0 < ε) :
    ∃ Z₂ : Ω → ℝ, Measurable[m₂] Z₂ ∧ (∀ᵐ ω ∂P, 0 ≤ Z₂ ω ∧ Z₂ ω ≤ (1 / α) * W ω) ∧
      P[Z₂|m₁] =ᵐ[P] W ∧ ∫ ω, U₁ ω * Z₂ ω ∂P < ∫ ω, U₀ ω * W ω ∂P + ε := by
  have h₁ : m₁ ≤ mΩ := h₁₂.trans h₂
  have hp := condAVaR_pairing h₁ P α hα₀ hα₁ U₁ U₀ hU₁ hV W hWm ⟨C, hWb⟩ hWn
  have hlt : ((∫ ω, U₀ ω * W ω ∂P : ℝ) : EReal) < ((∫ ω, U₀ ω * W ω ∂P + ε : ℝ) : EReal) := by
    exact_mod_cast (by linarith)
  rw [hp] at hlt
  obtain ⟨Z', h1⟩ := iInf_lt_iff.1 hlt
  obtain ⟨⟨hZ'm, hZ'b, hZ'c⟩, hZ'lt⟩ := iInf_lt_iff.1 h1
  have hZ'lt' : ∫ ω, U₁ ω * Z' ω ∂P < ∫ ω, U₀ ω * W ω ∂P + ε := by exact_mod_cast hZ'lt
  have hWm' : Measurable W := hWm.mono h₁ le_rfl
  have hWi : Integrable W P := (integrable_const C).mono' hWm'.aestronglyMeasurable
    (hWb.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hZ'bd : ∀ᵐ ω ∂P, ‖Z' ω‖ ≤ (1 / α) * C := by
    filter_upwards [hZ'b, hWb] with ω a b
    rw [Real.norm_eq_abs, abs_of_nonneg a.1]
    exact a.2.trans (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans b) (by positivity))
  have hZ'i : Integrable Z' P := (integrable_const _).mono' hZ'm.aestronglyMeasurable hZ'bd
  refine ⟨P[Z'|m₂], stronglyMeasurable_condExp.measurable, ?_, ?_, ?_⟩
  · have hc : P[fun ω => (1 / α) * W ω|m₂] = fun ω => (1 / α) * W ω :=
      condExp_of_stronglyMeasurable h₂ ((hWm.mono h₁₂ le_rfl).const_mul _).stronglyMeasurable
        (hWi.const_mul _)
    have hmono := condExp_mono (m := m₂) hZ'i (hWi.const_mul (1 / α))
      (hZ'b.mono fun ω h => h.2)
    have hnn := condExp_nonneg (m := m₂) (μ := P) (f := Z') (hZ'b.mono fun ω h => h.1)
    rw [hc] at hmono
    filter_upwards [hmono, hnn] with ω a b
    exact ⟨b, a⟩
  · exact (condExp_condExp_of_le h₁₂ h₂).trans hZ'c
  · have hUZ : Integrable (U₁ * Z') P := hU₁.mul_bdd hZ'm.aestronglyMeasurable hZ'bd
    have e1 : ∫ ω, U₁ ω * Z' ω ∂P = ∫ ω, U₁ ω * P[Z'|m₂] ω ∂P := by
      calc ∫ ω, U₁ ω * Z' ω ∂P = ∫ ω, (P[U₁ * Z'|m₂]) ω ∂P := (integral_condExp h₂).symm
        _ = ∫ ω, (U₁ * P[Z'|m₂]) ω ∂P :=
            integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hU₁m.stronglyMeasurable hUZ hZ'i)
        _ = _ := rfl
    rw [← e1]; exact hZ'lt'

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (Y : ℕ → Ω → ℝ)
    (hY : ∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P 1 (Y t)) :
    (∃ v : ℝ, IsNestedAVaR ℱ P α T Y v) ∧
      ∀ v : ℝ, IsNestedAVaR ℱ P α T Y v →
        (v : EReal) = ⨅ Z ∈ NestedDualSet ℱ P α T,
          ((∫ ω, (∑ t ∈ Finset.Icc 1 T, Y t ω) * Z T ω ∂P : ℝ) : EReal) := by
  classical
  set X : Ω → ℝ := fun ω => ∑ t ∈ Finset.Icc 1 T, Y t ω with hXdef
  have hXi : Integrable X P :=
    integrable_finsetSum _ fun t ht => memLp_one_iff_integrable.1 (hY t ht).2
  have hXm : Measurable[ℱ T] X := by
    rw [hℱ.2]
    exact Finset.measurable_sum _ fun t ht => ((hY t ht).1).mono (ℱ.le t) le_rfl
  refine ⟨?_, ?_⟩
  · let A : ℕ → (Ω → ℝ) → Ω → ℝ := fun s X =>
      if h : ∃ V, IsConditionalAVaR (ℱ s) P α X V then h.choose else 0
    refine ⟨_, A, fun s _ X hX => ?_, rfl⟩
    have h : ∃ V, IsConditionalAVaR (ℱ s) P α X V := nav_exists (ℱ.le s) hα₀ hα₁ hX
    show IsConditionalAVaR (ℱ s) P α X (if h : ∃ V, IsConditionalAVaR (ℱ s) P α X V then h.choose else 0)
    rw [dif_pos h]; exact h.choose_spec
  intro v ⟨A, hA, hv⟩
  let H : ℕ → Ω → ℝ := fun k => Nat.rec X (fun k h => A (T - 1 - k) h) k
  have H0 : H 0 = X := rfl
  have Hs : ∀ k, H (k + 1) = A (T - 1 - k) (H k) := fun k => rfl
  have Hcomp : ∀ k ≤ T, composition A T X = composition A (T - k) (H k) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [ih (by omega), Hs, show T - k = (T - (k + 1)) + 1 by omega, composition,
        show T - (k + 1) = T - 1 - k by omega]
  have Hint : ∀ k ≤ T, Integrable (H k) P := by
    intro k hk
    induction k with
    | zero => exact hXi
    | succ k ih => rw [Hs]; exact (hA _ (by omega) _ (ih (by omega))).2.1
  set U : ℕ → Ω → ℝ := fun t => H (T - t) with hUdef
  have hUT : U T = X := by simp [hUdef, H0]
  have hUc : ∀ t < T, IsConditionalAVaR (ℱ t) P α (U (t + 1)) (U t) := by
    intro t ht
    have e : U t = A t (U (t + 1)) := by
      simp only [hUdef]
      rw [show T - t = (T - (t + 1)) + 1 by omega, Hs, show T - 1 - (T - (t + 1)) = t by omega]
    rw [e]; exact hA t ht _ (Hint _ (by omega))
  have hUi : ∀ t ≤ T, Integrable (U t) P := fun t _ => Hint _ (by omega)
  have hUm : ∀ t ≤ T, Measurable[ℱ t] (U t) := by
    intro t ht
    rcases Nat.lt_or_ge t T with h | h
    · exact (hUc t h).1
    · rw [show t = T by omega, hUT]; exact hXm
  have hv' : v = ∫ ω, U 0 ω ∂P := by
    rw [hv, compositionValue, Hcomp T le_rfl]; simp [hUdef, composition]
  apply le_antisymm
  · -- v ≤ inf
    refine le_iInf₂ fun Z hZ => ?_
    obtain ⟨hZ0, hZc⟩ := hZ
    have hb : ∀ t ≤ T, Measurable[ℱ t] (Z t) ∧
        ∀ᵐ ω ∂P, 0 ≤ Z t ω ∧ Z t ω ≤ (1 / α) ^ t := by
      intro t ht
      induction t with
      | zero => rw [hZ0]; exact ⟨measurable_const, Filter.Eventually.of_forall fun ω => by simp⟩
      | succ t ih =>
        obtain ⟨h1, h2, _⟩ := hZc (t + 1) (Finset.mem_Icc.2 ⟨by omega, ht⟩)
        refine ⟨h1, ?_⟩
        filter_upwards [h2, (ih (by omega)).2] with ω a b
        simp only [Nat.add_sub_cancel] at a
        refine ⟨a.1, a.2.trans ?_⟩
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_left b.2 (by positivity)
    have key : ∀ k, ∀ t, t + k = T → ∫ ω, U t ω * Z t ω ∂P ≤ ∫ ω, X ω * Z T ω ∂P := by
      intro k
      induction k with
      | zero => intro t ht; rw [show t = T by omega, hUT]
      | succ k ih =>
        intro t ht
        refine le_trans ?_ (ih (t + 1) (by omega))
        have hbt := hb t (by omega)
        have hp := condAVaR_pairing (ℱ.le t) P α hα₀ hα₁ (U (t + 1)) (U t) (hUi _ (by omega))
          (hUc t (by omega)) (Z t) hbt.1 ⟨(1 / α) ^ t, hbt.2.mono fun ω h => by
            rw [abs_of_nonneg h.1]; exact h.2⟩ (hbt.2.mono fun ω h => h.1)
        obtain ⟨h1, h2, h3⟩ := hZc (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
        simp only [Nat.add_sub_cancel] at h2 h3
        have := iInf₂_le (f := fun (Z₂ : Ω → ℝ) (_ : Measurable Z₂ ∧
          (∀ᵐ ω ∂P, 0 ≤ Z₂ ω ∧ Z₂ ω ≤ (1 / α) * Z t ω) ∧ P[Z₂|ℱ t] =ᵐ[P] Z t) =>
            ((∫ ω, U (t + 1) ω * Z₂ ω ∂P : ℝ) : EReal)) (Z (t + 1))
            ⟨h1.mono (ℱ.le _) le_rfl, h2, h3⟩
        rw [← hp] at this
        exact_mod_cast this
    have := key T 0 (by omega)
    rw [hZ0] at this
    simp only [mul_one] at this
    rw [hv']
    exact_mod_cast this
  · -- inf ≤ v
    have key : ∀ k, ∀ t, t + k = T → ∀ W : Ω → ℝ, Measurable[ℱ t] W →
        ∀ C : ℝ, (∀ᵐ ω ∂P, |W ω| ≤ C) → (∀ᵐ ω ∂P, 0 ≤ W ω) → ∀ ε : ℝ, 0 < ε →
        ∃ Z : ℕ → Ω → ℝ, Z t = W ∧
          (∀ j, t < j → j ≤ T → Measurable[ℱ j] (Z j) ∧
            (∀ᵐ ω ∂P, 0 ≤ Z j ω ∧ Z j ω ≤ (1 / α) * Z (j - 1) ω) ∧
            P[Z j|ℱ (j - 1)] =ᵐ[P] Z (j - 1)) ∧
          ∫ ω, X ω * Z T ω ∂P < ∫ ω, U t ω * W ω ∂P + ε := by
      intro k
      induction k with
      | zero =>
        intro t ht W _ C _ _ ε hε
        obtain rfl : t = T := by omega
        refine ⟨fun _ => W, rfl, fun j h1 h2 => absurd h2 (by omega), ?_⟩
        rw [hUT]; linarith
      | succ k ih =>
        intro t ht W hWm C hWb hWn ε hε
        obtain ⟨Z₂, h1, h2, h3, h4⟩ := nav_step (ℱ.mono (Nat.le_succ t)) (ℱ.le (t + 1)) P α hα₀ hα₁
          (U (t + 1)) (U t) (hUi _ (by omega)) (hUm _ (by omega)) (hUc t (by omega)) W hWm C hWb hWn
          (ε / 2) (half_pos hε)
        have hb2 : ∀ᵐ ω ∂P, |Z₂ ω| ≤ (1 / α) * C := by
          filter_upwards [h2, hWb] with ω a b
          rw [abs_of_nonneg a.1]
          exact a.2.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans b) (by positivity))
        obtain ⟨Z'', e1, e2, e3⟩ := ih (t + 1) (by omega) Z₂ h1 _ hb2 (h2.mono fun ω h => h.1)
          (ε / 2) (half_pos hε)
        refine ⟨Function.update Z'' t W, by simp, fun j hj1 hj2 => ?_, ?_⟩
        · rw [Function.update_of_ne (show j ≠ t by omega)]
          rcases Nat.lt_or_ge (t + 1) j with hj | hj
          · rw [Function.update_of_ne (show j - 1 ≠ t by omega)]
            exact e2 j hj hj2
          · obtain rfl : j = t + 1 := by omega
            simp only [Nat.add_sub_cancel, Function.update_self]
            rw [e1]; exact ⟨h1, h2, h3⟩
        · rw [Function.update_of_ne (show T ≠ t by omega)]
          linarith
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hr1' : v < r := by exact_mod_cast hr1
    obtain ⟨Z, hZ0, hZc, hZv⟩ := key T 0 (by omega) (fun _ => 1) measurable_const 1
      (Filter.Eventually.of_forall fun ω => by simp) (Filter.Eventually.of_forall fun ω => by simp)
      (r - v) (by linarith)
    have hmem : Z ∈ NestedDualSet ℱ P α T :=
      ⟨hZ0, fun j hj => hZc j (by have := (Finset.mem_Icc.1 hj).1; omega) (Finset.mem_Icc.1 hj).2⟩
    have h1 := iInf₂_le (f := fun (Z : ℕ → Ω → ℝ) (_ : Z ∈ NestedDualSet ℱ P α T) =>
      ((∫ ω, (∑ t ∈ Finset.Icc 1 T, Y t ω) * Z T ω ∂P : ℝ) : EReal)) Z hmem
    simp only [mul_one, ← hv'] at hZv
    have h2 : ((∫ ω, (∑ t ∈ Finset.Icc 1 T, Y t ω) * Z T ω ∂P : ℝ) : EReal) < r := by
      exact_mod_cast (by linarith : ∫ ω, X ω * Z T ω ∂P < r)
    exact absurd (lt_of_le_of_lt h1 h2) (not_lt.2 hr2.le)
