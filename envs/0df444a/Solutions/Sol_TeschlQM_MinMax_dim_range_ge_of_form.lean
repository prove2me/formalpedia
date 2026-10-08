-- Prove2me | solution 1 for TeschlQM.MinMax.dim_range_ge_of_form
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T12:14:13.581994+00:00
-- url     : https://prove2.me/submissions/834243b1-d9c1-4a0d-b181-ba9948150a5c

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_MinMax_formDomain

open MeasureTheory
open scoped ENNReal InnerProductSpace

universe u

namespace TeschlQM.PVMCore

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma tendsto_nsmul_eq_zero {v w : H}
    (h : Filter.Tendsto (fun N : ℕ => N • v) Filter.atTop (nhds w)) : v = 0 := by
  have h1 : Filter.Tendsto (fun N : ℕ => (N + 1) • v) Filter.atTop (nhds w) :=
    h.comp (Filter.tendsto_add_atTop_nat 1)
  have h2 := h1.sub h
  simp only [add_smul, one_smul, add_sub_cancel_left] at h2
  have h3 : v = w - w := tendsto_nhds_unique tendsto_const_nhds h2
  simpa using h3

lemma pvm_empty (hP : TeschlQM.Shared.IsProjValuedMeasure P) : P ∅ = 0 := by
  ext ψ
  have := hP.2.2 (fun _ => ∅) (fun _ => MeasurableSet.empty)
    (fun i j _ => Set.disjoint_empty _) ψ
  simp only [Finset.sum_const, Finset.card_range, Set.iUnion_empty] at this
  simpa using tendsto_nsmul_eq_zero this

lemma pvm_union (hP : TeschlQM.Shared.IsProjValuedMeasure P) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    P (A ∪ B) = P A + P B := by
  ext ψ
  let Ω : ℕ → Set ℝ := fun n => if n = 0 then A else if n = 1 then B else ∅
  have hΩm : ∀ n, MeasurableSet (Ω n) := by
    intro n; simp only [Ω]; split_ifs <;> simp [hA, hB]
  have hΩd : Pairwise (Function.onFun Disjoint Ω) := by
    intro i j hij
    simp only [Function.onFun, Ω]
    split_ifs <;> first | (subst_vars; exact absurd rfl hij) | exact hAB | exact hAB.symm | simp_all
  have hU : (⋃ n, Ω n) = A ∪ B := by
    ext x; simp only [Set.mem_iUnion, Set.mem_union, Ω]
    constructor
    · rintro ⟨n, hn⟩; split_ifs at hn <;> simp_all
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
  have := hP.2.2 Ω hΩm hΩd ψ
  rw [hU] at this
  have hsum : ∀ N ≥ 2, ∑ n ∈ Finset.range N, P (Ω n) ψ = P A ψ + P B ψ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp [Finset.sum_range_succ, Ω]
    | succ N hN ih =>
      rw [Finset.sum_range_succ, ih]
      have : Ω N = ∅ := by simp only [Ω]; split_ifs <;> first | rfl | omega
      rw [this, pvm_empty hP]; simp
  have h2 : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, P (Ω n) ψ) Filter.atTop
      (nhds (P A ψ + P B ψ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    exact (hsum N hN).symm
  simpa using tendsto_nhds_unique this h2

lemma pvm_idem (hP : TeschlQM.Shared.IsProjValuedMeasure P) {A : Set ℝ} (hA : MeasurableSet A) :
    P A * P A = P A := (hP.1 A hA).2

lemma pvm_sa (hP : TeschlQM.Shared.IsProjValuedMeasure P) {A : Set ℝ} (hA : MeasurableSet A) :
    ContinuousLinearMap.adjoint (P A) = P A := (hP.1 A hA).1

lemma pvm_mul_disjoint (hP : TeschlQM.Shared.IsProjValuedMeasure P) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    P A * P B = 0 := by
  have hU := pvm_union hP hA hB hAB
  have hidem := pvm_idem hP (hA.union hB)
  rw [hU] at hidem
  have ha := pvm_idem hP hA
  have hb := pvm_idem hP hB
  have e1 : P A * P B + P B * P A = 0 := by
    have : (P A + P B) * (P A + P B) = P A * P A + P A * P B + P B * P A + P B * P B := by
      noncomm_ring
    rw [this, ha, hb] at hidem
    have : P A + P A * P B + P B * P A + P B - (P A + P B) = P A * P B + P B * P A := by abel
    rw [← this, hidem, sub_self]
  have e2 : P A * P B + P A * P B * P A = 0 := by
    have := congrArg (fun X => P A * X) e1
    simp only [mul_add, mul_zero, ← mul_assoc, ha] at this
    exact this
  have e3 : P A * P B * P A + P B * P A = 0 := by
    have := congrArg (fun X => X * P A) e1
    simp only [add_mul, zero_mul, mul_assoc, ha] at this
    exact this
  have e4 : P A * P B = P B * P A := by
    have := e2.trans e3.symm
    rw [add_comm (P A * P B * P A)] at this
    exact add_right_cancel this
  rw [e4] at e1
  have : (2 : ℂ) • (P B * P A) = 0 := by rw [two_smul]; exact e1
  rw [e4]
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

lemma pvm_mul (hP : TeschlQM.Shared.IsProjValuedMeasure P) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) : P A * P B = P (A ∩ B) := by
  have h1 : P A = P (A ∩ B) + P (A \ B) := by
    rw [← pvm_union hP (hA.inter hB) (hA.diff hB)
      (Set.disjoint_left.mpr fun x hx hx' => by simp_all), Set.inter_union_diff]
  have h2 : P B = P (A ∩ B) + P (B \ A) := by
    rw [← pvm_union hP (hA.inter hB) (hB.diff hA)
      (Set.disjoint_left.mpr fun x hx hx' => by simp_all), Set.inter_comm, Set.inter_union_diff]
  rw [h1, h2]
  have d1 := pvm_mul_disjoint hP (hA.inter hB) (hB.diff hA)
    (Set.disjoint_left.mpr fun x hx hx' => by simp_all)
  have d2 := pvm_mul_disjoint hP (hA.diff hB) (hA.inter hB)
    (Set.disjoint_left.mpr fun x hx hx' => by simp_all)
  have d3 := pvm_mul_disjoint hP (hA.diff hB) (hB.diff hA)
    (Set.disjoint_left.mpr fun x hx hx' => by simp_all)
  rw [add_mul, mul_add, mul_add, pvm_idem hP (hA.inter hB), d1, d2, d3]; simp

lemma pvm_inner_disjoint (hP : TeschlQM.Shared.IsProjValuedMeasure P) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) (ψ φ : H) :
    ⟪P A ψ, P B φ⟫_ℂ = 0 := by
  conv_lhs => rw [← pvm_sa hP hA]
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.mul_apply,
    pvm_mul_disjoint hP hA hB hAB]
  simp

lemma pvm_norm_sum_sq (hP : TeschlQM.Shared.IsProjValuedMeasure P) (Ω : ℕ → Set ℝ)
    (hm : ∀ n, MeasurableSet (Ω n)) (hd : Pairwise (Function.onFun Disjoint Ω)) (ψ : H) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, P (Ω n) ψ‖ ^ 2 = ∑ n ∈ Finset.range N, ‖P (Ω n) ψ‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, sq, sq, sq]
    apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro n hn
    exact pvm_inner_disjoint hP (hm n) (hm N) (hd (by simp at hn; omega)) ψ ψ

lemma sm_cond (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    ((‖P ∅ ψ‖₊ : ℝ≥0∞) ^ 2 = 0 ∧
      ∀ ⦃Ω : ℕ → Set ℝ⦄, (∀ n, MeasurableSet (Ω n)) → Pairwise (Function.onFun Disjoint Ω) →
        (‖P (⋃ n, Ω n) ψ‖₊ : ℝ≥0∞) ^ 2 = ∑' n, (‖P (Ω n) ψ‖₊ : ℝ≥0∞) ^ 2) := by
  refine ⟨by simp [pvm_empty hP], ?_⟩
  intro Ω hm hd
  have hlim := hP.2.2 Ω hm hd ψ
  have hlim2 : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ‖P (Ω n) ψ‖ ^ 2)
      Filter.atTop (nhds (‖P (⋃ n, Ω n) ψ‖ ^ 2)) := by
    have := (hlim.norm).pow 2
    simpa only [pvm_norm_sum_sq hP Ω hm hd ψ] using this
  have hsum : HasSum (fun n => ‖P (Ω n) ψ‖ ^ 2) (‖P (⋃ n, Ω n) ψ‖ ^ 2) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun n => sq_nonneg _) _).mpr hlim2
  have e : ∀ v : H, (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
    intro v
    rw [ENNReal.ofReal_pow (norm_nonneg v), ofReal_norm_eq_enorm]
    rfl
  simp only [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsum.summable, hsum.tsum_eq]

lemma spectralMeasure_apply (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) {Ω : Set ℝ}
    (hΩ : MeasurableSet Ω) :
    TeschlQM.Shared.spectralMeasure P ψ Ω = (‖P Ω ψ‖₊ : ℝ≥0∞) ^ 2 := by
  unfold TeschlQM.Shared.spectralMeasure
  rw [dif_pos (sm_cond hP ψ), Measure.ofMeasurable_apply _ hΩ]

lemma enn_norm_sq (v : H) : (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg v), ofReal_norm_eq_enorm]
  rfl

lemma pvm_univ_apply (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    P Set.univ ψ = ψ := by rw [hP.2.1]; rfl

lemma sm_univ (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    TeschlQM.Shared.spectralMeasure P ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [spectralMeasure_apply hP ψ MeasurableSet.univ, pvm_univ_apply hP, enn_norm_sq]

lemma sm_finite (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    IsFiniteMeasure (TeschlQM.Shared.spectralMeasure P ψ) :=
  ⟨by rw [sm_univ hP]; exact ENNReal.ofReal_lt_top⟩

lemma sm_real_univ (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    (TeschlQM.Shared.spectralMeasure P ψ).real Set.univ = ‖ψ‖ ^ 2 := by
  rw [measureReal_def, sm_univ hP, ENNReal.toReal_ofReal (sq_nonneg _)]

lemma sm_add_le (hP : TeschlQM.Shared.IsProjValuedMeasure P) (φ χ : H) :
    TeschlQM.Shared.spectralMeasure P (φ + χ) ≤
      (2 : ℝ≥0∞) • TeschlQM.Shared.spectralMeasure P φ +
        (2 : ℝ≥0∞) • TeschlQM.Shared.spectralMeasure P χ := by
  rw [Measure.le_iff]
  intro s hs
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [spectralMeasure_apply hP _ hs, spectralMeasure_apply hP _ hs, spectralMeasure_apply hP _ hs,
    enn_norm_sq, enn_norm_sq, enn_norm_sq, map_add]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := norm_add_le (P s φ) (P s χ)
  nlinarith [norm_nonneg (P s φ), norm_nonneg (P s χ), norm_nonneg (P s φ + P s χ),
    sq_nonneg (‖P s φ‖ - ‖P s χ‖)]

lemma sm_smul (hP : TeschlQM.Shared.IsProjValuedMeasure P) (c : ℂ) (φ : H) :
    TeschlQM.Shared.spectralMeasure P (c • φ) =
      ENNReal.ofReal (‖c‖ ^ 2) • TeschlQM.Shared.spectralMeasure P φ := by
  ext s hs
  simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [spectralMeasure_apply hP _ hs, spectralMeasure_apply hP _ hs, enn_norm_sq, enn_norm_sq,
    map_smul, norm_smul, ← ENNReal.ofReal_mul (sq_nonneg _), mul_pow]

end TeschlQM.PVMCore

namespace TeschlQM.PVMCore

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

/-- A linear map from a module containing `k` independent vectors into a space of rank `< k`
kills a nonzero vector of their span. -/
lemma exists_ker_of_rank_lt {M N : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] {k : ℕ} (v : Fin k → M) (hli : LinearIndependent ℂ v) (T : M →ₗ[ℂ] N)
    (h : ¬ (k : Cardinal) ≤ Module.rank ℂ (LinearMap.range T)) :
    ∃ φ ∈ Submodule.span ℂ (Set.range v), φ ≠ 0 ∧ T φ = 0 := by
  by_contra hne
  push_neg at hne
  apply h
  let V := Submodule.span ℂ (Set.range v)
  let L : V →ₗ[ℂ] LinearMap.range T := T.rangeRestrict.comp V.subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have : T (x : M) = 0 := by
      have := congrArg Subtype.val hx
      simpa [L] using this
    exact hne x x.2 (by simpa using hx0) this
  have := LinearMap.rank_le_of_injective L hinj
  have hk : Cardinal.mk (Set.range v) = k := by
    have := Cardinal.mk_range_eq_of_injective hli.injective
    rw [← Cardinal.lift_inj.{u, 0}]
    simpa using this
  rw [rank_span hli, hk] at this
  exact this

lemma mem_formDomain_add (hP : TeschlQM.Shared.IsProjValuedMeasure P) {φ χ : H}
    (hφ : φ ∈ TeschlQM.MinMax.formDomain P) (hχ : χ ∈ TeschlQM.MinMax.formDomain P) :
    φ + χ ∈ TeschlQM.MinMax.formDomain P := by
  unfold TeschlQM.MinMax.formDomain at *
  simp only [Set.mem_setOf_eq] at *
  calc ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ∂TeschlQM.Shared.spectralMeasure P (φ + χ)
      ≤ ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ∂((2 : ℝ≥0∞) • TeschlQM.Shared.spectralMeasure P φ +
        (2 : ℝ≥0∞) • TeschlQM.Shared.spectralMeasure P χ) := lintegral_mono' (sm_add_le hP φ χ) le_rfl
    _ < ∞ := by
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by simp) hφ,
        ENNReal.mul_lt_top (by simp) hχ⟩

lemma mem_formDomain_smul (hP : TeschlQM.Shared.IsProjValuedMeasure P) (c : ℂ) {φ : H}
    (hφ : φ ∈ TeschlQM.MinMax.formDomain P) :
    c • φ ∈ TeschlQM.MinMax.formDomain P := by
  unfold TeschlQM.MinMax.formDomain at *
  simp only [Set.mem_setOf_eq] at *
  rw [sm_smul hP, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ

lemma span_sub_formDomain (hP : TeschlQM.Shared.IsProjValuedMeasure P) {k : ℕ} (ψ : Fin k → H)
    (hQ : ∀ j, ψ j ∈ TeschlQM.MinMax.formDomain P) {φ : H}
    (hφ : φ ∈ Submodule.span ℂ (Set.range ψ)) : φ ∈ TeschlQM.MinMax.formDomain P := by
  induction hφ using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hQ j
  | zero =>
    have h0 : TeschlQM.Shared.spectralMeasure P (0 : H) = 0 := by
      have := sm_smul hP 0 (0 : H)
      simpa using this
    unfold TeschlQM.MinMax.formDomain
    simp [h0]
  | add x y _ _ hx hy => exact mem_formDomain_add hP hx hy
  | smul c x _ hx => exact mem_formDomain_smul hP c hx

lemma quad_ge_of_ker (hP : TeschlQM.Shared.IsProjValuedMeasure P) {φ : H}
    (hφ : φ ∈ TeschlQM.MinMax.formDomain P) (lam : ℝ) (hz : P (Set.Iio lam) φ = 0) :
    lam * ‖φ‖ ^ 2 ≤ TeschlQM.MinMax.quadForm P φ := by
  haveI := sm_finite hP φ
  have hint : Integrable (fun x : ℝ => x) (TeschlQM.Shared.spectralMeasure P φ) :=
    ⟨measurable_id.aestronglyMeasurable, hφ⟩
  have hnull : TeschlQM.Shared.spectralMeasure P φ (Set.Iio lam) = 0 := by
    rw [spectralMeasure_apply hP φ measurableSet_Iio, hz]; simp
  have hae : ∀ᵐ x ∂(TeschlQM.Shared.spectralMeasure P φ), lam ≤ x := by
    rw [ae_iff]
    have : {a : ℝ | ¬lam ≤ a} = Set.Iio lam := by ext; simp
    rw [this]; exact hnull
  have := integral_mono_ae (integrable_const lam) hint hae
  rw [integral_const, smul_eq_mul, sm_real_univ hP] at this
  unfold TeschlQM.MinMax.quadForm
  linarith

lemma quad_le_of_ker (hP : TeschlQM.Shared.IsProjValuedMeasure P) {φ : H}
    (hφ : φ ∈ TeschlQM.MinMax.formDomain P) (lam : ℝ) (hz : P (Set.Ioi lam) φ = 0) :
    TeschlQM.MinMax.quadForm P φ ≤ lam * ‖φ‖ ^ 2 := by
  haveI := sm_finite hP φ
  have hint : Integrable (fun x : ℝ => x) (TeschlQM.Shared.spectralMeasure P φ) :=
    ⟨measurable_id.aestronglyMeasurable, hφ⟩
  have hnull : TeschlQM.Shared.spectralMeasure P φ (Set.Ioi lam) = 0 := by
    rw [spectralMeasure_apply hP φ measurableSet_Ioi, hz]; simp
  have hae : ∀ᵐ x ∂(TeschlQM.Shared.spectralMeasure P φ), x ≤ lam := by
    rw [ae_iff]
    have : {a : ℝ | ¬a ≤ lam} = Set.Ioi lam := by ext; simp
    rw [this]; exact hnull
  have := integral_mono_ae hint (integrable_const lam) hae
  rw [integral_const, smul_eq_mul, sm_real_univ hP] at this
  unfold TeschlQM.MinMax.quadForm
  linarith

end TeschlQM.PVMCore

open TeschlQM.PVMCore TeschlQM.MinMax

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    {k : ℕ} (ψ : Fin k → H) (hli : LinearIndependent ℂ ψ) (hQ : ∀ j, ψ j ∈ formDomain P)
    (lam : ℝ) :
    ((∀ φ ∈ Submodule.span ℂ (Set.range ψ), φ ≠ 0 → quadForm P φ < lam * ‖φ‖ ^ 2) →
        (k : Cardinal) ≤ Module.rank ℂ (LinearMap.range (P (Set.Iio lam) : H →ₗ[ℂ] H))) ∧
      ((∀ φ ∈ Submodule.span ℂ (Set.range ψ), φ ≠ 0 → lam * ‖φ‖ ^ 2 < quadForm P φ) →
        (k : Cardinal) ≤ Module.rank ℂ (LinearMap.range (P (Set.Ioi lam) : H →ₗ[ℂ] H))) := by
  constructor
  · intro h
    by_contra hk
    obtain ⟨φ, hφV, hφ0, hPφ⟩ := exists_ker_of_rank_lt ψ hli (P (Set.Iio lam) : H →ₗ[ℂ] H) hk
    have h1 := quad_ge_of_ker hP (span_sub_formDomain hP ψ hQ hφV) lam hPφ
    have h2 := h φ hφV hφ0
    linarith
  · intro h
    by_contra hk
    obtain ⟨φ, hφV, hφ0, hPφ⟩ := exists_ker_of_rank_lt ψ hli (P (Set.Ioi lam) : H →ₗ[ℂ] H) hk
    have h1 := quad_le_of_ker hP (span_sub_formDomain hP ψ hQ hφV) lam hPφ
    have h2 := h φ hφV hφ0
    linarith
