-- Prove2me | solution 1 for TeschlQM.MinMax.dim_range_ge_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T12:21:14.351975+00:00
-- url     : https://prove2.me/submissions/0e481547-a042-4fe2-8f13-62503478578e

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral

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

end TeschlQM.PVMCore

namespace TeschlQM.PVMCore

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma symm_of_sa {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (x y : A.domain) :
    ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ := by
  have h := LinearPMap.isSelfAdjoint_def.mp hA
  have hdom : A.adjoint.domain = A.domain := by rw [h]
  obtain ⟨_, h2⟩ := LinearPMap.ext_iff.mp h
  have hx : (x : H) ∈ A.adjoint.domain := by rw [hdom]; exact x.2
  have := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain ⟨x, hx⟩ y
  rw [@h2 (x : H) hx x.2] at this
  simpa using this

/-- The spectral measure of `a • P(Δ) φ + b • φ`. -/
lemma sm_comb (hP : TeschlQM.Shared.IsProjValuedMeasure P) {Δ : Set ℝ} (hΔ : MeasurableSet Δ)
    (a b : ℂ) (φ : H) :
    TeschlQM.Shared.spectralMeasure P (a • P Δ φ + b • φ) =
      ENNReal.ofReal (‖a + b‖ ^ 2) • (TeschlQM.Shared.spectralMeasure P φ).restrict Δ +
        ENNReal.ofReal (‖b‖ ^ 2) • (TeschlQM.Shared.spectralMeasure P φ).restrict Δᶜ := by
  ext s hs
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Measure.restrict_apply hs]
  rw [spectralMeasure_apply hP _ hs, spectralMeasure_apply hP _ (hs.inter hΔ),
    spectralMeasure_apply hP _ (hs.inter hΔ.compl), enn_norm_sq, enn_norm_sq, enn_norm_sq]
  have hsplit : P s = P (s ∩ Δ) + P (s ∩ Δᶜ) := by
    rw [← pvm_union hP (hs.inter hΔ) (hs.inter hΔ.compl)
      (Set.disjoint_left.mpr fun x hx hx' => by simp_all), ← Set.inter_union_distrib_left,
      Set.union_compl_self, Set.inter_univ]
  have hval : P s (a • P Δ φ + b • φ) = (a + b) • P (s ∩ Δ) φ + b • P (s ∩ Δᶜ) φ := by
    rw [map_add, map_smul, map_smul, ← ContinuousLinearMap.mul_apply, pvm_mul hP hs hΔ, hsplit,
      ContinuousLinearMap.add_apply]
    module
  have horth : ⟪(a + b) • P (s ∩ Δ) φ, b • P (s ∩ Δᶜ) φ⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, pvm_inner_disjoint hP (hs.inter hΔ) (hs.inter hΔ.compl)
      (Set.disjoint_left.mpr fun x hx hx' => by simp_all)]
    simp
  rw [hval, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  rw [sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ horth,
    norm_smul, norm_smul]
  ring

/-- Elements of the domain have integrable first moment. -/
lemma integrable_of_spectralDomain (hP : TeschlQM.Shared.IsProjValuedMeasure P) {φ : H}
    (hφ : φ ∈ TeschlQM.Shared.spectralDomain P (fun x : ℝ => (x : ℂ))) :
    Integrable (fun x : ℝ => x) (TeschlQM.Shared.spectralMeasure P φ) := by
  haveI := sm_finite hP φ
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  unfold TeschlQM.Shared.spectralDomain at hφ
  simp only [Set.mem_setOf_eq, Complex.nnnorm_real] at hφ
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖x‖ₑ ∂TeschlQM.Shared.spectralMeasure P φ
      ≤ ∫⁻ x, (1 + (‖x‖₊ : ℝ≥0∞) ^ 2) ∂TeschlQM.Shared.spectralMeasure P φ := by
        apply lintegral_mono
        intro x
        show (‖x‖₊ : ℝ≥0∞) ≤ 1 + (‖x‖₊ : ℝ≥0∞) ^ 2
        rcases le_total (‖x‖₊ : ℝ≥0∞) 1 with h | h
        · exact h.trans le_self_add
        · calc (‖x‖₊ : ℝ≥0∞) = ‖x‖₊ * 1 := (mul_one _).symm
            _ ≤ ‖x‖₊ * ‖x‖₊ := by gcongr
            _ = (‖x‖₊ : ℝ≥0∞) ^ 2 := (sq _).symm
            _ ≤ 1 + (‖x‖₊ : ℝ≥0∞) ^ 2 := le_add_self
    _ < ∞ := by
        rw [lintegral_add_left measurable_const]
        simp only [lintegral_const, one_mul]
        exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, hφ⟩

lemma mem_spectralDomain_comb (hP : TeschlQM.Shared.IsProjValuedMeasure P) {Δ : Set ℝ}
    (hΔ : MeasurableSet Δ) (a b : ℂ) {φ : H}
    (hφ : φ ∈ TeschlQM.Shared.spectralDomain P (fun x : ℝ => (x : ℂ))) :
    a • P Δ φ + b • φ ∈ TeschlQM.Shared.spectralDomain P (fun x : ℝ => (x : ℂ)) := by
  unfold TeschlQM.Shared.spectralDomain at *
  simp only [Set.mem_setOf_eq] at *
  rw [sm_comb hP hΔ, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
  · exact lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) hφ
  · exact lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) hφ

lemma integral_comb (hP : TeschlQM.Shared.IsProjValuedMeasure P) {Δ : Set ℝ}
    (hΔ : MeasurableSet Δ) (a b : ℂ) {φ : H}
    (hφ : φ ∈ TeschlQM.Shared.spectralDomain P (fun x : ℝ => (x : ℂ))) :
    ∫ x, x ∂TeschlQM.Shared.spectralMeasure P (a • P Δ φ + b • φ) =
      ‖a + b‖ ^ 2 * ∫ x in Δ, x ∂TeschlQM.Shared.spectralMeasure P φ +
        ‖b‖ ^ 2 * ∫ x in Δᶜ, x ∂TeschlQM.Shared.spectralMeasure P φ := by
  have hint := integrable_of_spectralDomain hP hφ
  rw [sm_comb hP hΔ, integral_add_measure, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
    smul_eq_mul]
  · exact (hint.restrict).smul_measure ENNReal.ofReal_ne_top
  · exact (hint.restrict).smul_measure ENNReal.ofReal_ne_top

/-- Key identity: `Re ⟨P(Δ) φ, A φ⟩ = ∫_Δ x dμ_φ`. -/
lemma re_inner_proj_apply (hP : TeschlQM.Shared.IsProjValuedMeasure P) {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    {Δ : Set ℝ} (hΔ : MeasurableSet Δ) (φ : A.domain) :
    ∃ hX : P Δ φ ∈ A.domain,
      (⟪P Δ φ, A φ⟫_ℂ).re = ∫ x in Δ, x ∂TeschlQM.Shared.spectralMeasure P φ := by
  have hdom : ∀ v : H, v ∈ A.domain ↔ v ∈ TeschlQM.Shared.spectralDomain P (fun x : ℝ => (x : ℂ)) :=
    fun v => by rw [← hAP.1]; rfl
  have hφ := (hdom φ).mp φ.2
  have hX : P Δ φ ∈ A.domain := by
    have := mem_spectralDomain_comb hP hΔ 1 0 hφ
    simp only [one_smul, zero_smul, add_zero] at this
    exact (hdom _).mpr this
  refine ⟨hX, ?_⟩
  set X : A.domain := ⟨P Δ φ, hX⟩
  have hq : ∀ u : A.domain, ⟪(u : H), A u⟫_ℂ =
      ((∫ x, x ∂TeschlQM.Shared.spectralMeasure P u : ℝ) : ℂ) := by
    intro u; rw [hAP.2 u]; exact integral_ofReal
  -- quadratic form of `X` and of `X + φ`
  have h0 := hq X
  have h1 := hq (X + φ)
  have e0 : ∫ x, x ∂TeschlQM.Shared.spectralMeasure P (X : H) =
      ∫ x in Δ, x ∂TeschlQM.Shared.spectralMeasure P φ := by
    have := integral_comb hP hΔ 1 0 hφ
    simp only [one_smul, zero_smul, add_zero, norm_one, norm_zero] at this
    simpa using this
  have e1 : ∫ x, x ∂TeschlQM.Shared.spectralMeasure P ((X + φ : A.domain) : H) =
      4 * ∫ x in Δ, x ∂TeschlQM.Shared.spectralMeasure P φ +
        ∫ x in Δᶜ, x ∂TeschlQM.Shared.spectralMeasure P φ := by
    have := integral_comb hP hΔ 1 1 hφ
    simp only [one_smul] at this
    rw [show ((X + φ : A.domain) : H) = P Δ φ + φ from rfl, this]
    norm_num
  have e2 : ∫ x, x ∂TeschlQM.Shared.spectralMeasure P (φ : H) =
      ∫ x in Δ, x ∂TeschlQM.Shared.spectralMeasure P φ +
        ∫ x in Δᶜ, x ∂TeschlQM.Shared.spectralMeasure P φ := by
    rw [integral_add_compl hΔ (integrable_of_spectralDomain hP hφ)]
  have h2 := hq φ
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [LinearPMap.map_add] at h1
  simp only [Submodule.coe_add, inner_add_left, inner_add_right] at h1
  have hs := symm_of_sa hA φ X
  -- `⟨φ, A X⟩ = conj ⟨X, A φ⟩`
  have hc : ⟪(φ : H), A X⟫_ℂ = (starRingEnd ℂ) ⟪(X : H), A φ⟫_ℂ := by
    rw [← hs, inner_conj_symm]
  rw [hc, h0, h2] at h1
  have := congrArg Complex.re h1
  simp only [Complex.add_re, Complex.ofReal_re, Complex.conj_re] at this
  show (⟪(X : H), A φ⟫_ℂ).re = _
  linarith

lemma sm_real_apply (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) {Ω : Set ℝ}
    (hΩ : MeasurableSet Ω) :
    (TeschlQM.Shared.spectralMeasure P ψ).real Ω = ‖P Ω ψ‖ ^ 2 := by
  rw [measureReal_def, spectralMeasure_apply hP ψ hΩ, enn_norm_sq,
    ENNReal.toReal_ofReal (sq_nonneg _)]

/-- If `P((λ₁, λ₂)) φ = 0` then `‖(A - c) φ‖ ≥ r ‖φ‖` with `c, r` the midpoint and half-width. -/
lemma norm_ge_of_ker (hP : TeschlQM.Shared.IsProjValuedMeasure P) {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (lam₁ lam₂ : ℝ) (hlt : lam₁ < lam₂) (φ : A.domain)
    (hz : P (Set.Ioo lam₁ lam₂) φ = 0) :
    (lam₂ - lam₁) / 2 * ‖(φ : H)‖ ≤
      ‖A φ - (((lam₂ + lam₁) / 2 : ℝ) : ℂ) • (φ : H)‖ := by
  set c : ℝ := (lam₂ + lam₁) / 2
  set Dp : Set ℝ := Set.Ici lam₂
  set Dm : Set ℝ := Set.Iic lam₁
  have hDp : MeasurableSet Dp := measurableSet_Ici
  have hDm : MeasurableSet Dm := measurableSet_Iic
  have hdisj : Disjoint Dm Dp :=
    Set.disjoint_left.mpr fun x hx hx' => by simp [Dm, Dp] at hx hx'; linarith
  -- decomposition of `φ`
  have hU : Set.univ = (Dm ∪ Set.Ioo lam₁ lam₂) ∪ Dp := by
    ext x; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_Ici, true_iff,
      Dm, Dp]
    by_cases h1 : x ≤ lam₁
    · left; left; exact h1
    by_cases h2 : lam₂ ≤ x
    · right; exact h2
    left; right; constructor <;> linarith [not_le.mp h1, not_le.mp h2]
  have hdec : (φ : H) = P Dm φ + P Dp φ := by
    have h := pvm_univ_apply hP (φ : H)
    rw [hU, pvm_union hP (hDm.union measurableSet_Ioo) hDp
      (Set.disjoint_left.mpr fun x hx hx' => by
        simp [Dm, Dp] at hx hx'; rcases hx with hx | ⟨_, hx⟩ <;> linarith),
      pvm_union hP hDm measurableSet_Ioo
      (Set.disjoint_left.mpr fun x hx hx' => by simp [Dm] at hx hx'; linarith [hx'.1])] at h
    simp only [ContinuousLinearMap.add_apply, hz, add_zero] at h
    exact h.symm
  set φp := P Dp (φ : H)
  set φm := P Dm (φ : H)
  have horth : ⟪φm, φp⟫_ℂ = 0 := pvm_inner_disjoint hP hDm hDp hdisj φ φ
  have horth' : ⟪φp, φm⟫_ℂ = 0 := by rw [← inner_conj_symm, horth]; simp
  have hnφ : ‖(φ : H)‖ ^ 2 = ‖φp‖ ^ 2 + ‖φm‖ ^ 2 := by
    rw [hdec, sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ horth]
    ring
  set χ := φp - φm
  have hnχ : ‖χ‖ = ‖(φ : H)‖ := by
    have : ‖χ‖ ^ 2 = ‖φp‖ ^ 2 + ‖φm‖ ^ 2 := by
      have h3 : ⟪φp, -φm⟫_ℂ = 0 := by rw [inner_neg_right, horth', neg_zero]
      rw [show χ = φp + -φm from sub_eq_add_neg _ _, sq, sq, sq,
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ h3, norm_neg]
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), this, hnφ]
  have hpφ : (⟪φp, (φ : H)⟫_ℂ).re = ‖φp‖ ^ 2 := by
    rw [hdec, inner_add_right, horth', zero_add, inner_self_eq_norm_sq_to_K]; norm_cast
  have hmφ : (⟪φm, (φ : H)⟫_ℂ).re = ‖φm‖ ^ 2 := by
    rw [hdec, inner_add_right, horth, add_zero, inner_self_eq_norm_sq_to_K]; norm_cast
  -- the integrals
  have hφd : (φ : H) ∈ TeschlQM.Shared.spectralDomain P (fun x : ℝ => (x : ℂ)) := by
    rw [← hAP.1]; exact φ.2
  have hint := integrable_of_spectralDomain hP hφd
  haveI := sm_finite hP (φ : H)
  obtain ⟨_, hp⟩ := re_inner_proj_apply hP hA hAP hDp φ
  obtain ⟨_, hm⟩ := re_inner_proj_apply hP hA hAP hDm φ
  have ip : lam₂ * ‖φp‖ ^ 2 ≤ (⟪φp, A φ⟫_ℂ).re := by
    rw [hp]
    have := setIntegral_ge_of_const_le (c := lam₂) hDp (measure_ne_top _ _)
      (fun x hx => hx) hint.integrableOn
    rw [sm_real_apply hP _ hDp, smul_eq_mul] at this
    linarith
  have im : (⟪φm, A φ⟫_ℂ).re ≤ lam₁ * ‖φm‖ ^ 2 := by
    rw [hm]
    have := setIntegral_mono_on hint.integrableOn (integrableOn_const (C := lam₁)
      (measure_ne_top _ _)) hDm (fun x hx => hx)
    rw [setIntegral_const, sm_real_apply hP _ hDm, smul_eq_mul] at this
    linarith
  -- Cauchy–Schwarz
  have hre : (⟪χ, A φ - (c : ℂ) • (φ : H)⟫_ℂ).re =
      (⟪φp, A φ⟫_ℂ).re - (⟪φm, A φ⟫_ℂ).re - c * (‖φp‖ ^ 2 - ‖φm‖ ^ 2) := by
    rw [inner_sub_right, inner_smul_right, inner_sub_left, inner_sub_left, Complex.sub_re,
      Complex.sub_re, Complex.re_ofReal_mul, Complex.sub_re, hpφ, hmφ]
  have hcs : (⟪χ, A φ - (c : ℂ) • (φ : H)⟫_ℂ).re ≤ ‖χ‖ * ‖A φ - (c : ℂ) • (φ : H)‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [hre, hnχ] at hcs
  have key : (lam₂ - lam₁) / 2 * ‖(φ : H)‖ ^ 2 ≤
      ‖(φ : H)‖ * ‖A φ - (c : ℂ) • (φ : H)‖ := by
    rw [hnφ]; simp only [c] at hcs ⊢; nlinarith
  rcases eq_or_lt_of_le (norm_nonneg (φ : H)) with h0 | h0
  · rw [← h0]; simp
  · nlinarith

end TeschlQM.PVMCore

open TeschlQM.PVMCore

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (lam₁ lam₂ : ℝ) (hlt : lam₁ < lam₂)
    {k : ℕ} (ψ : Fin k → A.domain) (hli : LinearIndependent ℂ (fun j => (ψ j : H)))
    (h : ∀ φ ∈ Submodule.span ℂ (Set.range ψ), φ ≠ 0 →
      ‖A φ - (((lam₂ + lam₁) / 2 : ℝ) : ℂ) • (φ : H)‖ < (lam₂ - lam₁) / 2 * ‖(φ : H)‖) :
    (k : Cardinal) ≤ Module.rank ℂ (LinearMap.range (P (Set.Ioo lam₁ lam₂) : H →ₗ[ℂ] H)) := by
  by_contra hk
  have hli' : LinearIndependent ℂ ψ := LinearIndependent.of_comp A.domain.subtype hli
  obtain ⟨φ, hφV, hφ0, hPφ⟩ := exists_ker_of_rank_lt ψ hli'
    ((P (Set.Ioo lam₁ lam₂) : H →ₗ[ℂ] H) ∘ₗ A.domain.subtype)
    (fun h' => hk (h'.trans (Submodule.rank_mono (LinearMap.range_comp_le_range _ _))))
  have hz : P (Set.Ioo lam₁ lam₂) φ = 0 := by simpa using hPφ
  have h1 := norm_ge_of_ker hP hA hAP lam₁ lam₂ hlt φ hz
  have h2 := h φ hφV hφ0
  linarith
