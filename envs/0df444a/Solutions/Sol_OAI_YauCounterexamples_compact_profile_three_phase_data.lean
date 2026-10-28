-- Prove2me | solution 1 for OAI.YauCounterexamples.compact_profile_three_phase_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:26:20.627626+00:00
-- url     : https://prove2.me/submissions/e34a6bfe-74d1-40bd-990d-0cd89bfa53e3

import Mathlib
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RealForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem phase_hessian_exists (H : RealForm V) (hH : H.IsSymm)
    (a b : V) (hab : inner ℝ a b = 0)
    (hsize : inner ℝ b b = 1 + inner ℝ a a)
    (hstrict : 0 < H a a + H b b) : Nonempty (AdmissiblePhaseHessian H a b) := by
  by_cases ha : a = 0
  · subst a
    have hb : 0 < H b b := by simpa using hstrict
    exact ⟨admissibleCritical H hH b hb⟩
  · have hb : b ≠ 0 := by
      intro h
      subst b
      simp only [inner_zero_left] at hsize
      have := real_inner_self_nonneg (x := a)
      linarith
    exact ⟨admissibleNoncritical H hH a b ha hb hab hstrict⟩
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CriticalTransversePositive
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Submodule
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma critical_transverse_positive (hd : Module.finrank ℝ E = 3)
    (H : RealForm E) {ν : E} (hν : ‖ν‖ = 1)
    (hP : ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H v v) :
    ∃ b : E, ‖b‖ = 1 ∧ inner ℝ ν b = 0 ∧ 0 < H b b := by
  obtain ⟨P, hdP, hP⟩ := hP
  have hνne : ν ≠ 0 := by intro he; simp [he] at hν
  let : Fact (Module.finrank ℝ E = 2 + 1) := ⟨hd⟩
  let K := (ℝ ∙ ν)ᗮ
  have hdK : Module.finrank ℝ K = 2 := finrank_orthogonal_span_singleton hνne
  have hdim := P.finrank_sup_add_finrank_inf_eq K
  have hle : Module.finrank ℝ (P ⊔ K : Submodule ℝ E) ≤ 3 := (Submodule.finrank_le _).trans_eq hd
  have hpos : 0 < Module.finrank ℝ (P ⊓ K : Submodule ℝ E) := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hvE : (v : E) ≠ 0 := fun he => hv (Subtype.ext he)
  let b : E := ‖(v : E)‖⁻¹ • (v : E)
  have hnp : 0 < ‖(v : E)‖ := norm_pos_iff.mpr hvE
  refine ⟨b, ?_, ?_, ?_⟩
  · simp [b, norm_smul, hnp.ne']
  · have ho := mem_orthogonal_singleton_iff_inner_right.mp v.property.2
    simp [b, inner_smul_right, ho]
  · have hvpos := hP (v : E) v.property.1 hvE
    dsimp [b]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    positivity

lemma exists_good_transverse (hd : Module.finrank ℝ E = 3)
    (H : RealForm E) (a ν : E) (hν : ‖ν‖ = 1) (haν : a = ‖a‖ • ν)
    (hnc : a ≠ 0 → ∃ b, inner ℝ a b = 0 ∧ ‖b‖^2 = 1 + ‖a‖^2 ∧
      0 < H a a + H b b)
    (hc : a = 0 → ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H v v) :
    ∃ b, inner ℝ ν b = 0 ∧ ‖b‖^2 = 1 + ‖a‖^2 ∧ 0 < H a a + H b b := by
  by_cases ha : a = 0
  · obtain ⟨b, hb, hνb, hH⟩ := critical_transverse_positive hd H hν (hc ha)
    exact ⟨b, hνb, by simp [ha, hb], by simpa [ha] using hH⟩
  · obtain ⟨b, hab, hb, hH⟩ := hnc ha
    refine ⟨b, ?_, hb, hH⟩
    have he : ‖a‖ * inner ℝ ν b = 0 := by
      rw [haν, inner_smul_left, conj_trivial] at hab
      exact hab
    exact (mul_eq_zero.mp he).resolve_left (norm_ne_zero_iff.mpr ha)

omit [FiniteDimensional ℝ E] in
lemma exists_second_transverse_unit (hd : Module.finrank ℝ E = 3)
    {ν b : E} (hν : ν ≠ 0) (hb : b ≠ 0) (hνb : inner ℝ ν b = 0) :
    ∃ w : E, ‖w‖ = 1 ∧ inner ℝ ν w = 0 ∧ inner ℝ b w = 0 := by
  let K := (ℝ ∙ ν)ᗮ
  let bK : K := ⟨b, mem_orthogonal_singleton_iff_inner_right.mpr hνb⟩
  have hbK : bK ≠ 0 := fun he => hb (congrArg Subtype.val he)
  let : Fact (Module.finrank ℝ E = 2 + 1) := ⟨hd⟩
  have hK : Module.finrank ℝ K = 2 := finrank_orthogonal_span_singleton hν
  let : Fact (Module.finrank ℝ K = 1 + 1) := ⟨hK⟩
  let B : OrthonormalBasis (Fin 1) ℝ ((ℝ ∙ bK)ᗮ : Submodule ℝ K) :=
    OrthonormalBasis.fromOrthogonalSpanSingleton 1 hbK
  let wK : K := B 0
  refine ⟨wK, B.norm_eq_one 0, ?_, ?_⟩
  · exact mem_orthogonal_singleton_iff_inner_right.mp wK.property
  · have h : inner ℝ bK wK = 0 :=
      mem_orthogonal_singleton_iff_inner_right.mp (B 0).property
    exact h

theorem two_good_transverse (hd : Module.finrank ℝ E = 3)
    (H : RealForm E) (a ν : E) (hν : ‖ν‖ = 1)
    (b : E) (hνb : inner ℝ ν b = 0) (hb : ‖b‖^2 = 1 + ‖a‖^2)
    (hgood : 0 < H a a + H b b) :
    ∃ c : E, inner ℝ ν c = 0 ∧ ‖c‖^2 = 1 + ‖a‖^2 ∧
      0 < H a a + H c c ∧
      0 < ‖b‖^2 * ‖c‖^2 - (inner ℝ b c)^2 := by
  have hbpos : 0 < ‖b‖ := by nlinarith [norm_nonneg b, sq_nonneg ‖a‖]
  have hνne : ν ≠ 0 := by intro he; simp [he] at hν
  obtain ⟨w, hw, hνw, hbw⟩ := exists_second_transverse_unit hd hνne
    (norm_ne_zero_iff.mp hbpos.ne') hνb
  let f : ℝ → E := fun t => Real.cos t • b + (‖b‖ * Real.sin t) • w
  have hf : Continuous f := by unfold f; fun_prop
  have hf0 : f 0 = b := by simp [f]
  have hc : Continuous (fun t => H a a + H (f t) (f t)) :=
    continuous_const.add ((H.toContinuousBilinearMap.continuous.comp hf).clm_apply hf)
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < H a a + H (f t) (f t) :=
    (hc.tendsto 0).eventually_const_lt (by simpa [hf0] using hgood)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  let t : ℝ := min (ε / 2) (Real.pi / 2)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
  have htπ : t < Real.pi := (min_le_right _ _).trans_lt (by nlinarith [Real.pi_pos])
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht htπ
  have hn : inner ℝ b b = ‖b‖^2 := real_inner_self_eq_norm_sq b
  have hnw : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwb : inner ℝ w b = 0 := by simpa [real_inner_comm] using hbw
  have hfn : ‖f t‖^2 = ‖b‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [f, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, conj_trivial, hn, hnw, hbw, hwb, mul_zero, zero_add, add_zero]
    calc
      _ = ‖b‖^2 * ((Real.sin t)^2 + (Real.cos t)^2) := by ring
      _ = ‖b‖^2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hinner : inner ℝ b (f t) = Real.cos t * ‖b‖^2 := by
    simp only [f, inner_add_right, inner_smul_right, hn, hbw, mul_zero, add_zero]
  refine ⟨f t, ?_, hfn.trans hb, ?_, ?_⟩
  · simp [f, inner_add_right, inner_smul_right, hνb, hνw]
  · exact he (by simpa [Real.dist_eq, abs_of_pos ht] using htε)
  · rw [hfn, hinner]
    have heq : ‖b‖^2 * ‖b‖^2 - (Real.cos t * ‖b‖^2)^2 =
        ‖b‖^4 * (Real.sin t)^2 := by
      calc
        _ = ‖b‖^4 * (1 - (Real.cos t)^2) := by ring
        _ = ‖b‖^4 * (Real.sin t)^2 := by
          rw [show 1 - (Real.cos t)^2 = (Real.sin t)^2 by
            linarith [Real.sin_sq_add_cos_sq t]]
    rw [heq]
    positivity

theorem actual_two_transverse_phases (hd : Module.finrank ℝ E = 3)
    (H : RealForm E) (a ν : E) (hν : ‖ν‖ = 1) (haν : a = ‖a‖ • ν)
    (hnc : a ≠ 0 → ∃ b, inner ℝ a b = 0 ∧ ‖b‖^2 = 1 + ‖a‖^2 ∧
      0 < H a a + H b b)
    (hc : a = 0 → ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H v v) :
    ∃ b c, inner ℝ ν b = 0 ∧ inner ℝ ν c = 0 ∧
      ‖b‖^2 = 1 + ‖a‖^2 ∧ ‖c‖^2 = 1 + ‖a‖^2 ∧
      0 < H a a + H b b ∧ 0 < H a a + H c c ∧
      0 < ‖b‖^2 * ‖c‖^2 - (inner ℝ b c)^2 := by
  obtain ⟨b, hνb, hb, hgood⟩ := exists_good_transverse hd H a ν hν haν hnc hc
  obtain ⟨c, hνc, hcn, hcg, hangle⟩ := two_good_transverse hd H a ν hν b hνb hb hgood
  exact ⟨b, c, hνb, hνc, hb, hcn, hgood, hcg, hangle⟩

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseFormMatrix
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology

lemma continuous_quadratic_coercive {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (q : V → ℝ) (hq : Continuous q)
    (hhom : ∀ (c : ℝ) (v : V), q (c • v) = c^2 * q v)
    (hpos : ∀ v ≠ 0, 0 < q v) : ∃ μ > 0, ∀ v, μ * ‖v‖^2 ≤ q v := by
  have hzero : q 0 = 0 := by simpa using hhom 0 0
  cases subsingleton_or_nontrivial V with
  | inl h =>
    let := h
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    rw [Subsingleton.elim v 0, norm_zero, hzero]
    norm_num
  | inr h =>
    let := h
    obtain ⟨v, hv⟩ : ∃ v : V, ‖v‖ = 1 := by
      obtain ⟨w, hw⟩ := exists_ne (0 : V)
      refine ⟨‖w‖⁻¹ • w, ?_⟩
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      ⟨v, by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩ hq.continuousOn
    have hv₀norm : ‖v₀‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv₀
    have hv₀ne : v₀ ≠ 0 := by intro hz; simp [hz] at hv₀norm
    refine ⟨q v₀, hpos v₀ hv₀ne, ?_⟩
    intro w
    by_cases hw : w = 0
    · simp [hw, hzero]
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hwn.le), inv_mul_cancel₀ hwn.ne']
    have hh := hmin (show ‖w‖⁻¹ • w ∈ Metric.sphere (0 : V) 1 by
      simpa [Metric.mem_sphere, dist_zero_right] using hunit)
    change q v₀ ≤ q (‖w‖⁻¹ • w) at hh
    rw [hhom] at hh
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖w‖)
    calc
      _ ≤ (‖w‖⁻¹)^2 * q w * ‖w‖^2 := hh'
      _ = q w := by field_simp

variable {ι : Type*} [Fintype ι]

lemma realQuadratic_hom (a : ι → ι → ℝ) (c : ℝ) (v : ι → ℝ) :
    realQuadratic a (c • v) = c^2 * realQuadratic a v := by
  simp only [realQuadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma squareSum_nonneg (v : ι → ℝ) : 0 ≤ squareSum v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma abs_mul_le_squareSum (v : ι → ℝ) (i j : ι) : |v i * v j| ≤ squareSum v := by
  have hi : v i * v i ≤ squareSum v :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ i)
  have hj : v j * v j ≤ squareSum v :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (v i + v j), sq_nonneg (v i - v j)]

lemma realQuadratic_abs_bound (a : ι → ι → ℝ) (v : ι → ℝ) :
    |realQuadratic a v| ≤ (∑ i, ∑ j, |a i j|) * squareSum v := by
  unfold realQuadratic
  calc
    _ ≤ ∑ i, |∑ j, a i j * v i * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i j * v i * v j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_mul_le_squareSum v i j) (abs_nonneg _)

lemma realQuadratic_sub (a b : ι → ι → ℝ) (v : ι → ℝ) :
    realQuadratic (a-b) v = realQuadratic a v - realQuadratic b v := by
  simp only [realQuadratic, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma phaseProjection_annihilates (z : ι → ℂ) (hz : z ⬝ᵥ z = -1) :
    phaseProjection z *ᵥ z = 0 := by
  simp [phaseProjection, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, hz]

lemma continuedPhaseMatrix_transpose (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q)
    (z : ι → ℂ) : (continuedPhaseMatrix Q z)ᵀ = continuedPhaseMatrix Q z := by
  simp only [continuedPhaseMatrix, Matrix.transpose_mul, Matrix.transpose_transpose, hQ]
  rw [Matrix.mul_assoc]

lemma continuedPhaseMatrix_annihilates (Q : Matrix ι ι ℂ)
    (z : ι → ℂ) (hz : z ⬝ᵥ z = -1) :
    continuedPhaseMatrix Q z *ᵥ z = 0 := by
  rw [continuedPhaseMatrix, ← Matrix.mulVec_mulVec,
    phaseProjection_annihilates z hz, Matrix.mulVec_zero]

lemma continuedPhaseMatrix_eq (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q)
    (z : ι → ℂ) (hQz : Q *ᵥ z = 0) : continuedPhaseMatrix Q z = Q := by
  have hright : Q * phaseProjection z = Q := by
    simp [phaseProjection, Matrix.mul_add, Matrix.mul_vecMulVec, hQz]
  have hleft : (phaseProjection z)ᵀ * Q = Q := by
    have := congrArg Matrix.transpose hright
    simpa only [Matrix.transpose_mul, hQ] using this
  rw [continuedPhaseMatrix, hleft, hright]

lemma continuous_continuedPhaseMatrix (Q : Matrix ι ι ℂ) :
    Continuous (continuedPhaseMatrix Q) := by
  unfold continuedPhaseMatrix
  fun_prop

omit [DecidableEq ι] in
lemma strict_real_quadratic_coercive (A : Matrix ι ι ℝ)
    (hA : ∀ v : ι → ℝ, v ≠ 0 → 0 < realQuadratic A v) :
    ∃ μ > 0, ∀ v, μ * squareSum v ≤ realQuadratic A v := by
  let q : EuclideanSpace ℝ ι → ℝ := fun v => realQuadratic A v
  have hc : Continuous q := by unfold q realQuadratic; fun_prop
  have hp : ∀ v : EuclideanSpace ℝ ι, v ≠ 0 → 0 < q v := by
    intro v hv
    apply hA
    intro he
    apply hv
    ext i
    exact congrFun he i
  obtain ⟨μ, hμ, hb⟩ := continuous_quadratic_coercive q hc
    (fun c v => realQuadratic_hom A c v) hp
  refine ⟨μ, hμ, fun v => ?_⟩
  have h := hb (WithLp.toLp 2 v)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  simpa only [q, squareSum, sq, PiLp.toLp_apply] using h


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma phaseFormMatrix_mulVec (U : RealForm (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ ι) (i : ι) :
    (phaseFormMatrix U *ᵥ (fun j => v j)) i = U (EuclideanSpace.basisFun ι ℝ i) v := by
  conv_rhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct,
    phaseFormMatrix, EuclideanSpace.basisFun_repr]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
lemma realQuadratic_phaseFormMatrix (U : RealForm (EuclideanSpace ℝ ι))
    (v : ι → ℝ) : realQuadratic (phaseFormMatrix U) v =
      U (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  have heq : realQuadratic (phaseFormMatrix U) v =
      ∑ i, v i * U (EuclideanSpace.basisFun ι ℝ i) w := by
    unfold realQuadratic
    apply Finset.sum_congr rfl
    intro i _
    rw [← phaseFormMatrix_mulVec U w i]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, w]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  change _ = U w w
  conv_rhs => arg 1; rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, EuclideanSpace.basisFun_repr, w]

omit [DecidableEq ι] in
lemma complexPhaseMatrix_re (U D : RealForm (EuclideanSpace ℝ ι)) :
    (complexPhaseMatrix U D).map Complex.re = phaseFormMatrix U := by
  ext i j
  simp [complexPhaseMatrix]

omit [DecidableEq ι] in
lemma complexPhaseMatrix_transpose (U D : RealForm (EuclideanSpace ℝ ι))
    (hU : U.IsSymm) (hD : D.IsSymm) :
    (complexPhaseMatrix U D)ᵀ = complexPhaseMatrix U D := by
  ext i j
  simp only [Matrix.transpose_apply, complexPhaseMatrix, phaseFormMatrix,
    hU.eq (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i),
    hD.eq (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)]

omit [DecidableEq ι] in
lemma complexPhaseMatrix_annihilates {H : RealForm (EuclideanSpace ℝ ι)}
    {a b : EuclideanSpace ℝ ι} (Q : AdmissiblePhaseHessian H a b) :
    complexPhaseMatrix Q.realPart Q.imagPart *ᵥ complexPhaseVector a b = 0 := by
  ext i
  apply Complex.ext
  · simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Complex.zero_re,
      Complex.re_sum, complexPhaseMatrix, complexPhaseVector,
      Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, mul_zero, add_zero, zero_add, sub_zero,
      Complex.mul_im, Finset.sum_sub_distrib]
    change (phaseFormMatrix Q.realPart *ᵥ (fun j => a j)) i -
      (phaseFormMatrix Q.imagPart *ᵥ (fun j => b j)) i = 0
    rw [phaseFormMatrix_mulVec, phaseFormMatrix_mulVec]
    rw [Q.real_symm.eq, Q.imag_symm.eq, Q.column_b, sub_self]
  · simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Complex.zero_im,
      Complex.im_sum, complexPhaseMatrix, complexPhaseVector,
      Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, mul_zero, add_zero, zero_add, sub_zero,
      Complex.mul_im, Finset.sum_add_distrib]
    change (phaseFormMatrix Q.realPart *ᵥ (fun j => b j)) i +
      (phaseFormMatrix Q.imagPart *ᵥ (fun j => a j)) i = 0
    rw [phaseFormMatrix_mulVec, phaseFormMatrix_mulVec]
    rw [Q.real_symm.eq, Q.imag_symm.eq, Q.column_a, add_neg_cancel]

omit [DecidableEq ι] in
lemma complexPhaseVector_square (a b : EuclideanSpace ℝ ι)
    (hab : inner ℝ a b = 0) (hs : inner ℝ b b = 1 + inner ℝ a a) :
    complexPhaseVector a b ⬝ᵥ complexPhaseVector a b = -1 := by
  have ha : (∑ i, a i * a i) = inner ℝ a a := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  have hb : (∑ i, b i * b i) = inner ℝ b b := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  have hab' : (∑ i, a i * b i) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hab
  apply Complex.ext
  · simp only [dotProduct, complexPhaseVector, Complex.re_sum, Complex.mul_re,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      sub_zero, Complex.mul_im, Complex.neg_re, Complex.one_re,
      Finset.sum_sub_distrib, ha, hb]
    linarith
  · simp only [dotProduct, complexPhaseVector, Complex.im_sum, Complex.mul_re,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      sub_zero, Complex.mul_im, Complex.neg_im, Complex.one_im,
      Finset.sum_add_distrib, mul_comm, hab']
    norm_num

omit [DecidableEq ι] in
theorem actual_complex_phase_matrix (H : RealForm (EuclideanSpace ℝ ι))
    (hH : H.IsSymm) (a b : EuclideanSpace ℝ ι)
    (hab : inner ℝ a b = 0) (hs : inner ℝ b b = 1 + inner ℝ a a)
    (hstrict : 0 < H a a + H b b) :
    ∃ Q : Matrix ι ι ℂ, Qᵀ = Q ∧ Q *ᵥ complexPhaseVector a b = 0 ∧
      ∃ κ > 0, ∀ v, κ * squareSum v ≤
        realQuadratic (phaseFormMatrix H - Q.map Complex.re) v := by
  obtain ⟨Q⟩ := phase_hessian_exists H hH a b hab hs hstrict
  refine ⟨complexPhaseMatrix Q.realPart Q.imagPart,
    complexPhaseMatrix_transpose _ _ Q.real_symm Q.imag_symm,
    complexPhaseMatrix_annihilates Q, ?_⟩
  apply strict_real_quadratic_coercive
  intro v hv
  rw [complexPhaseMatrix_re]
  have heq : phaseFormMatrix H - phaseFormMatrix Q.realPart =
      phaseFormMatrix (H - Q.realPart) := by ext i j; rfl
  rw [heq, realQuadratic_phaseFormMatrix]
  change 0 < H (WithLp.toLp 2 v) (WithLp.toLp 2 v) -
    Q.realPart (WithLp.toLp 2 v) (WithLp.toLp 2 v)
  apply sub_pos.mpr
  apply Q.gap
  intro he
  apply hv
  ext i
  have hi := congrArg (fun w : EuclideanSpace ℝ ι => w i) he
  exact hi




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousRealQuadraticCoerciveNear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples
section LocalContinuationAt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma continuousAt_real_quadratic_coercive_near {T : Type*} [TopologicalSpace T]
    (A : T → Matrix ι ι ℝ) (t : T) (hA : ContinuousAt A t)
    (μ : ℝ) (hμ : 0 < μ)
    (hb : ∀ v, μ * squareSum v ≤ realQuadratic (A t) v) :
    ∀ᶠ s in 𝓝 t, ∀ v, (μ / 2) * squareSum v ≤ realQuadratic (A s) v := by
  let variation : T → ℝ := fun s => ∑ i, ∑ j, |A t i j - A s i j|
  have hc : ContinuousAt variation t := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (continuousAt_const.sub ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hA))).abs
  have hzero : variation t = 0 := by simp [variation]
  have he : ∀ᶠ s in 𝓝 t, variation s < μ / 2 :=
    hc.tendsto.eventually_lt_const (by rw [hzero]; positivity)
  filter_upwards [he] with s hs v
  have hab := realQuadratic_abs_bound ((fun i j => A t i j) - (fun i j => A s i j)) v
  rw [realQuadratic_sub] at hab
  change |realQuadratic (A t) v - realQuadratic (A s) v| ≤
    variation s * squareSum v at hab
  have hh := (le_abs_self (realQuadratic (A t) v - realQuadratic (A s) v)).trans hab
  have hv := mul_le_mul_of_nonneg_right hs.le (squareSum_nonneg v)
  linarith [hb v]

theorem phase_matrix_continuation_at {T : Type*} [TopologicalSpace T]
    (H : T → Matrix ι ι ℝ) (z : T → ι → ℂ) (t : T)
    (hH : ContinuousAt H t) (hz : ContinuousAt z t)
    (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q) (hQz : Q *ᵥ z t = 0)
    (hgap : ∀ v : ι → ℝ, v ≠ 0 →
      0 < realQuadratic (H t - Q.map Complex.re) v) :
    ∃ κ > 0, ∃ C > 0, ∀ᶠ s in 𝓝 t,
      (continuedPhaseMatrix Q (z s))ᵀ = continuedPhaseMatrix Q (z s) ∧
      (z s ⬝ᵥ z s = -1 → continuedPhaseMatrix Q (z s) *ᵥ z s = 0) ∧
      ‖continuedPhaseMatrix Q (z s)‖ ≤ C ∧
      ∀ v, 4 * κ * squareSum v ≤
        realQuadratic (H s - (continuedPhaseMatrix Q (z s)).map Complex.re) v := by
  let A : T → Matrix ι ι ℝ := fun s =>
    H s - (continuedPhaseMatrix Q (z s)).map Complex.re
  have hA : ContinuousAt A t := by
    apply hH.sub
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact Complex.continuous_re.continuousAt.comp
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp
        ((continuous_continuedPhaseMatrix Q).continuousAt.comp hz)))
  have hAt : A t = H t - Q.map Complex.re := by
    dsimp only [A]
    rw [continuedPhaseMatrix_eq Q hQ _ hQz]
  obtain ⟨μ, hμ, hb⟩ := strict_real_quadratic_coercive _ hgap
  have hlower := continuousAt_real_quadratic_coercive_near A t hA μ hμ (by
    rw [hAt]; exact hb)
  have hcont := ((continuous_continuedPhaseMatrix Q).continuousAt.comp hz).norm
  have hbound : ∀ᶠ s in 𝓝 t, ‖continuedPhaseMatrix Q (z s)‖ < ‖Q‖ + 1 :=
    hcont.tendsto.eventually_lt_const (by
      dsimp only [Function.comp_def]
      rw [continuedPhaseMatrix_eq Q hQ _ hQz]; linarith)
  refine ⟨μ / 8, by positivity, ‖Q‖ + 1, by positivity, ?_⟩
  filter_upwards [hlower, hbound] with s hs hB
  refine ⟨continuedPhaseMatrix_transpose Q hQ _,
    continuedPhaseMatrix_annihilates Q _, hB.le, ?_⟩
  intro v
  convert hs v using 1
  all_goals try with_reducible_and_instances rfl
  ring
end LocalContinuationAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma transverseProjection_eq {ν b : E} (hb : inner ℝ ν b = 0) :
    transverseProjection ν b = b := by simp [transverseProjection, hb]

lemma transverseProjection_orthogonal {ν : E} (hν : ‖ν‖ = 1) (b : E) :
    inner ℝ ν (transverseProjection ν b) = 0 := by
  have hn : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  simp [transverseProjection, inner_sub_right, inner_smul_right, hν]

lemma normalizedTransverse_eq {a ν b : E} (hb : inner ℝ ν b = 0)
    (hn : ‖b‖^2 = 1 + ‖a‖^2) : normalizedTransverse a ν b = b := by
  have hbn : 0 < ‖b‖ := by nlinarith [norm_nonneg b, sq_nonneg ‖a‖]
  rw [normalizedTransverse, transverseProjection_eq hb, ← hn, Real.sqrt_sq_eq_abs,
    abs_of_pos hbn, div_self hbn.ne', one_smul]

lemma normalizedTransverse_orthogonal {ν : E} (hν : ‖ν‖ = 1) (a b : E) :
    inner ℝ ν (normalizedTransverse a ν b) = 0 := by
  simp [normalizedTransverse, inner_smul_right, transverseProjection_orthogonal hν]

lemma normalizedTransverse_norm_sq (a ν b : E) (hb : transverseProjection ν b ≠ 0) :
    ‖normalizedTransverse a ν b‖^2 = 1 + ‖a‖^2 := by
  have hn := norm_pos_iff.mpr hb
  rw [normalizedTransverse, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ hn.ne', Real.sq_sqrt (by positivity)]

lemma continuousAt_normalizedTransverse {T : Type*} [TopologicalSpace T]
    (a ν : T → E) (b : E) (t : T) (ha : ContinuousAt a t) (hν : ContinuousAt ν t)
    (hb : transverseProjection (ν t) b ≠ 0) :
    ContinuousAt (fun s => normalizedTransverse (a s) (ν s) b) t := by
  have hp : ContinuousAt (fun s => transverseProjection (ν s) b) t :=
    continuous_transverseProjection.continuousAt.comp (hν.prodMk continuousAt_const)
  exact ((continuousAt_const.add (ha.norm.pow 2)).sqrt.div hp.norm
    (norm_ne_zero_iff.mpr hb)).smul hp
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealPhaseLinear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise

lemma PhaseMatrixValid.mono {H : RealForm PhaseSpace} {z : Fin 3 → ℂ}
    {κ κ' C C' : ℝ} {Q : ComplexPhaseMatrix} (h : PhaseMatrixValid H z κ C Q)
    (hk : κ' ≤ κ) (hC : C ≤ C') : PhaseMatrixValid H z κ' C' Q := by
  refine ⟨h.1, h.2.1, h.2.2.1.trans hC, fun v => ?_⟩
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num))
    (squareSum_nonneg v)).trans (h.2.2.2 v)

lemma ThreePhaseData.mono {H : RealForm PhaseSpace} {a ν : PhaseSpace}
    {δ κ κ' η η' C C' : ℝ} (h : ThreePhaseData H a ν δ κ η C)
    (hk : κ' ≤ κ) (hη : η' ≤ η) (hC : C ≤ C') :
    ThreePhaseData H a ν δ κ' η' C' := by
  obtain ⟨b, c, hb, hc, hbn, hcn, ha, ⟨Q₀, h₀⟩, ⟨Q₁, h₁⟩, ⟨Q₂, h₂⟩⟩ := h
  exact ⟨b, c, hb, hc, hbn, hcn, hη.trans ha,
    ⟨Q₀, h₀.mono hk hC⟩, ⟨Q₁, h₁.mono hk hC⟩, ⟨Q₂, h₂.mono hk hC⟩⟩

lemma squareSum_pos {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : v ≠ 0) :
    0 < squareSum v := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv (funext hn)
  have hi' : 0 < v i * v i := mul_self_pos.mpr hi
  exact hi'.trans_le (Finset.single_le_sum (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ i))

lemma complexPhaseVector_continuousAt {T : Type*} [TopologicalSpace T]
    (a b : T → PhaseSpace) (t : T) (ha : ContinuousAt a t) (hb : ContinuousAt b t) :
    ContinuousAt (fun s => complexPhaseVector (a s) (b s)) t := by
  apply continuousAt_pi.mpr
  intro i
  apply ContinuousAt.add
  · exact Complex.continuous_ofReal.continuousAt.comp
      ((EuclideanSpace.proj i).continuous.continuousAt.comp ha)
  · exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      ((EuclideanSpace.proj i).continuous.continuousAt.comp hb))

lemma aligned_phase_square {a ν b : PhaseSpace} (hνb : inner ℝ ν b = 0)
    (ha : a = ‖a‖ • ν) (hb : ‖b‖^2 = 1 + ‖a‖^2) :
    complexPhaseVector a b ⬝ᵥ complexPhaseVector a b = -1 := by
  apply complexPhaseVector_square
  · rw [ha, inner_smul_left, conj_trivial, hνb, mul_zero]
  · simpa only [real_inner_self_eq_norm_sq] using hb

lemma shiftedPhaseImag_eq_normalized (a ν b : PhaseSpace) (δ : ℝ) :
    shiftedPhaseImag a ν (normalizedTransverse a ν b) δ =
      normalizedTransverse (a + δ • ν) ν b := by
  have hp : Real.sqrt (1 + ‖a‖^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  dsimp [shiftedPhaseImag, normalizedTransverse]
  rw [smul_smul]
  congr 1
  field_simp

lemma shifted_phase_square {a ν b : PhaseSpace} (hνb : inner ℝ ν b = 0)
    (ha : a = ‖a‖ • ν) (hb : ‖b‖^2 = 1 + ‖a‖^2) (δ : ℝ) :
    complexPhaseVector (a + δ • ν) (shiftedPhaseImag a ν b δ) ⬝ᵥ
      complexPhaseVector (a + δ • ν) (shiftedPhaseImag a ν b δ) = -1 := by
  apply complexPhaseVector_square
  · simp only [shiftedPhaseImag, inner_smul_right, inner_add_left,
      inner_smul_left, conj_trivial, hνb, mul_zero, add_zero]
    rw [ha, inner_smul_left, conj_trivial, hνb, mul_zero, mul_zero]
  · simp only [real_inner_self_eq_norm_sq, shiftedPhaseImag, norm_smul,
      Real.norm_eq_abs, sq_abs, mul_pow, div_pow, hb]
    rw [Real.sq_sqrt (show 0 ≤ 1 + ‖a + δ • ν‖^2 by positivity),
      Real.sq_sqrt (show 0 ≤ 1 + ‖a‖^2 by positivity)]
    have hn : (1 : ℝ) + ‖a‖^2 ≠ 0 := by positivity
    field_simp


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_CompactProfileThreePhaseData
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise
variable {T : Type*} [TopologicalSpace T]

theorem local_three_phase_data
    (H : T → RealForm PhaseSpace) (a ν : T → PhaseSpace)
    (hH : Continuous (fun s => phaseFormMatrix (H s)))
    (ha : Continuous a) (hν : Continuous ν)
    (hunit : ∀ s, ‖ν s‖ = 1) (halign : ∀ s, a s = ‖a s‖ • ν s)
    (t : T) (hsymm : (H t).IsSymm)
    (hnc : a t ≠ 0 → ∃ b, inner ℝ (a t) b = 0 ∧ ‖b‖^2 = 1 + ‖a t‖^2 ∧
      0 < H t (a t) (a t) + H t b b)
    (hcrit : a t = 0 → ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H t v v) :
    ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∀ᶠ q : T × ℝ in 𝓝 (t, 0),
      ThreePhaseData (H q.1) (a q.1) (ν q.1) q.2 κ η C := by
  obtain ⟨b, c, hνb, hνc, hbn, hcn, hbg, hcg, hbc⟩ :=
    actual_two_transverse_phases (by simp) (H t) (a t) (ν t)
      (hunit t) (halign t) hnc hcrit
  have hbnpos : 0 < ‖b‖ := by nlinarith [norm_nonneg b, sq_nonneg ‖a t‖]
  have hcnpos : 0 < ‖c‖ := by nlinarith [norm_nonneg c, sq_nonneg ‖a t‖]
  let A : T × ℝ → PhaseSpace := fun q => a q.1
  let N : T × ℝ → PhaseSpace := fun q => ν q.1
  let A' : T × ℝ → PhaseSpace := fun q => a q.1 + q.2 • ν q.1
  let B : T × ℝ → PhaseSpace := fun q => normalizedTransverse (A q) (N q) b
  let D : T × ℝ → PhaseSpace := fun q => normalizedTransverse (A q) (N q) c
  let B' : T × ℝ → PhaseSpace := fun q => normalizedTransverse (A' q) (N q) b
  have hA : Continuous A := ha.comp continuous_fst
  have hN : Continuous N := hν.comp continuous_fst
  have hA' : Continuous A' := hA.add (continuous_snd.smul hN)
  have hbproj : transverseProjection (ν t) b ≠ 0 := by
    rw [transverseProjection_eq hνb]; exact norm_ne_zero_iff.mp hbnpos.ne'
  have hcproj : transverseProjection (ν t) c ≠ 0 := by
    rw [transverseProjection_eq hνc]; exact norm_ne_zero_iff.mp hcnpos.ne'
  have hB : ContinuousAt B (t, 0) := continuousAt_normalizedTransverse A N b (t, 0)
    hA.continuousAt hN.continuousAt hbproj
  have hD : ContinuousAt D (t, 0) := continuousAt_normalizedTransverse A N c (t, 0)
    hA.continuousAt hN.continuousAt hcproj
  have hB' : ContinuousAt B' (t, 0) := continuousAt_normalizedTransverse A' N b (t, 0)
    hA'.continuousAt hN.continuousAt hbproj
  have hB0 : B (t, 0) = b := normalizedTransverse_eq hνb hbn
  have hD0 : D (t, 0) = c := normalizedTransverse_eq hνc hcn
  have hA0 : A' (t, 0) = a t := by simp [A']
  have hB'0 : B' (t, 0) = b := by
    change normalizedTransverse (A' (t, 0)) (ν t) b = b
    rw [hA0]; exact hB0
  have hab : inner ℝ (a t) b = 0 := by
    rw [halign t, inner_smul_left, conj_trivial, hνb, mul_zero]
  have hac : inner ℝ (a t) c = 0 := by
    rw [halign t, inner_smul_left, conj_trivial, hνc, mul_zero]
  obtain ⟨Q₀, hs₀, hz₀, μ₀, hμ₀, hg₀⟩ := actual_complex_phase_matrix
    (H t) hsymm (a t) b hab (by simpa only [real_inner_self_eq_norm_sq] using hbn) hbg
  obtain ⟨Q₁, hs₁, hz₁, μ₁, hμ₁, hg₁⟩ := actual_complex_phase_matrix
    (H t) hsymm (a t) c hac (by simpa only [real_inner_self_eq_norm_sq] using hcn) hcg
  have hgap₀ : ∀ v : Fin 3 → ℝ, v ≠ 0 →
      0 < realQuadratic (phaseFormMatrix (H t) - Q₀.map Complex.re) v :=
    fun v hv => (mul_pos hμ₀ (squareSum_pos v hv)).trans_le (hg₀ v)
  have hgap₁ : ∀ v : Fin 3 → ℝ, v ≠ 0 →
      0 < realQuadratic (phaseFormMatrix (H t) - Q₁.map Complex.re) v :=
    fun v hv => (mul_pos hμ₁ (squareSum_pos v hv)).trans_le (hg₁ v)
  let HM : T × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun q => phaseFormMatrix (H q.1)
  let Z₀ := fun q => complexPhaseVector (A q) (B q)
  let Z₁ := fun q => complexPhaseVector (A q) (D q)
  let Z₂ := fun q => complexPhaseVector (A' q) (B' q)
  have hHM : ContinuousAt HM (t, 0) := (hH.comp continuous_fst).continuousAt
  obtain ⟨κ₀, hk₀, C₀, hC₀, he₀⟩ := phase_matrix_continuation_at HM Z₀ (t, 0) hHM
    (complexPhaseVector_continuousAt A B _ hA.continuousAt hB) Q₀ hs₀
      (by simpa only [Z₀, hB0, A] using hz₀) hgap₀
  obtain ⟨κ₁, hk₁, C₁, hC₁, he₁⟩ := phase_matrix_continuation_at HM Z₁ (t, 0) hHM
    (complexPhaseVector_continuousAt A D _ hA.continuousAt hD) Q₁ hs₁
      (by simpa only [Z₁, hD0, A] using hz₁) hgap₁
  obtain ⟨κ₂, hk₂, C₂, hC₂, he₂⟩ := phase_matrix_continuation_at HM Z₂ (t, 0) hHM
    (complexPhaseVector_continuousAt A' B' _ hA'.continuousAt hB') Q₀ hs₀
      (by simpa only [Z₂, hA0, hB'0] using hz₀) hgap₀
  have hden : 0 < ‖b‖^2 * ‖c‖^2 := mul_pos (pow_pos hbnpos _) (pow_pos hcnpos _)
  have hang : 0 < transverseAngleSq b c := div_pos hbc hden
  have hangle : ContinuousAt (fun q => transverseAngleSq (B q) (D q)) (t, 0) := by
    apply ((hB.norm.pow 2).mul (hD.norm.pow 2)).sub ((hB.inner hD).pow 2) |>.div
      ((hB.norm.pow 2).mul (hD.norm.pow 2))
    change ‖B (t, 0)‖^2 * ‖D (t, 0)‖^2 ≠ 0
    rw [hB0, hD0]
    exact hden.ne'
  have hea : ∀ᶠ q in 𝓝 (t, 0), transverseAngleSq b c / 2 <
      transverseAngleSq (B q) (D q) := hangle.tendsto.eventually_const_lt (by
        rw [hB0, hD0]; linarith)
  have hep (v : PhaseSpace) (hv : transverseProjection (ν t) v ≠ 0) :
      ∀ᶠ q : T × ℝ in 𝓝 (t, 0), transverseProjection (N q) v ≠ 0 := by
    have hh : Continuous (fun q : T × ℝ => transverseProjection (N q) v) :=
      continuous_transverseProjection.comp (hN.prodMk continuous_const)
    have h := (hh.norm.tendsto (t, 0)).eventually_const_lt (norm_pos_iff.mpr hv)
    filter_upwards [h] with q hq using norm_pos_iff.mp hq
  refine ⟨min κ₀ (min κ₁ κ₂), lt_min hk₀ (lt_min hk₁ hk₂),
    transverseAngleSq b c / 2, by positivity, C₀ + C₁ + C₂, by positivity, ?_⟩
  filter_upwards [he₀, he₁, he₂, hea, hep b hbproj, hep c hcproj] with q h₀ h₁ h₂ hangle hbq hcq
  have hBq := normalizedTransverse_orthogonal (hunit q.1) (a q.1) b
  have hDq := normalizedTransverse_orthogonal (hunit q.1) (a q.1) c
  have hBqn := normalizedTransverse_norm_sq (a q.1) (ν q.1) b hbq
  have hDqn := normalizedTransverse_norm_sq (a q.1) (ν q.1) c hcq
  have hZ₀ := aligned_phase_square hBq (halign q.1) hBqn
  have hZ₁ := aligned_phase_square hDq (halign q.1) hDqn
  have hshift : shiftedPhaseImag (a q.1) (ν q.1) (B q) q.2 = B' q :=
    shiftedPhaseImag_eq_normalized (a q.1) (ν q.1) b q.2
  have hZ₂ := shifted_phase_square hBq (halign q.1) hBqn q.2
  rw [hshift] at hZ₂
  refine ⟨B q, D q, hBq, hDq, hBqn, hDqn, hangle.le, ?_, ?_, ?_⟩
  · refine ⟨continuedPhaseMatrix Q₀ (Z₀ q), ?_⟩
    exact (show PhaseMatrixValid (H q.1) (Z₀ q) κ₀ C₀ _ from
      ⟨h₀.1, h₀.2.1 hZ₀, h₀.2.2.1, h₀.2.2.2⟩).mono
      (min_le_left _ _) (by linarith)
  · refine ⟨continuedPhaseMatrix Q₁ (Z₁ q), ?_⟩
    exact (show PhaseMatrixValid (H q.1) (Z₁ q) κ₁ C₁ _ from
      ⟨h₁.1, h₁.2.1 hZ₁, h₁.2.2.1, h₁.2.2.2⟩).mono
      ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  · rw [hshift]
    refine ⟨continuedPhaseMatrix Q₀ (Z₂ q), ?_⟩
    exact (show PhaseMatrixValid (H q.1) (Z₂ q) κ₂ C₂ _ from
      ⟨h₂.1, h₂.2.1 hZ₂, h₂.2.2.1, h₂.2.2.2⟩).mono
      ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise

lemma finite_positive_common_lower {I : Type*} (s : Finset I) (c : I → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) : ∃ d > 0, ∀ i ∈ s, d ≤ c i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨d, hd, hds⟩ := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    refine ⟨min (c i) d, lt_min (hc i (Finset.mem_insert_self _ _)) hd, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hds j hj)

theorem uniform_three_phase_data {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (H : T → RealForm PhaseSpace) (a ν : T → PhaseSpace)
    (hH : Continuous (fun s => phaseFormMatrix (H s)))
    (ha : Continuous a) (hν : Continuous ν)
    (hunit : ∀ s, ‖ν s‖ = 1) (halign : ∀ s, a s = ‖a s‖ • ν s)
    (hsymm : ∀ t, (H t).IsSymm)
    (hnc : ∀ t, a t ≠ 0 → ∃ b, inner ℝ (a t) b = 0 ∧ ‖b‖^2 = 1 + ‖a t‖^2 ∧
      0 < H t (a t) (a t) + H t b b)
    (hcrit : ∀ t, a t = 0 → ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H t v v) :
    ∃ δ₀ > 0, ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∀ t, ∀ δ ∈ Icc 0 δ₀,
      ThreePhaseData (H t) (a t) (ν t) δ κ η C := by
  classical
  have hlocal : ∀ t : T, ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∃ U : Set T,
      IsOpen U ∧ t ∈ U ∧ ∃ ε > 0, ∀ s ∈ U, ∀ δ ∈ Icc 0 ε,
        ThreePhaseData (H s) (a s) (ν s) δ κ η C := by
    intro t
    obtain ⟨κ, hk, η, hη, C, hC, he⟩ := local_three_phase_data H a ν hH ha hν
      hunit halign t (hsymm t) (hnc t) (hcrit t)
    rw [nhds_prod_eq] at he
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp he
    obtain ⟨W, hWU, hW, htW⟩ := mem_nhds_iff.mp hU
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨κ, hk, η, hη, C, hC, W, hW, htW, r / 2, by positivity, ?_⟩
    intro s hs δ hδ
    refine hUV (show (s, δ) ∈ U ×ˢ V from ?_)
    refine ⟨hWU hs, hrV ?_⟩
    change dist δ 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ.1]
    linarith [hδ.2]
  choose κ hk η hη C hC U hU htU ε hε hlocal using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (by intro t _; exact mem_iUnion_of_mem t (htU t))
  obtain ⟨δ₀, hδ₀, hδε⟩ := finite_positive_common_lower s ε (fun t _ => hε t)
  obtain ⟨κ₀, hk₀, hκ⟩ := finite_positive_common_lower s κ (fun t _ => hk t)
  obtain ⟨η₀, hη₀, hηη⟩ := finite_positive_common_lower s η (fun t _ => hη t)
  let C₀ : ℝ := 1 + ∑ t ∈ s, C t
  have hC₀ : 0 < C₀ := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun t _ => (hC t).le)
  refine ⟨δ₀, hδ₀, κ₀, hk₀, η₀, hη₀, C₀, hC₀, ?_⟩
  intro t δ hδ
  obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp (hs (mem_univ t))
  have hci : C i ≤ C₀ := by
    have hh := Finset.single_le_sum (fun j _ => (hC j).le) hi
    dsimp [C₀]
    linarith
  exact (hlocal i t hti δ ⟨hδ.1, hδ.2.trans (hδε i hi)⟩).mono
    (hκ i hi) (hηη i hi) hci

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise

theorem compact_profile_three_phase_data_oai {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : X → RealForm PhaseSpace) (a : X → PhaseSpace)
    (hH : Continuous (fun x => phaseFormMatrix (H x))) (ha : Continuous a)
    (hsymm : ∀ x, (H x).IsSymm)
    (hnc : ∀ x, a x ≠ 0 → ∃ b, inner ℝ (a x) b = 0 ∧ ‖b‖^2 = 1 + ‖a x‖^2 ∧
      0 < H x (a x) (a x) + H x b b)
    (hcrit : ∀ x, a x = 0 → ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H x v v) :
    ∃ δ₀ > 0, ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∀ x ν,
      ‖ν‖ = 1 → a x = ‖a x‖ • ν → ∀ δ ∈ Icc 0 δ₀,
        ThreePhaseData (H x) (a x) ν δ κ η C := by
  let K : Set (X × PhaseSpace) := {p | ‖p.2‖ = 1 ∧ a p.1 = ‖a p.1‖ • p.2}
  have hcompact : IsCompact K := by
    have heq : K = (univ ×ˢ Metric.sphere (0 : PhaseSpace) 1) ∩
        {p | a p.1 = ‖a p.1‖ • p.2} := by
      ext p
      simp [K]
    rw [heq]
    exact (isCompact_univ.prod (isCompact_sphere 0 1)).inter_right
      (isClosed_eq (ha.comp continuous_fst)
        ((ha.comp continuous_fst).norm.smul continuous_snd))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let partition : K → X := fun p => p.val.1
  let ν : K → PhaseSpace := fun p => p.val.2
  have hπ : Continuous partition := continuous_fst.comp continuous_subtype_val
  obtain ⟨δ₀, hδ₀, κ, hk, η, hη, C, hC, h⟩ := uniform_three_phase_data
    (fun p => H (partition p)) (fun p => a (partition p)) ν
    (hH.comp hπ) (ha.comp hπ) (continuous_snd.comp continuous_subtype_val)
    (fun p => p.property.1) (fun p => p.property.2)
    (fun p => hsymm (partition p)) (fun p => hnc (partition p)) (fun p => hcrit (partition p))
  refine ⟨δ₀, hδ₀, κ, hk, η, hη, C, hC, ?_⟩
  intro x v hv hav δ hδ
  exact h ⟨(x, v), hv, hav⟩ δ hδ



end YauCounterexamples
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.compact_profile_three_phase_data_oai.{u_1} := @OAI.YauCounterexamples.compact_profile_three_phase_data_oai.{u_1}
