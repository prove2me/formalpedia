-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.example_2_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:47:37.127244+00:00
-- url     : https://prove2.me/submissions/2498ed90-8411-4c43-8674-b48dcea06cc9

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]


end QAlgorithms.Papers.Independent.Support50.P12

attribute [local instance] Classical.propDecidable Classical.decEq

namespace A3S55EX
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms (spectralProjector)
open scoped Matrix ComplexConjugate ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

theorem specProj_eq (A M : Mat I) (a : ℝ) (hM : Mᴴ = M) (hMM : M * M = M)
    (hAM : A * M = (a : ℂ) • M) (c : ℂ) (hc : 1 - M = c • (A - (a : ℂ) • 1)) :
    spectralProjector A a = M := by
  unfold spectralProjector QAlgorithms.eigenProjection
  rw [LinearEquiv.symm_apply_eq]
  apply LinearMap.ext
  intro u
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, ContinuousLinearMap.coe_coe]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Module.End.mem_eigenspace_iff]
    simp only [ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hAM, Matrix.smul_mulVec]
  · intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw
    simp only [ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at hw
    simp only [Matrix.toEuclideanLin_apply] at hw ⊢
    have hw' : M *ᵥ w.ofLp = w.ofLp := by
      have h1 : (1 - M) *ᵥ w.ofLp = 0 := by
        rw [hc, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        have := congrArg WithLp.ofLp hw
        simp only [WithLp.ofLp_toLp] at this
        rw [this]; simp
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
      exact h1.symm
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rw [← hw']
    rw [dotProduct_comm, Matrix.dotProduct_mulVec]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_toLp, star_sub, Matrix.star_mulVec, hM, Matrix.sub_vecMul,
      Matrix.vecMul_vecMul, hMM, sub_self, zero_dotProduct]

def two (b1 b2 : ℝ) (Q : Mat I) : Mat I := (b1 : ℂ) • Q + (b2 : ℂ) • (1 - Q)

section
variable {Q : Mat I} (hQQ : Q * Q = Q)
include hQQ

theorem two_mul_Q (b1 b2 : ℝ) : two b1 b2 Q * Q = (b1 : ℂ) • Q := by
  simp [two, add_mul, sub_mul, hQQ, smul_mul_assoc]
theorem Q_mul_two (b1 b2 : ℝ) : Q * two b1 b2 Q = (b1 : ℂ) • Q := by
  simp [two, mul_add, mul_sub, hQQ, mul_smul_comm]
theorem two_mul_Qc (b1 b2 : ℝ) : two b1 b2 Q * (1 - Q) = (b2 : ℂ) • (1 - Q) := by
  simp [two, add_mul, sub_mul, mul_sub, hQQ, smul_mul_assoc]
theorem Qc_mul_two (b1 b2 : ℝ) : (1 - Q) * two b1 b2 Q = (b2 : ℂ) • (1 - Q) := by
  simp [two, mul_add, mul_sub, sub_mul, hQQ, mul_smul_comm]

omit hQQ in
theorem two_herm (hQ : Qᴴ = Q) (b1 b2 : ℝ) : (two b1 b2 Q)ᴴ = two b1 b2 Q := by
  simp [two, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hQ]

theorem spectrum_two_sub (b1 b2 : ℝ) : spectrum ℝ (two b1 b2 Q) ⊆ {b1, b2} := by
  intro a ha
  by_contra hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  apply ha
  refine IsUnit.of_mul_eq_one (((a - b1)⁻¹ : ℝ) • Q + ((a - b2)⁻¹ : ℝ) • (1 - Q)) ?_
  have h1 : (a - b1 : ℝ) ≠ 0 := sub_ne_zero.mpr hne.1
  have h2 : (a - b2 : ℝ) ≠ 0 := sub_ne_zero.mpr hne.2
  rw [Algebra.algebraMap_eq_smul_one]
  have e : a • (1 : Mat I) - two b1 b2 Q = ((a - b1 : ℝ) : ℂ) • Q + ((a - b2 : ℝ) : ℂ) • (1 - Q) := by
    simp only [two]; ext i j; simp [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
  rw [e]
  have hc : ∀ (r : ℝ) (M : Mat I), r • M = (r : ℂ) • M := fun r M => by ext; simp
  rw [hc, hc]
  simp only [add_mul, mul_add, smul_mul_smul, mul_sub, sub_mul, hQQ, one_mul, mul_one, sub_self,
    smul_zero, add_zero, zero_add]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]
  simp

theorem spectrum_two (hQ0 : Q ≠ 0) (hQ1 : 1 - Q ≠ 0) (b1 b2 : ℝ) :
    spectrum ℝ (two b1 b2 Q) = {b1, b2} := by
  apply (spectrum_two_sub hQQ b1 b2).antisymm
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  intro hu
  rcases ha with rfl | rfl
  · apply hQ0
    have : (a • (1 : Mat I) - two a b2 Q) * Q = 0 := by
      rw [sub_mul, two_mul_Q hQQ]; ext; simp
    exact (hu.mul_right_eq_zero).mp this
  · apply hQ1
    have : (a • (1 : Mat I) - two b1 a Q) * (1 - Q) = 0 := by
      rw [sub_mul, two_mul_Qc hQQ]; ext; simp
    exact (hu.mul_right_eq_zero).mp this

theorem spec_two (hQ : Qᴴ = Q) (hQ0 : Q ≠ 0) (hQ1 : 1 - Q ≠ 0) (b1 b2 : ℝ) :
    QAlgorithms.Papers.Independent.Support50.P12.spec (two b1 b2 Q) = {b1, b2} := by
  have hH : (two b1 b2 Q).IsHermitian := two_herm hQ b1 b2
  unfold QAlgorithms.Papers.Independent.Support50.P12.spec
  rw [dif_pos hH]
  ext a
  have := spectrum_two hQQ hQ0 hQ1 b1 b2
  rw [hH.spectrum_real_eq_range_eigenvalues] at this
  have h2 := congrArg (a ∈ ·) this
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at h2
  simp [h2]

theorem cfc_two (hQ : Qᴴ = Q) (b1 b2 : ℝ) (hb : b1 ≠ b2) (g : ℝ → ℝ) :
    cfc g (two b1 b2 Q) = two (g b1) (g b2) Q := by
  have hH : IsSelfAdjoint (two b1 b2 Q) := two_herm hQ b1 b2
  set β := (g b2 - g b1) / (b2 - b1)
  set α := g b1 - β * b1
  have hb' : b2 - b1 ≠ 0 := sub_ne_zero.mpr hb.symm
  have h1 : α + β * b1 = g b1 := by simp [α]
  have h2 : α + β * b2 = g b2 := by
    simp only [α, β]; field_simp; ring
  rw [cfc_congr (g := fun x => α + β * x)]
  · rw [cfc_add (a := two b1 b2 Q) (fun _ => α) (fun x => β * x), cfc_const α (two b1 b2 Q), cfc_const_mul β (fun x => x) (two b1 b2 Q), cfc_id' ℝ (two b1 b2 Q)]
    rw [← h1, ← h2, Algebra.algebraMap_eq_smul_one]
    simp only [two]; ext i j
    simp [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
  · intro x hx
    rcases spectrum_two_sub hQQ b1 b2 hx with rfl | h
    · exact h1.symm
    · rw [Set.mem_singleton_iff] at h; subst h; exact h2.symm

theorem specProj_two1 (hQ : Qᴴ = Q) (b1 b2 : ℝ) (hb : b1 ≠ b2) :
    spectralProjector (two b1 b2 Q) b1 = Q := by
  have hb' : ((b2 : ℂ) - b1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hb.symm
  apply specProj_eq _ _ _ hQ hQQ (two_mul_Q hQQ b1 b2) ((b2 - b1 : ℂ)⁻¹)
  have e : two b1 b2 Q - (b1 : ℂ) • 1 = ((b2 : ℂ) - b1) • (1 - Q) := by
    simp only [two]; ext i j; simp [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
  rw [e, smul_smul, inv_mul_cancel₀ hb', one_smul]

theorem specProj_two2 (hQ : Qᴴ = Q) (b1 b2 : ℝ) (hb : b1 ≠ b2) :
    spectralProjector (two b1 b2 Q) b2 = 1 - Q := by
  have hb' : ((b1 : ℂ) - b2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hb
  have hQc : (1 - Q) * (1 - Q) = 1 - Q := by simp [mul_sub, sub_mul, hQQ]
  apply specProj_eq _ _ _ (by simp [Matrix.conjTranspose_sub, hQ]) hQc (two_mul_Qc hQQ b1 b2)
    ((b1 - b2 : ℂ)⁻¹)
  have e : two b1 b2 Q - (b2 : ℂ) • 1 = ((b1 : ℂ) - b2) • (1 - (1 - Q)) := by
    simp only [two]; ext i j; simp [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
  rw [e, smul_smul, inv_mul_cancel₀ hb', one_smul, sub_sub_cancel]
end

theorem hs_eq (A B : Mat I) : QAlgorithms.Papers.Independent.Frontier18.P17.hs A B = (Aᴴ * B).trace := by
  unfold QAlgorithms.Papers.Independent.Frontier18.P17.hs QAlgorithms.Papers.Independent.Frontier18.P17.res
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diag,
    Matrix.conjTranspose_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  simp [mul_comm]

def gh (x : ℝ) : ℝ := if x = 0 then 0 else Real.rpow x (1 / 2)

theorem sp_two {Q : Mat I} (hQQ : Q * Q = Q) (hQ : Qᴴ = Q) (b1 b2 : ℝ) (hb : b1 ≠ b2) :
    QAlgorithms.Papers.Independent.Information100.P71.supportPower (two b1 b2 Q) (1 / 2) =
      two (gh b1) (gh b2) Q := by
  unfold QAlgorithms.Papers.Independent.Information100.P71.supportPower
  exact cfc_two hQQ hQ b1 b2 hb _

theorem quasi_two (f : ℝ → ℝ) {P Q : Mat I} (hPP : P * P = P) (hP : Pᴴ = P) (hP0 : P ≠ 0)
    (hP1 : 1 - P ≠ 0) (hQQ : Q * Q = Q) (hQ : Qᴴ = Q) (hQ0 : Q ≠ 0) (hQ1 : 1 - Q ≠ 0)
    (a1 a2 b1 b2 : ℝ) (ha : a1 ≠ a2) (hb : b1 ≠ b2) :
    QAlgorithms.Papers.Independent.Support50.P12.quasi f (two a1 a2 P) (two b1 b2 Q) =
      f (a1 / b1) * (gh b1 * gh b1) * (Q * P).trace.re
      + f (a1 / b2) * (gh b2 * gh b2) * ((1 - Q) * P).trace.re
      + f (a2 / b1) * (gh b1 * gh b1) * (Q * (1 - P)).trace.re
      + f (a2 / b2) * (gh b2 * gh b2) * ((1 - Q) * (1 - P)).trace.re := by
  unfold QAlgorithms.Papers.Independent.Support50.P12.quasi
    QAlgorithms.Papers.Independent.Support50.P12.modular
  rw [sp_two hQQ hQ b1 b2 hb, spec_two hPP hP hP0 hP1, spec_two hQQ hQ hQ0 hQ1,
    Finset.sum_pair ha, Finset.sum_pair hb, Finset.sum_pair hb,
    specProj_two1 hPP hP _ _ ha, specProj_two2 hPP hP _ _ ha,
    specProj_two1 hQQ hQ _ _ hb, specProj_two2 hQQ hQ _ _ hb, hs_eq, two_herm hQ]
  set S := two (gh b1) (gh b2) Q
  have t1 : ∀ X : Mat I, (S * (X * S * Q)).trace = ((gh b1 * gh b1 : ℝ) : ℂ) * (Q * X).trace := by
    intro X
    rw [Matrix.mul_assoc X, two_mul_Q hQQ, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_mul_comm, Matrix.mul_assoc, Q_mul_two hQQ, Matrix.mul_smul, Matrix.trace_smul]
    simp [smul_eq_mul, mul_assoc, Matrix.trace_mul_comm X]
  have t2 : ∀ X : Mat I, (S * (X * S * (1 - Q))).trace =
      ((gh b2 * gh b2 : ℝ) : ℂ) * ((1 - Q) * X).trace := by
    intro X
    rw [Matrix.mul_assoc X, two_mul_Qc hQQ, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_mul_comm, Matrix.mul_assoc, Qc_mul_two hQQ, Matrix.mul_smul, Matrix.trace_smul]
    simp [smul_eq_mul, mul_assoc, Matrix.trace_mul_comm X]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, t1, t2,
    smul_eq_mul, Complex.add_re]
  simp only [Complex.re_ofReal_mul]
  ring

section concrete

def P0 : Mat (Fin 2) := !![1, 0; 0, 0]
def H0 : Mat (Fin 2) := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

theorem P0_idem : P0 * P0 = P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P0, Matrix.mul_apply, Fin.sum_univ_two]
theorem H0_idem : H0 * H0 = H0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H0, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
theorem P0_herm : P0ᴴ = P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P0]
theorem H0_herm : H0ᴴ = H0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H0]
theorem P0_ne0 : P0 ≠ 0 := by
  intro h; have := congrFun (congrFun h 0) 0; simp [P0] at this
theorem P0_ne1 : 1 - P0 ≠ 0 := by
  intro h; have := congrFun (congrFun h 1) 1; simp [P0, Matrix.sub_apply] at this
theorem H0_ne0 : H0 ≠ 0 := by
  intro h; have := congrFun (congrFun h 0) 0; simp [H0] at this
theorem H0_ne1 : 1 - H0 ≠ 0 := by
  intro h; have := congrFun (congrFun h 0) 0; simp [H0, Matrix.sub_apply] at this; norm_num at this

theorem gh_sq {x : ℝ} (hx : 0 < x) : gh x * gh x = x := by
  simp only [gh, if_neg hx.ne']
  show x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x
  rw [← Real.rpow_add hx]; norm_num

theorem gh_pos {x : ℝ} (hx : 0 < x) : 0 < gh x := by
  simp only [gh, if_neg hx.ne']; exact Real.rpow_pos_of_pos hx _

theorem gh_one : gh 1 = 1 := by simp [gh]
theorem gh_zero : gh 0 = 0 := by simp [gh]

theorem two_psd {Q : Mat I} (hQQ : Q * Q = Q) (hQ : Qᴴ = Q) {b1 b2 : ℝ} (h1 : 0 ≤ b1)
    (h2 : 0 ≤ b2) : (two b1 b2 Q).PosSemidef := by
  have hq : Q.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self Q
    rwa [hQ, hQQ] at this
  have hq' : (1 - Q).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (1 - Q)
    rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.sub_mul, hQQ, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, sub_self, sub_zero] at this
  exact (hq.smul (by exact_mod_cast h1)).add (hq'.smul (by exact_mod_cast h2))

theorem two_two {Q : Mat I} (hQQ : Q * Q = Q) (a1 a2 b1 b2 : ℝ) :
    two a1 a2 Q * two b1 b2 Q = two (a1 * b1) (a2 * b2) Q := by
  have hQc : (1 - Q) * (1 - Q) = 1 - Q := by simp [mul_sub, sub_mul, hQQ]
  have h0 : Q * (1 - Q) = 0 := by simp [mul_sub, hQQ]
  have h0' : (1 - Q) * Q = 0 := by simp [sub_mul, hQQ]
  simp only [two, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hQQ, hQc, h0, h0',
    smul_zero, add_zero, zero_add, smul_smul, Complex.ofReal_mul]
  rw [mul_comm (a1 : ℂ), mul_comm (a2 : ℂ)]

theorem two_one_one (Q : Mat I) : two 1 1 Q = 1 := by simp [two]

theorem supports_two {Q : Mat I} (hQQ : Q * Q = Q) {b1 b2 : ℝ} (h1 : b1 ≠ 0) (h2 : b2 ≠ 0)
    (A : Mat I) : QAlgorithms.Papers.Independent.Next46.P23.Supports A (two b1 b2 Q) := by
  intro v hv
  have : v = 0 := by
    have e : two b1⁻¹ b2⁻¹ Q * two b1 b2 Q = 1 := by
      rw [two_two hQQ, inv_mul_cancel₀ h1, inv_mul_cancel₀ h2, two_one_one]
    calc v = (two b1⁻¹ b2⁻¹ Q * two b1 b2 Q) *ᵥ v := by rw [e, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rw [this, Matrix.mulVec_zero]

theorem rho_eq : two 1 0 P0 = P0 := by simp [two]

/-- `P0 * sigma * P0` for the three test states. -/
theorem sand (b1 b2 : ℝ) : P0 * two b1 b2 P0 * P0 = two b1 0 P0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, two, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply] <;> simp [P0, H0] <;> ring
theorem sandH (b1 b2 : ℝ) : P0 * two b1 b2 H0 * P0 = two ((b1 + b2) / 2) 0 P0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, two, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply] <;> simp [P0, H0] <;> ring

theorem tr_two (c : ℝ) : QAlgorithms.Papers.Independent.Dependency50.P28.tr (two c 0 P0) = c := by
  simp [QAlgorithms.Papers.Independent.Dependency50.P28.tr, two, P0, Matrix.trace_fin_two]

theorem tr_two' {Q : Mat (Fin 2)} (b1 b2 : ℝ) (hQ : Q = P0 ∨ Q = H0) :
    QAlgorithms.Papers.Independent.Dependency50.P28.tr (two b1 b2 Q) = (b1 + b2) / 2 + (b1 + b2) / 2 := by
  rcases hQ with rfl | rfl <;>
    simp [QAlgorithms.Papers.Independent.Dependency50.P28.tr, two, P0, H0, Matrix.trace_fin_two,
      Matrix.sub_apply] <;> ring

/-- The RHS fidelity value at `rho = P0`. -/
theorem rhs_val (X : Mat (Fin 2)) (c : ℝ) (hc : c ≠ 0) (hX : P0 * X * P0 = two c 0 P0) :
    QAlgorithms.Papers.Independent.Dependency50.P28.tr
      (QAlgorithms.Papers.Independent.Information100.P71.supportPower
        (QAlgorithms.Papers.Independent.Information100.P71.supportPower P0 (1 / 2) * X *
          QAlgorithms.Papers.Independent.Information100.P71.supportPower P0 (1 / 2)) (1 / 2)) = gh c := by
  have e : QAlgorithms.Papers.Independent.Information100.P71.supportPower P0 (1 / 2) = P0 := by
    conv_lhs => rw [← rho_eq]
    rw [sp_two P0_idem P0_herm 1 0 one_ne_zero, gh_one, gh_zero, rho_eq]
  rw [e, hX, sp_two P0_idem P0_herm c 0 hc, gh_zero, tr_two]

end concrete

theorem main_contra (f : ℝ → ℝ)
    (H : ∀ (n : ℕ), 0 < n → ∀ rho sigma : Mat (Fin n),
        QAlgorithms.Papers.Independent.Support50.P12.AlgebraDensity ⊤ rho →
        QAlgorithms.Papers.Independent.Support50.P12.AlgebraDensity ⊤ sigma →
        QAlgorithms.Papers.Independent.Support50.P12.div f rho sigma =
          (QAlgorithms.Papers.Independent.Dependency50.P28.tr
            (QAlgorithms.Papers.Independent.Information100.P71.supportPower
              (QAlgorithms.Papers.Independent.Information100.P71.supportPower rho (1 / 2) * sigma *
                QAlgorithms.Papers.Independent.Information100.P71.supportPower rho (1 / 2)) (1 / 2)) : EReal)) :
    False := by
  have dens : ∀ (Q : Mat (Fin 2)) (b1 b2 : ℝ), (Q = P0 ∨ Q = H0) → 0 ≤ b1 → 0 ≤ b2 → b1 + b2 = 1 →
      QAlgorithms.Papers.Independent.Support50.P12.AlgebraDensity ⊤ (two b1 b2 Q) := by
    intro Q b1 b2 hQ h1 h2 hs
    have hQQ : Q * Q = Q := by rcases hQ with rfl | rfl; exacts [P0_idem, H0_idem]
    have hQh : Qᴴ = Q := by rcases hQ with rfl | rfl; exacts [P0_herm, H0_herm]
    refine ⟨StarSubalgebra.mem_top, two_psd hQQ hQh h1 h2, ?_⟩
    rw [tr_two' b1 b2 hQ, hs]; norm_num
  have dP : QAlgorithms.Papers.Independent.Support50.P12.AlgebraDensity ⊤ P0 := by
    have := dens P0 1 0 (Or.inl rfl) (by norm_num) (by norm_num) (by norm_num)
    rwa [rho_eq] at this
  have key : ∀ (Q : Mat (Fin 2)) (b1 b2 c : ℝ), (Q = P0 ∨ Q = H0) → 0 < b1 → 0 < b2 → b1 + b2 = 1 →
      b1 ≠ b2 → c ≠ 0 → P0 * two b1 b2 Q * P0 = two c 0 P0 →
      QAlgorithms.Papers.Independent.Support50.P12.quasi f (two 1 0 P0) (two b1 b2 Q) = gh c := by
    intro Q b1 b2 c hQ h1 h2 hs hne hc hX
    rw [rho_eq]
    have h := H 2 (by norm_num) P0 (two b1 b2 Q) dP (dens Q b1 b2 hQ h1.le h2.le hs)
    have hQQ : Q * Q = Q := by rcases hQ with rfl | rfl; exacts [P0_idem, H0_idem]
    unfold QAlgorithms.Papers.Independent.Support50.P12.div at h
    rw [if_pos (supports_two hQQ h1.ne' h2.ne' _), rhs_val _ c hc hX] at h
    exact_mod_cast h
  have q1 := key P0 (9 / 10) (1 / 10) (9 / 10) (Or.inl rfl) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sand _ _)
  have q2 := key P0 (1 / 10) (9 / 10) (1 / 10) (Or.inl rfl) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sand _ _)
  have q3 := key H0 (9 / 10) (1 / 10) ((9 / 10 + 1 / 10) / 2) (Or.inr rfl) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (sandH _ _)
  rw [quasi_two f P0_idem P0_herm P0_ne0 P0_ne1 P0_idem P0_herm P0_ne0 P0_ne1 1 0 _ _
    one_ne_zero (by norm_num)] at q1 q2
  rw [quasi_two f P0_idem P0_herm P0_ne0 P0_ne1 H0_idem H0_herm H0_ne0 H0_ne1 1 0 _ _
    one_ne_zero (by norm_num)] at q3
  rw [gh_sq (by norm_num), gh_sq (by norm_num)] at q1 q2 q3
  have hx := gh_sq (x := 9 / 10) (by norm_num)
  have hy := gh_sq (x := 1 / 10) (by norm_num)
  have hz := gh_sq (x := 1 / 2) (by norm_num)
  have px := gh_pos (x := 9 / 10) (by norm_num)
  have py := gh_pos (x := 1 / 10) (by norm_num)
  have pz := gh_pos (x := 1 / 2) (by norm_num)
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.one_apply] at q1 q2 q3
  simp [P0, H0] at q1 q2 q3
  norm_num at q1 q2 q3
  have hsum : gh (9 / 10) + gh (1 / 10) = 2 * gh (1 / 2) := by
    norm_num at pz hz ⊢
    linarith
  norm_num at hz pz hx hy px py hsum
  have hxy : gh (9 / 10) * gh (1 / 10) = 1 / 2 := by
    have e : (gh (9 / 10) + gh (1 / 10)) * (gh (9 / 10) + gh (1 / 10)) = 2 := by
      rw [hsum]; linear_combination 4 * hz
    linear_combination e / 2 - hx / 2 - hy / 2
  have e2 : (gh (9 / 10) * gh (1 / 10)) * (gh (9 / 10) * gh (1 / 10)) =
      (gh (9 / 10) * gh (9 / 10)) * (gh (1 / 10) * gh (1 / 10)) := by ring
  rw [hxy, hx, hy] at e2
  norm_num at e2

end A3S55EX

open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

theorem solution :
    ¬ ∃ f : ℝ → ℝ, DivergenceGenerator f ∧
      ∀ (n : ℕ), 0 < n → ∀ rho sigma : Mat (Fin n),
        AlgebraDensity ⊤ rho → AlgebraDensity ⊤ sigma →
        div f rho sigma = (tr (supportPower
          (supportPower rho (1 / 2) * sigma * supportPower rho (1 / 2)) (1 / 2)) : EReal) := by
  rintro ⟨f, -, H⟩
  exact A3S55EX.main_contra f H

end

#print axioms solution
