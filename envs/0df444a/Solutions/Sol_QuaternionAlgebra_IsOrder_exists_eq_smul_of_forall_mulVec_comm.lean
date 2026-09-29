-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_eq_smul_of_forall_mulVec_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/73a8fcb4-4b67-5d46-8f8f-5c28051e4653

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_eq_smul_of_forall_mulVec_comm

set_option autoImplicit false

open scoped Quaternion MatrixGroups
open QuaternionAlgebra CerednikDrinfeld

noncomputable section
namespace Schur11

variable {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]

omit [Fact q'.Prime] in
theorem ne_zero_and_ne_zero (hB : IsIndefiniteRamifiedExactlyAt a b q q') : a ≠ 0 ∧ b ≠ 0 := by
  have key : ∀ y : ℍ[ℚ, a, b], y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    obtain ⟨u, rfl⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB y hy
    apply hy
    calc (u : ℍ[ℚ, a, b]) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hyy, mul_zero]
  refine ⟨fun h0 => key ⟨0, 1, 0, 0⟩ ?_ ?_, fun h0 => key ⟨0, 0, 1, 0⟩ ?_ ?_⟩
  · intro h; simpa using congrArg QuaternionAlgebra.imI h
  · ext <;> simp [h0]
  · intro h; simpa using congrArg QuaternionAlgebra.imJ h
  · ext <;> simp [h0]

abbrev cx (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ := A.map (algebraMap ℝ ℂ)

theorem cx_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) : cx (A * B) = cx A * cx B := Matrix.map_mul
theorem cx_one : cx (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  simp [cx]
theorem cx_add (A B : Matrix (Fin 2) (Fin 2) ℝ) : cx (A + B) = cx A + cx B := by ext i j; simp [cx]
theorem cx_neg (A : Matrix (Fin 2) (Fin 2) ℝ) : cx (-A) = -cx A := by ext i j; simp [cx]
theorem cx_smul (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : cx (r • A) = (r : ℂ) • cx A := by
  ext i j; simp [cx, Matrix.map_apply]

theorem coeff_zero {I J : Matrix (Fin 2) (Fin 2) ℂ} {a' b' : ℂ} (ha : a' ≠ 0) (hb : b' ≠ 0)
    (hI : I * I = a' • 1) (hJ : J * J = b' • 1) (hIJ : I * J = -(J * I)) (x y : ℂ)
    (h : x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + y • J = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp only [zero_smul, add_zero] at h
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
    simp at this
    exact ⟨this, rfl⟩
  · exfalso

    have hJs : J = (-(x / y)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have : y • J = -(x • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := eq_neg_of_add_eq_zero_right h
      calc J = y⁻¹ • (y • J) := by rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
        _ = (-(x / y)) • 1 := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    have hcomm : I * J = J * I := by rw [hJs]; simp
    have hJI0 : J * I = 0 := by
      have := hIJ; rw [hcomm] at this

      have h2 : (2 : ℂ) • (J * I) = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel _
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    have : (b' * a') • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
      calc (b' * a') • (1 : Matrix (Fin 2) (Fin 2) ℂ) = (J * J) * (I * I) := by
            rw [hI, hJ, smul_mul_smul_comm, one_mul]
        _ = J * (J * I) * I := by simp [mul_assoc]
        _ = 0 := by rw [hJI0, mul_zero, zero_mul]
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) this
    simp [ha, hb] at this

end Schur11
end

open Schur11 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (hM : ∀ x ∈ Λ, ∀ v : Fin 2 → ℂ, M (((ι x).map (algebraMap ℝ ℂ)).mulVec v) = ((ι x).map (algebraMap ℝ ℂ)).mulVec (M v)) :
    ∃ c : ℂ, ∀ v : Fin 2 → ℂ, M v = c • v := by
  classical
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB

  have hMB : ∀ y : ℍ[ℚ, a, b], ∀ v : Fin 2 → ℂ, M ((cx (ι y)).mulVec v) = (cx (ι y)).mulVec (M v) := by
    intro y
    have hy : y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := by rw [hΛ.spanTop]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx => exact hM x hx
    | zero => intro v; simp [cx]
    | add x y _ _ hx hy => intro v; rw [map_add, cx_add, Matrix.add_mulVec, map_add, hx, hy, Matrix.add_mulVec]
    | smul r x _ hx =>
      intro v
      rw [map_smul, show (r • ι x) = ((r : ℝ) • ι x) from rfl, cx_smul, Matrix.smul_mulVec, map_smul, hx,
        Matrix.smul_mulVec]

  set A : Matrix (Fin 2) (Fin 2) ℂ := LinearMap.toMatrix' M with hA
  have hAv : ∀ v, M v = A.mulVec v := fun v => by rw [hA, LinearMap.toMatrix'_mulVec]
  have hcommY : ∀ y : ℍ[ℚ, a, b], A * cx (ι y) = cx (ι y) * A := by
    intro y
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hAv, hMB]
  set I : Matrix (Fin 2) (Fin 2) ℂ := cx (ι ⟨0, 1, 0, 0⟩) with hIdef
  set J : Matrix (Fin 2) (Fin 2) ℂ := cx (ι ⟨0, 0, 1, 0⟩) with hJdef
  have hqI : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩ = (a : ℚ) • (1 : ℍ[ℚ, a, b]) := by ext <;> simp
  have hqJ : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = (b : ℚ) • (1 : ℍ[ℚ, a, b]) := by ext <;> simp
  have hqIJ : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = -(⟨0, 0, 1, 0⟩ * ⟨0, 1, 0, 0⟩) := by ext <;> simp
  have hI : I * I = ((a : ℝ) : ℂ) • 1 := by
    rw [hIdef, ← cx_mul, ← map_mul, hqI, map_smul, map_one, show ((a : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = ((a : ℝ) • 1) from by ext i j; simp [Matrix.smul_apply, Rat.smul_def], cx_smul, cx_one]
  have hJ : J * J = ((b : ℝ) : ℂ) • 1 := by
    rw [hJdef, ← cx_mul, ← map_mul, hqJ, map_smul, map_one, show ((b : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = ((b : ℝ) • 1) from by ext i j; simp [Matrix.smul_apply, Rat.smul_def], cx_smul, cx_one]
  have hIJ : I * J = -(J * I) := by
    rw [hIdef, hJdef, ← cx_mul, ← cx_mul, ← map_mul, ← map_mul, hqIJ, map_neg, cx_neg]
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  have hb' : ((b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb

  let v : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, I, J, I * J]
  have hJinv : J * ((((b : ℝ) : ℂ))⁻¹ • J) = 1 := by rw [mul_smul_comm, hJ, smul_smul, inv_mul_cancel₀ hb', one_smul]
  have hIinv : ((((a : ℝ) : ℂ))⁻¹ • I) * I = 1 := by rw [smul_mul_assoc, hI, smul_smul, inv_mul_cancel₀ ha', one_smul]
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [v, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hg

    obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) ℂ, C = (((b : ℝ) : ℂ))⁻¹ • J := ⟨_, rfl⟩
    rw [← hC] at hJinv
    have e3 : J * J * C = J := by
      rw [hC, mul_smul_comm, hJ, smul_mul_assoc, one_mul, smul_smul, inv_mul_cancel₀ hb', one_smul]
    have e1 : J * (1 : Matrix (Fin 2) (Fin 2) ℂ) * C = 1 := by rw [mul_one, hJinv]
    have e2 : J * I * C = -I := by
      rw [show J * I = -(I * J) by rw [hIJ, neg_neg], neg_mul, mul_assoc, hJinv, mul_one]
    have e4 : J * (I * J) * C = -(I * J) := by
      rw [← mul_assoc, show J * I = -(I * J) by rw [hIJ, neg_neg], neg_mul, neg_mul, mul_assoc (I * J), hJinv, mul_one]
    have hg' : g 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + g 1 • (-I) + g 2 • J + g 3 • (-(I * J)) = 0 := by
      let f : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
        (LinearMap.mulRight ℂ C).comp (LinearMap.mulLeft ℂ J)
      have hf : ∀ X, f X = J * X * C := fun X => by
        simp [f, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      have h := congrArg f hg
      rw [map_zero, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hf, hf, hf, hf,
        e1, e2, e3, e4] at h
      exact h

    have hsum : (2 * g 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (2 * g 2) • J = 0 := by
      have := congrArg₂ (· + ·) hg hg'
      simp only [add_zero] at this
      calc (2 * g 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (2 * g 2) • J
          = (g 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + g 1 • I + g 2 • J + g 3 • (I * J)) +
            (g 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + g 1 • (-I) + g 2 • J + g 3 • (-(I * J))) := by module
        _ = 0 := this
    have hdiff : (2 * g 1) • I + (2 * g 3) • (I * J) = 0 := by
      have := congrArg₂ (· - ·) hg hg'
      simp only [sub_zero] at this
      calc (2 * g 1) • I + (2 * g 3) • (I * J)
          = (g 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + g 1 • I + g 2 • J + g 3 • (I * J)) -
            (g 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + g 1 • (-I) + g 2 • J + g 3 • (-(I * J))) := by module
        _ = 0 := this
    obtain ⟨h0, h2⟩ := coeff_zero ha' hb' hI hJ hIJ _ _ hsum
    have hdiff' : (2 * g 1) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (2 * g 3) • J = 0 := by
      have := congrArg (fun X => ((((a : ℝ) : ℂ))⁻¹ • I) * X) hdiff
      simp only [mul_add, mul_smul_comm, mul_zero, ← mul_assoc, hIinv, one_mul] at this
      exact this
    obtain ⟨h1, h3⟩ := coeff_zero ha' hb' hI hJ hIJ _ _ hdiff'
    have two0 : (2 : ℂ) ≠ 0 := two_ne_zero
    intro i
    fin_cases i
    · exact (mul_eq_zero.mp h0).resolve_left two0
    · exact (mul_eq_zero.mp h1).resolve_left two0
    · exact (mul_eq_zero.mp h2).resolve_left two0
    · exact (mul_eq_zero.mp h3).resolve_left two0
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp [Module.finrank_matrix]

  have hcomm1 : ∀ i, Commute (v i) A := by
    intro i
    fin_cases i
    · exact Commute.one_left A
    · exact (show Commute I A from (hcommY _).symm)
    · exact (show Commute J A from (hcommY _).symm)
    · exact (show Commute I A from (hcommY _).symm).mul_left (show Commute J A from (hcommY _).symm)
  have hcommAll : ∀ Y : Matrix (Fin 2) (Fin 2) ℂ, Commute Y A := by
    intro Y
    have hY : Y ∈ Submodule.span ℂ (Set.range v) := by rw [hspan]; trivial
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hcomm1 i
    | zero => exact Commute.zero_left A
    | add x y _ _ hx hy => exact hx.add_left hy
    | smul r x _ hx => exact hx.smul_left r
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr (fun i j => hcommAll _)
  refine ⟨c, fun w => ?_⟩
  rw [hAv, ← hc, Matrix.scalar_apply]
  ext i
  rw [Matrix.mulVec_diagonal]; simp [Pi.smul_apply]

end S_QuaternionAlgebra_IsOrder_exists_eq_smul_of_forall_mulVec_comm
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_eq_smul_of_forall_mulVec_comm (solution)
