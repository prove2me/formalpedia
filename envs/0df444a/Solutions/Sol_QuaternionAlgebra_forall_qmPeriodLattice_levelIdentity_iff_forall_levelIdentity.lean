-- Prove2me | solution 1 for QuaternionAlgebra.forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cf7a537a-3ac6-5f0a-b41f-d6215d4b7a43

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
p2m_open "IsDedekindDomain NumberField QuaternionAlgebra P2MW.S_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity.QuaternionAlgebra CerednikDrinfeld"

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re im coe_algebraMap qmPeriodMap qmPeriodMap_apply qmPeriodLattice mem_qmPeriodLattice_iff IsIndefiniteRamifiedExactlyAt"
namespace LevelIdPullbackAux
p2m_open "QuaternionAlgebra"

theorem qmPeriodMap_injective {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) : Function.Injective (qmPeriodMap ι τ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker, qmPeriodMap_apply] at hx
  have hrow : ∀ i : Fin 2, ι x i 0 = 0 ∧ ι x i 1 = 0 := by
    intro i
    have h := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply, mul_one, Complex.coe_algebraMap] at h
    have him := congrArg Complex.im h
    rw [Complex.add_im, Complex.ofReal_im, add_zero, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.zero_im] at him
    have h0 : ι x i 0 = 0 := (mul_eq_zero.mp him).resolve_right τ.im_pos.ne'
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, h0, zero_mul, zero_add, Complex.zero_re] at hre
    exact ⟨h0, hre⟩
  apply hι
  rw [map_zero]
  ext i j
  fin_cases j
  · exact (hrow i).1
  · exact (hrow i).2

end QuaternionAlgebra.LevelIdPullbackAux

open QuaternionAlgebra.LevelIdPullbackAux in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (Λ J' : Submodule ℤ ℍ[ℚ, a, b]) (t : ℍ[ℚ, a, b]) (ℓ : ℕ) (τ : UpperHalfPlane) :
    (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ y ∈ Λ, (ℓ : ℂ) • w + qmPeriodMap ι τ (y * t) = v) ↔
        ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) ↔
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) := by
  have hinj := qmPeriodMap_injective ι hι τ
  have hsmul : ∀ j : ℍ[ℚ, a, b], (ℓ : ℂ) • qmPeriodMap ι τ j = qmPeriodMap ι τ ((ℓ : ℤ) • j) := fun j => by
    rw [map_zsmul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  constructor
  · intro H x
    constructor
    · rintro ⟨j, hj, m, hm, rfl⟩
      obtain ⟨y, hy, hyv⟩ := (H (qmPeriodMap ι τ ((ℓ : ℤ) • j + m * t))).mp
        ⟨qmPeriodMap ι τ j, (mem_qmPeriodLattice_iff ι J' τ _).mpr ⟨j, hj, rfl⟩, m, hm, by rw [hsmul, ← map_add]⟩
      exact ⟨y, hy, hinj hyv⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨w, hw, y, hy, hv⟩ := (H (qmPeriodMap ι τ (j * t))).mpr ⟨j, hj, rfl⟩
      obtain ⟨j', hj', rfl⟩ := (mem_qmPeriodLattice_iff ι J' τ w).mp hw
      rw [hsmul, ← map_add] at hv
      exact ⟨j', hj', y, hy, hinj hv⟩
  · intro H v
    constructor
    · rintro ⟨w, hw, y, hy, rfl⟩
      obtain ⟨j, hj, rfl⟩ := (mem_qmPeriodLattice_iff ι J' τ w).mp hw
      obtain ⟨j', hj', hx⟩ := (H ((ℓ : ℤ) • j + y * t)).mp ⟨j, hj, y, hy, rfl⟩
      exact ⟨j', hj', by rw [hx, map_add, hsmul]⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨j', hj', m, hm, hx⟩ := (H (j * t)).mpr ⟨j, hj, rfl⟩
      exact ⟨qmPeriodMap ι τ j', (mem_qmPeriodLattice_iff ι J' τ _).mpr ⟨j', hj', rfl⟩, m, hm,
        by rw [hsmul, ← map_add, hx]⟩

end S_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity
end P2MW
export P2MW.S_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity (solution)
