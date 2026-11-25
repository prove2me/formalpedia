-- Prove2me | solution 1 for PI.LocMassTypL.wCoreG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:55.884717+00:00
-- url     : https://prove2.me/submissions/f5ae42af-6d76-4f32-919a-fe5c0f0b8d1d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypL
open Matrix PI.LocMassTypW.WCoreP
namespace PI.LocMassTypL
theorem _root_.solution (O : Type) [CommRing O] [IsLocalRing O] {n m : ℕ} (t : O)
    (ht : t ∈ IsLocalRing.maximalIdeal O) (A0 A B0 B A' B' : Matrix (Fin n) (Fin m) O)
    (L0 M : Matrix (Fin m) (Fin n) O) (hL0 : L0 * A0 = 1) (hM : M * B = 1)
    (hC : A0ᵀ * B0 = Aᵀ * B) (hA : A = A0 + t • A') (hB : B = B0 + t • B') :
    ∃ k K' : Matrix (Fin n) (Fin n) O, IsUnit k ∧ k * A0 = A ∧ kᵀ * B = B0 ∧ k = 1 + t • K' := by
  classical
  set K' : Matrix (Fin n) (Fin n) O := A' * L0 - Mᵀ * B'ᵀ * (1 - A0 * L0) with hK'

  have h1 : (1 - A0 * L0) * A0 = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hL0, Matrix.mul_one, sub_self]

  have hkey : t • (A0ᵀ * B' + A'ᵀ * B) = 0 := by
    have e : Aᵀ * B = A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B) := by
      calc Aᵀ * B = A0ᵀ * B + t • (A'ᵀ * B) := by
            rw [hA, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul]
        _ = A0ᵀ * B0 + t • (A0ᵀ * B') + t • (A'ᵀ * B) := by
            nth_rewrite 1 [hB]; rw [Matrix.mul_add, Matrix.mul_smul]
        _ = A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B) := by rw [smul_add, add_assoc]
    rw [e] at hC
    calc t • (A0ᵀ * B' + A'ᵀ * B) = (A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B)) - A0ᵀ * B0 := by abel
      _ = 0 := by rw [← hC, sub_self]
  have hBM : Bᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]
  have key' : t • (Bᵀ * A') + t • (B'ᵀ * A0) = 0 := by
    have := congrArg Matrix.transpose hkey
    simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_zero, smul_add] at this
    rw [add_comm]; exact this
  have hB0 : B0ᵀ = Bᵀ - t • B'ᵀ := by
    rw [hB, Matrix.transpose_add, Matrix.transpose_smul, add_sub_cancel_right]
  have hk : Bᵀ * (1 + t • K') = B0ᵀ := by
    have e : Bᵀ * (1 + t • K') = Bᵀ - t • B'ᵀ + (t • (Bᵀ * A') + t • (B'ᵀ * A0)) * L0 := by
      simp only [hK', Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_sub,
        ← Matrix.mul_assoc, hBM, Matrix.one_mul, Matrix.add_mul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, key', Matrix.zero_mul, add_zero, hB0]
  refine ⟨1 + t • K', K', ?_, ?_, ?_, rfl⟩
  ·
    rw [Matrix.isUnit_iff_isUnit_det]
    have ht0 : IsLocalRing.residue O t = 0 := (IsLocalRing.residue_eq_zero_iff t).2 ht
    have hmap : (IsLocalRing.residue O).mapMatrix (1 + t • K') = 1 := by
      ext i j
      simp [Matrix.one_apply, apply_ite, ht0]
    have hdet : IsLocalRing.residue O (1 + t • K').det = 1 := by
      rw [RingHom.map_det, hmap, Matrix.det_one]
    by_contra hnu
    have hm : (1 + t • K').det ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [(IsLocalRing.residue_eq_zero_iff _).2 hm] at hdet
    exact zero_ne_one hdet
  · rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hK', Matrix.sub_mul, Matrix.mul_assoc A',
      hL0, Matrix.mul_one, Matrix.mul_assoc (Mᵀ * B'ᵀ), h1, Matrix.mul_zero, sub_zero, hA]
  · rw [← Matrix.transpose_transpose B, ← Matrix.transpose_mul, hk,
      Matrix.transpose_transpose]
end PI.LocMassTypL
