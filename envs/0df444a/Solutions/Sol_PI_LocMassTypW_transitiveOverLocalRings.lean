-- Prove2me | solution 1 for PI.LocMassTypW.transitiveOverLocalRings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:16.335297+00:00
-- url     : https://prove2.me/submissions/3f8af749-a0b2-410b-9ce5-449dd28f4c0f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings
import Theorems.Thm_PI_LocMassTypW_WCoreP_field_mat
import Theorems.Thm_PI_LocMassTypW_WCoreP_affine_sol
import Theorems.Thm_PI_LocMassTypW_WCoreP_proj_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW
open Matrix WCoreP
namespace PI.LocMassTypW
theorem _root_.solution : WCore := by
  intro O _ _ n m A0 A B0 B ⟨L0, hL0⟩ ⟨L, hL⟩ ⟨M0, hM0⟩ ⟨M, hM⟩ hC
  set f := IsLocalRing.residue O with hf
  have hmap1 : ∀ {X : Matrix (Fin m) (Fin n) O} {Y : Matrix (Fin n) (Fin m) O}, X * Y = 1 →
      X.map f * Y.map f = 1 := by
    intro X Y h
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]
  have hCf : (A0.map f)ᵀ * B0.map f = (A.map f)ᵀ * B.map f := by
    rw [← Matrix.transpose_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hC]

  obtain ⟨kb, hkbu, hkbA, hkbB⟩ := field_mat (A0.map f) (A.map f) (B0.map f) (B.map f) (L0.map f) (L.map f)
    (M0.map f) (M.map f) (hmap1 hL0) (hmap1 hL) (hmap1 hM0) (hmap1 hM) hCf
  have hC' : B0ᵀ * A0 = Bᵀ * A := by
    have h := congrArg Matrix.transpose hC
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h

  obtain ⟨hk1A, hk1B⟩ := affine_sol A0 A B0 B L0 M hL0 hM hC' 0
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at hk1A hk1B
  set hbar := kb - (k1 A B0 B L0 M).map f with hhbar
  have hb1 : hbar * A0.map f = 0 := by
    rw [hhbar, Matrix.sub_mul, hkbA, ← Matrix.map_mul, hk1A, sub_self]
  have hb2 : (B.map f)ᵀ * hbar = 0 := by
    rw [hhbar, Matrix.mul_sub, hkbB, ← Matrix.transpose_map (M := B), ← Matrix.map_mul, hk1B,
      Matrix.transpose_map, sub_self]
  have hproj := proj_fix (A0.map f) (B.map f) (L0.map f) (M.map f) hbar hb1 hb2

  let X : Matrix (Fin n) (Fin n) O := fun i j => Function.surjInv IsLocalRing.residue_surjective (hbar i j)
  have hX : X.map f = hbar := by
    ext i j
    exact Function.surjInv_eq IsLocalRing.residue_surjective (hbar i j)
  obtain ⟨hkA, hkB⟩ := affine_sol A0 A B0 B L0 M hL0 hM hC' X
  set k := k1 A B0 B L0 M + (1 - Mᵀ * Bᵀ) * X * (1 - A0 * L0) with hk
  have hkmap : k.map f = kb := by
    rw [← RingHom.mapMatrix_apply, hk]
    simp only [map_add, map_mul, map_sub, map_one, RingHom.mapMatrix_apply]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map, hX, hproj, hhbar]
    abel
  refine ⟨k, ?_, hkA, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hdet : IsLocalRing.residue O k.det = kb.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hf, hkmap]
    rw [hdet]
    exact ((Matrix.isUnit_iff_isUnit_det kb).mp hkbu).ne_zero
  · have h := congrArg Matrix.transpose hkB
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h
end PI.LocMassTypW
