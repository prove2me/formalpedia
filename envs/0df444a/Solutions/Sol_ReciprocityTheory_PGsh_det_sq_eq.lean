-- Prove2me | solution 1 for ReciprocityTheory.PGsh.det_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:25:44.814206+00:00
-- url     : https://prove2.me/submissions/514176f5-f8ea-4b9d-ad67-567ec58a33d1

import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAUses
import Theorems.Thm_ReciprocityTheory_PGsh_det_stdJ_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {D : Type} [CommRing D] {g : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D)
    (hJ : Φᵀ * stdJ D g * Φ = c • E) :
    Φ.det ^ 2 = c ^ (2 * g) * (E.det * (stdJ D g).det) := by
  have h := congrArg Matrix.det hJ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_sum, Fintype.card_fin,
    ← two_mul] at h
  have hJ2 := det_stdJ_sq (D := D) (g := g)
  calc Φ.det ^ 2 = Φ.det ^ 2 * ((stdJ D g).det ^ 2) := by rw [hJ2, mul_one]
    _ = (Φ.det * (stdJ D g).det * Φ.det) * (stdJ D g).det := by ring
    _ = c ^ (2 * g) * (E.det * (stdJ D g).det) := by rw [h]; ring
end ReciprocityTheory.PGsh
