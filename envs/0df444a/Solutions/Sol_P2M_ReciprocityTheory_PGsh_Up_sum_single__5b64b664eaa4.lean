-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_Up_sum_single__5b64b664eaa4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:37.091037+00:00
-- url     : https://prove2.me/submissions/aeff873a-ca10-4e9f-ac4e-6ea9cca0fbd7

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] {g d : ℕ} (P : Matrix (Fin g) (Fin g) R) (hP : P * P = P)
  (φ : LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R))
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n : ℕ} (y : Fin n → R) : y = ∑ l, y l • (Pi.single l 1 : Fin n → R) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]
end ReciprocityTheory.PGsh.Up
