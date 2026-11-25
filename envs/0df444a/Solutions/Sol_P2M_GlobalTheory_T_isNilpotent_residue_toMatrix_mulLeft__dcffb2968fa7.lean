-- Prove2me | solution 1 for P2M_GlobalTheory_T_isNilpotent_residue_toMatrix_mulLeft__dcffb2968fa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:54.38077+00:00
-- url     : https://prove2.me/submissions/e463036b-af59-405b-991e-5ce59e7b8e56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsNilpotentResidueToMatrixMulLeft
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsNilpotentResidueToMatrixMulLeftStatement
import Theorems.Thm_GlobalTheory_isNilpotent_residue_toMatrix_mulLeft


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by
  first | exact @GlobalTheory.isNilpotent_residue_toMatrix_mulLeft | exact GlobalTheory.isNilpotent_residue_toMatrix_mulLeft | (intros; apply GlobalTheory.isNilpotent_residue_toMatrix_mulLeft <;> assumption)
end _root_.GlobalTheory.T
