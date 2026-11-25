-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_submatrix_eq_zero_cec33daaf8a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:25.011166+00:00
-- url     : https://prove2.me/submissions/ae758399-c9e7-4835-956f-5ef9fc94c6be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Finset Equiv
open GroundTheory.Heights₂.Heights.CauchyBinetAlt
variable {R : Type*} [CommRing R] {j N : ℕ}
namespace GroundTheory.Heights₂.Heights.CauchyBinetAlt
theorem _root_.solution (A : Matrix (Fin j) (Fin N) R) {p : Fin j → Fin N}
    (hp : ¬ Function.Injective p) : (A.submatrix id p).det = 0 := by
  simp only [Function.Injective, not_forall, exists_prop] at hp
  obtain ⟨a, b, hab, hne⟩ := hp
  exact det_zero_of_column_eq hne fun k => by simp [hab]
end GroundTheory.Heights₂.Heights.CauchyBinetAlt
