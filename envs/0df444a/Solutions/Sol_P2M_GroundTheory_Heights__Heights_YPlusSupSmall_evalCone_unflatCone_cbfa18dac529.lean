-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSupSmall_evalCone_unflatCone_cbfa18dac529
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:20.127981+00:00
-- url     : https://prove2.me/submissions/81876b0f-e905-4424-84a0-ddc42f5bcf92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_eval_map_int_3fe0911283fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.YPlusSupSmall
theorem _root_.solution {κ : Type} {m : κ → ℕ} {R : Type*} [CommRing R] (w : Coord m → R)
    (p : MvPolynomial (Coord m) ℤ) : evalCone (unflatCone w) p = aeval w p := by
  rw [← eval_map_flatCone, flatCone_unflatCone, eval_map_int]
end GroundTheory.Heights₂.Heights.YPlusSupSmall
