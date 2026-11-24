-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSupSmall_eval_map_int_3fe0911283fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:50.902823+00:00
-- url     : https://prove2.me/submissions/ed92aff3-6735-485f-a11c-112d420b9d33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall

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
theorem _root_.solution {σ R : Type*} [CommRing R] (w : σ → R) (p : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom R) p) = aeval w p := by
  rw [eval_map, aeval_def, algebraMap_int_eq]
end GroundTheory.Heights₂.Heights.YPlusSupSmall
