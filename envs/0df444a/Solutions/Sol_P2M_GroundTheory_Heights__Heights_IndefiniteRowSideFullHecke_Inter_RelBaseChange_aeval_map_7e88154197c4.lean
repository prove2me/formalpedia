-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_RelBaseChange_aeval_map_7e88154197c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:33.876711+00:00
-- url     : https://prove2.me/submissions/54dc35f1-8d9b-4411-9ab6-dbfc77e7d23d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRelBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial TensorProduct
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace RelBaseChange
theorem _root_.solution {F F' : Type} [Field F] [Field F'] [Algebra F F'] {σ τ : Type}
    (g : σ → MvPolynomial τ F) (p : MvPolynomial σ F) :
    aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (MvPolynomial.map (algebraMap F F') p) =
      MvPolynomial.map (algebraMap F F') (aeval g p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, hp, map_X, aeval_X]
end RelBaseChange
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
