-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_one_flagMinor_bf395fdba984
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:12.540061+00:00
-- url     : https://prove2.me/submissions/2607c298-1516-4eb3-b389-56e0e1a7f413

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    eval (fun q : Fin n × Fin n => if q.1 = q.2 then (1 : FnField P) else 0)
      (flagMinor (genMat (FnField P) n * B.map C) j S) = flagMinor B j S := by
  rw [flagMinor, flagMinor, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext a b
  simp only [Matrix.map_apply, Matrix.submatrix_apply]
  erw [Matrix.mul_apply]
  simp [genMat]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
