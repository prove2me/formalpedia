-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_map_rename_pblk_fcf18dd5a0ec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:56.074355+00:00
-- url     : https://prove2.me/submissions/37601fcf-7ec1-4799-9f46-12d0c2c897e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (z' : (Σ k, PBlk n k) → ℂ) (g : MvPolynomial (Fin n) ℤ) :
    eval z' (map (Int.castRingHom ℂ) (rename (fun i : Fin n => (⟨(), i⟩ : Σ k, PBlk n k)) g)) =
      eval (fun i => z' ⟨(), i⟩) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]
  rfl
end GroundTheory.Heights₂.Heights
