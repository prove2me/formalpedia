-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_complexFibreIdeal_of_forall_e9fcbb433878
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:37:39.087031+00:00
-- url     : https://prove2.me/submissions/462b5b11-a3f3-4d12-9acc-4baddc2d12bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_rename_pblk_fcf18dd5a0ec
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
theorem _root_.solution {P : Ideal (MRing (PBlk n))} {z' : (Σ k, PBlk n k) → ℂ}
    (hz : ∀ f ∈ P, eval z' (map (Int.castRingHom ℂ) f) = 0) :
    ∀ q ∈ complexFibreIdeal P, eval (fun i => z' ⟨(), i⟩) q = 0 := by
  intro q hq
  have hle : complexFibreIdeal P ≤ RingHom.ker (eval fun i => z' ⟨(), i⟩) := by
    unfold complexFibreIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, ← eval_map_rename_pblk]
    exact hz _ hg
  exact hle hq
end GroundTheory.Heights₂.Heights
