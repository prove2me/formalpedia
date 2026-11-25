-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_mem_semiMaxIdeal_iff_9811936ba746
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:35:36.378532+00:00
-- url     : https://prove2.me/submissions/56db5dea-27ba-4cdd-ba7c-17efec0cd1db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_maximalIdeal_iff_2f60d05acc3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_semiToLoc_coe_6afe5d0b143c


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))
namespace GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
theorem _root_.solution {W' : Ideal (MRing ι)} [W'.IsPrime] (hW' : W' ∈ 𝒲) (hPW : P ≤ W')
    [IsLocalRing (locRing P W')] (b : semiLocRing P 𝒲) {u w : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a)
    (hw : IsMultiHomog w a) (hwW : w ∉ W')
    (hb : (b : FractionRing (MRing ι ⧸ P)) * fracHom P w = fracHom P u) :
    b ∈ semiMaxIdeal P 𝒲 W' hW' ↔ u ∈ W' := by
  unfold semiMaxIdeal
  rw [Ideal.mem_comap]
  exact mem_maximalIdeal_iff hPW _ hu hw hwW (by rw [semiToLoc_coe]; exact hb)
end GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
