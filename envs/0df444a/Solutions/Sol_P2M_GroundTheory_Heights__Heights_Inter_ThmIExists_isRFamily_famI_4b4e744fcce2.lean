-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isRFamily_famI_4b4e744fcce2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:27.879959+00:00
-- url     : https://prove2.me/submissions/c31994c4-fc40-47ec-b0b3-e762b11c4207

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_all_dims_7eb7dcfabea6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1)) :
    IsRFamily (famI (ι := ι)) :=
  ⟨fun P n L A B hP hL hA hB => (all_dims hD1 hMul hstep n).2.2 P L A B hP hL hA hB,
    fun P n L A s a hP hL hA ha hs hsP =>
      (all_dims hD1 hMul hstep n).2.1 P L A s hP hL hA ⟨a, ha, hs, hsP⟩⟩
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
