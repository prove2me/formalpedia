-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_all_dims_7eb7dcfabea6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:06.108285+00:00
-- url     : https://prove2.me/submissions/ae8e3df7-98c6-44ef-ad72-77b6427e0207

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hasRAt_famI_c9f04179f3a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_lastAddAt_famI_86b3ad5459f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_wdAt_zero_e03b9480a50b

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
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1))
    (n : ℕ) : WDAt (famI (ι := ι)) n ∧ HasRAt (famI (ι := ι)) n ∧ LastAddAt (famI (ι := ι)) n := by
  induction n with
  | zero =>
    have h0 := wdAt_zero (ι := ι) hD1
    exact ⟨h0, hasRAt_famI hMul h0, lastAddAt_famI hMul h0⟩
  | succ n ih =>
    have h1 := hstep n ih.2.1 ih.2.2
    exact ⟨h1, hasRAt_famI hMul h1, lastAddAt_famI hMul h1⟩
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
