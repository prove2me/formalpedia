-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hasRAt_famI_c9f04179f3a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:16.865196+00:00
-- url     : https://prove2.me/submissions/4874d151-404c-40c9-83e7-897077cf9293

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSmoothHerm_segreLine_1e1d36fff7ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_mul_1c4c584656fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_segre_f966ae4bfd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_eq_diff_5bf2b43907d8

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
variable (hMul : RMulStatement) {n : ℕ} (hwd : WDAt (famI (ι := ι)) n)
include hMul hwd
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution : HasRAt (famI (ι := ι)) n := by
  intro P L A s hP hL hA hs
  have hpr : P.IsPrime := hP.2.1.1
  have hH : IsSmoothHerm (segreLine (shift A) : HermLine ι) := isSmoothHerm_segreLine _
  have hu := isSectionOn_segre hP (shift A)
  rw [famI_eq_diff hMul hwd hP hL hA hH (sec_mul hpr hs hu) hu,
    hMul K ι famI P n L A _ s _ hP hL hA hH hs hu]
  ring
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
