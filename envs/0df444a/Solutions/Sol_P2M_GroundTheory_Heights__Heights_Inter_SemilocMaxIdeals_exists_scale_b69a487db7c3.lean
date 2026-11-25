-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_scale_b69a487db7c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:48.986152+00:00
-- url     : https://prove2.me/submissions/0fd9d816-cac1-485b-9867-e8bd328c6888

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_exists_form_avoid_7ec45983efdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_form_notMem_9e34f112a8d3


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
theorem _root_.solution (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W) (a : K → ℕ) {W' : Ideal (MRing ι)}
    (hr : IsRelevant W') (hp : W'.IsPrime) :
    ∃ (t h : MRing ι) (d : K → ℕ), IsMultiHomog t d ∧ IsMultiHomog h (a + d) ∧ t ∉ W' ∧ ∀ W ∈ 𝒲, h ∉ W := by
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid 𝒲 hfin h𝒲
  obtain ⟨h, hh, hhW⟩ := hd₀ (a + d₀) le_add_self
  obtain ⟨t, ht, htW⟩ := exists_form_notMem hr hp d₀
  exact ⟨t, h, d₀, ht, hh, htW, hhW⟩
end GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
