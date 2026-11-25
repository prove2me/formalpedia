-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1GenAmple_of_subsingleton_920f91cfcb7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:47.723447+00:00
-- url     : https://prove2.me/submissions/9c32bfa1-7673-49d6-a150-d07ef8176a12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_cechHc_one_subsingleton_0d6516e3ebc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_generatedMod_of_subsingleton_6bce206c756e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (V : Ideal (MRingOver S ι)) (N : K → ℤ) : H1GenAmple S V N := by
  intro M _ _ _ _ 𝓜 _ _ _ e
  exact ⟨0, fun c _ => ⟨cechHc_one_subsingleton 𝓜 _, generatedMod_of_subsingleton 𝓜 _⟩⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel
