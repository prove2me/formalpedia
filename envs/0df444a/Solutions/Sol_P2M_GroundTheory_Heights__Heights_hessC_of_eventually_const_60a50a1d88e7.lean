-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hessC_of_eventually_const_60a50a1d88e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:59.417818+00:00
-- url     : https://prove2.me/submissions/b92d0a5b-3958-4c07-9ff8-78278669c6bb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_congr__aa19fc468bd1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {c : ℝ}
    (h : φ =ᶠ[𝓝 y] fun _ => c) : hessC φ y = 0 ∧ hessC (fun z => φ z ^ 2 / 2) y = 0 := by
  have h2 : (fun z => φ z ^ 2 / 2) =ᶠ[𝓝 y] fun _ => c ^ 2 / 2 := by
    filter_upwards [h] with z hz
    rw [hz]
  have hc : ∀ a : ℝ, hessC (fun _ : Fin D → ℂ => a) y = 0 := by
    intro a
    ext i j
    simp [hessC]
  exact ⟨(hessC_congr' h).trans (hc c), (hessC_congr' h2).trans (hc _)⟩
end GroundTheory.Heights₂.Heights
