-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.smul_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:48.978828+00:00
-- url     : https://prove2.me/submissions/64323074-8ddc-46c9-b4c0-4e653912d73a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    MeasurePreserving (fun y : Fin D → ℂ => ζ • y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => ζ • y) := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  refine ⟨?_, (Homeomorph.smulOfNeZero ζ hζ0).measurableEmbedding⟩
  let c : Circle := ⟨ζ, by simp [Submonoid.unitSphere, hζ]⟩
  have h := volume_preserving_pi (ι := Fin D) (fun _ => (rotation c).measurePreserving)
  convert h using 1
  funext y i
  rw [Pi.smul_apply, smul_eq_mul, rotation_apply]
end ReciprocityTheory.AnForm.A
