-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_eventualValue_comp_47b47bf9c10c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:03.571805+00:00
-- url     : https://prove2.me/submissions/aacf65f2-36dc-493f-b024-a12d280ea408

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)
namespace GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
theorem _root_.solution (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  have key : ∀ c, (∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c) ↔
      ∀ᶠ m in atTop, g m = c := by
    intro c
    rw [← (precompIso e).map_atTop, Filter.eventually_map]
    rfl
  unfold eventualValue
  by_cases hg : ∃ c, ∀ᶠ m in atTop, g m = c
  · have hf : ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      hg.imp fun c hc => (key c).2 hc
    rw [dif_pos hf, dif_pos hg]
    obtain ⟨m, h1, h2⟩ := (((key _).1 hf.choose_spec).and hg.choose_spec).exists
    exact h1.symm.trans h2
  · have hf : ¬ ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      fun ⟨c, hc⟩ => hg ⟨c, (key c).1 hc⟩
    rw [dif_neg hf, dif_neg hg]
end GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
