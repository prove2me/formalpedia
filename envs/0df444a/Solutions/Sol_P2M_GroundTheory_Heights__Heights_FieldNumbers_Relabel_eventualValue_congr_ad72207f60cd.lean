-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_congr_ad72207f60cd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:23.32567+00:00
-- url     : https://prove2.me/submissions/2dd7cfc4-6e8e-4704-b67c-93fd910ddced

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel

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
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)
namespace GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
theorem _root_.solution {K K' : Type*} {f : (K → ℤ) → ℤ} {g : (K' → ℤ) → ℤ}
    (h : ∀ c, (∀ᶠ m in atTop, f m = c) ↔ ∀ᶠ m in atTop, g m = c) :
    eventualValue f = eventualValue g := by
  unfold eventualValue
  by_cases hf : ∃ c, ∀ᶠ m in atTop, f m = c
  · have hg : ∃ c, ∀ᶠ m in atTop, g m = c := hf.imp fun c hc => (h c).1 hc
    rw [dif_pos hf, dif_pos hg]
    have h1 := (h _).1 hf.choose_spec
    have h2 := hg.choose_spec
    obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
    exact hm1.symm.trans hm2
  · have hg : ¬ ∃ c, ∀ᶠ m in atTop, g m = c := fun ⟨c, hc⟩ => hf ⟨c, (h c).2 hc⟩
    rw [dif_neg hf, dif_neg hg]
end GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
