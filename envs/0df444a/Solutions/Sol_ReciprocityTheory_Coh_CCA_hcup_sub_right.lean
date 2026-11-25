-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.hcup_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:33.571376+00:00
-- url     : https://prove2.me/submissions/52d76d7a-2e33-460a-8f37-f7710e09bf8b

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {X V W Z : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z] (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V)
    (F₁ F₂ : (Fin (q + 1) → X) → W) :
    hcup β p q F (F₁ - F₂) = hcup β p q F F₁ - hcup β p q F F₂ := by
  funext x
  simp only [hcup, Pi.sub_apply, map_sub]
end ReciprocityTheory.Coh.CCA
