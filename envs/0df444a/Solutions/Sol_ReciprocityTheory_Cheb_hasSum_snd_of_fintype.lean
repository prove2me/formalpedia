-- Prove2me | solution 1 for ReciprocityTheory.Cheb.hasSum_snd_of_fintype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:31.56938+00:00
-- url     : https://prove2.me/submissions/8f900d67-03de-4556-a8c3-a65cbb8f039c

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {α β : Type*} [Fintype α] {g : β → ℝ} (hg0 : ∀ b, 0 ≤ g b) {t : ℝ}
    (hg : HasSum g t) : HasSum (fun p : α × β => g p.2) (Fintype.card α * t) := by
  have h1 : HasSum (fun _ : α => (1 : ℝ)) (Fintype.card α) := by
    simpa using hasSum_fintype (fun _ : α => (1 : ℝ))
  have hs : Summable (fun p : α × β => (fun _ : α => (1 : ℝ)) p.1 * g p.2) :=
    Summable.mul_of_nonneg h1.summable hg.summable (fun _ => zero_le_one) hg0
  simpa only [one_mul] using h1.mul hg hs
end ReciprocityTheory.Cheb
