-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.eval_blockSlice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:47.050999+00:00
-- url     : https://prove2.me/submissions/a37773bd-10da-4fb8-9337-19d048bc5229

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCores

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} (f : MvPolynomial (Fin B × Fin n) ℂ) (b : Fin B)
    (p : Fin B → Fin n → ℂ) (w : Fin n → ℂ) :
    eval w (bind₁ (blockSlice b p) f) = eval (fun q => Function.update p b w q.1 q.2) f := by
  have hφ : (fun q => eval₂Hom (RingHom.id ℂ) w (blockSlice b p q)) =
      fun q => Function.update p b w q.1 q.2 := by
    funext q
    by_cases hq : q.1 = b
    · simp [blockSlice, hq]
    · simp [blockSlice, hq]
  show eval₂Hom (RingHom.id ℂ) w (bind₁ _ f) = _
  rw [eval₂Hom_bind₁, hφ]
  rfl
end ReciprocityTheory.MultiplicativeHeights
