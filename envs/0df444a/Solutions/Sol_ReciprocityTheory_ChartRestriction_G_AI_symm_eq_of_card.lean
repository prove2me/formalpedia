-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.symm_eq_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:53.159592+00:00
-- url     : https://prove2.me/submissions/a7f0cb29-d521-4fb9-bca9-68fd91ccaba4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (v w : Fin n → V)
    (h : ∀ x : V, (Finset.univ.filter fun i => v i = x).card = (Finset.univ.filter fun i => w i = x).card) :
    I v = I w := by
  have e : ∀ c : V, {a // w a = c} ≃ {b // v b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact (h c).symm)
  have hσ : v ∘ (Equiv.ofFiberEquiv e) = w := funext fun i => Equiv.ofFiberEquiv_map e i
  rw [← hσ, hI]
end ReciprocityTheory.ChartRestriction.G.AI
