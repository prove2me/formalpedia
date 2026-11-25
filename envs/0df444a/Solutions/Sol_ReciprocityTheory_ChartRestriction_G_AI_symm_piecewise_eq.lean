-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.symm_piecewise_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:42.914122+00:00
-- url     : https://prove2.me/submissions/0fd54ea5-1b9f-4ffd-97c8-b657ebb1ef0e

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s t : Finset (Fin n))
    (hst : s.card = t.card) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (t.piecewise (fun _ => x) fun _ => y) := by
  classical
  have e : ∀ c : Bool, {a // decide (a ∈ t) = c} ≃ {b // decide (b ∈ s) = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      cases c
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = false) = tᶜ := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = false) = sᶜ := by ext; simp
        rw [h1, h2, Finset.card_compl, Finset.card_compl, hst]
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = true) = t := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = true) = s := by ext; simp
        rw [h1, h2, hst])
  have hσ : ∀ i, (Equiv.ofFiberEquiv e i ∈ s ↔ i ∈ t) := fun i => by
    have := Equiv.ofFiberEquiv_map e i
    rw [← decide_eq_decide]
    exact this
  have hfun : (s.piecewise (fun _ => x) fun _ => y) ∘ (Equiv.ofFiberEquiv e) =
      t.piecewise (fun _ => x) fun _ => y := by
    funext i
    rw [Function.comp_apply]
    by_cases hi : i ∈ t
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ ((hσ i).2 hi)]
    · have hi' : Equiv.ofFiberEquiv e i ∉ s := fun h => hi ((hσ i).1 h)
      first
        | rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi']
        | rw [Finset.piecewise_eq_of_not_mem _ _ _ hi, Finset.piecewise_eq_of_not_mem _ _ _ hi']
  rw [← hfun, hI]
end ReciprocityTheory.ChartRestriction.G.AI
