-- Prove2me | solution 1 for RelativisticZK205.ThreeCol.pr_no_signalling
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-24T23:45:02.831809+00:00
-- url     : https://prove2.me/submissions/55d85334-8cb5-49f1-89d6-3bfea77b87f1

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_PRBox

open RelativisticZK205 RelativisticZK205.ThreeCol

-- riskiest
/-- Each `prSolutions` set has exactly two elements. -/
lemma prSolutions_card (a b : Bool) : (prSolutions a b).card = 2 := by
  cases a <;> cases b <;> unfold prSolutions <;> decide

/-- Pointwise description: each solution of `x ⊕ y = a ∧ b` gets mass `1/2`, everything else `0`. -/
lemma prBox_apply_eq (a b : Bool) (p : Bool × Bool) :
    (prBox a b) p = (if xor p.1 p.2 = (a && b) then (1 : ENNReal) / 2 else 0) := by
  dsimp only [prBox]
  rw [PMF.uniformOfFinset_apply, prSolutions_card]
  have h : p ∈ prSolutions a b ↔ xor p.1 p.2 = (a && b) := by
    simp [prSolutions, Finset.mem_filter, Finset.mem_univ]
  simp [h]

/-- `Finset.univ : Finset (Bool × Bool)` is the four-element finset of all bit pairs. -/
lemma univ_Bool_pair :
    (Finset.univ : Finset (Bool × Bool)) = {(false, false), (false, true), (true, false), (true, true)} := by
  decide

/-- Alice's marginal sum: for fixed inputs `a, b` and output `x`, the total mass of pairs with
first coordinate `x` is `1/2`. -/
lemma aliceMarg_step (a b x : Bool) :
    (∑ p : Bool × Bool, if x = p.1 then (prBox a b) p else 0) = (1 : ENNReal) / 2 := by
  cases a <;> cases b <;> cases x <;>
    (rw [univ_Bool_pair]
     simp [prBox_apply_eq])

/-- Bob's marginal sum: for fixed inputs `a, b` and output `y`, the total mass of pairs with
second coordinate `y` is `1/2`. -/
lemma bobMarg_step (a b y : Bool) :
    (∑ p : Bool × Bool, if y = p.2 then (prBox a b) p else 0) = (1 : ENNReal) / 2 := by
  cases a <;> cases b <;> cases y <;>
    (rw [univ_Bool_pair]
     simp [prBox_apply_eq])

/-- Alice's marginal is the uniform PMF on `Bool`, for every pair of inputs. -/
lemma prBox_aliceMarg (a b : Bool) :
    (prBox a b).map Prod.fst =
      PMF.uniformOfFinset (Finset.univ : Finset Bool) (Finset.univ_nonempty : Finset.univ.Nonempty) := by
  refine PMF.ext fun x => ?_
  rw [PMF.map_apply, tsum_eq_sum (s := (Finset.univ : Finset (Bool × Bool))) (fun p h => by simp at h)]
  cases x <;> cases a <;> cases b <;>
    (rw [univ_Bool_pair]
     simp [prBox_apply_eq, PMF.uniformOfFinset_apply])

/-- Bob's marginal is the uniform PMF on `Bool`, for every pair of inputs. -/
lemma prBox_bobMarg (a b : Bool) :
    (prBox a b).map Prod.snd =
      PMF.uniformOfFinset (Finset.univ : Finset Bool) (Finset.univ_nonempty : Finset.univ.Nonempty) := by
  refine PMF.ext fun y => ?_
  rw [PMF.map_apply, tsum_eq_sum (s := (Finset.univ : Finset (Bool × Bool))) (fun p h => by simp at h)]
  cases y <;> cases a <;> cases b <;>
    (rw [univ_Bool_pair]
     simp [prBox_apply_eq, PMF.uniformOfFinset_apply])

/-- Fig. 6, p.6: the PR-box is No-Signalling, and its output `(x, y)` on inputs `(a, b)` has
positive probability exactly when `x ⊕ y = a ∧ b`. -/
theorem solution :
    IsNoSignalling prBox ∧ ∀ a b x y : Bool, (prBox a b (x, y) ≠ 0 ↔ xor x y = (a && b)) := by
  refine ⟨?_, ?_⟩
  · unfold IsNoSignalling
    constructor
    · intro a b b'
      rw [prBox_aliceMarg, prBox_aliceMarg]
    · intro a a' b
      rw [prBox_bobMarg, prBox_bobMarg]
  · intro a b x y
    simp only [prBox, prSolutions, PMF.uniformOfFinset_apply, ne_eq, ite_eq_right_iff,
      ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, Finset.mem_filter, Finset.mem_univ,
      Classical.not_imp]
    simp
