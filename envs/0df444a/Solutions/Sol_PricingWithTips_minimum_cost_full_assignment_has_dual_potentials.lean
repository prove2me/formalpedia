-- Prove2me | solution 1 for PricingWithTips.minimum_cost_full_assignment_has_dual_potentials
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:06:02.542521+00:00
-- url     : https://prove2.me/submissions/d88c41aa-371a-4ae9-bc65-c404849fef97

import Theorems.Thm_PricingWithTips_full_courier_assignment_equiv_orders
import Theorems.Thm_PricingWithTips_minimum_cost_full_assignment_optimal_matching
import Theorems.Thm_AssignmentGame_CoreCorners_optimal_matching_has_dual_potentials

open PricingWithTips
open AssignmentGame.CoreCorners

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (hminimum : ∀ A' : Allocation B S D,
      (∀ b, (A'.assigned b).map Prod.fst = (A.assigned b).map Prod.fst) →
        welfare M A' ≤ welfare M A) :
    ∃ (C : ℝ) (u : D → ℝ) (v : B → S → ℝ),
      (∀ d, 0 ≤ u d) ∧
      (∀ d b s, C - M.cost d b s ≤ u d + v b s) ∧
      (∀ d b s, A.Trades b s d → u d + v b s = C - M.cost d b s) := by
  classical
  let O := {p : B × S // A.Delivers p.1 p.2}
  obtain ⟨e, he⟩ := full_courier_assignment_equiv_orders A hfull
  obtain ⟨U, hU⟩ : BddAbove
      (Set.range (fun x : D × B × S => M.cost x.1 x.2.1 x.2.2)) :=
    Finite.bddAbove_range _
  let C : ℝ := max 0 U + 1
  have hC : ∀ d b s, M.cost d b s < C := by
    intro d b s
    have hc : M.cost d b s ≤ U := hU ⟨(d, b, s), rfl⟩
    have hUmax : U ≤ max 0 U := le_max_right _ _
    dsimp [C]
    linarith
  let a : D → O → ℝ := fun d o => C - M.cost d o.1.1 o.1.2
  have ha : ∀ d o, 0 ≤ a d o := by
    intro d o
    dsimp [a]
    linarith [hC d o.1.1 o.1.2]
  let P : Finset (D × O) := Finset.univ.image (fun d => (d, e d))
  have hP : IsMatching Finset.univ Finset.univ P := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp
    · intro p hp q hq hfst
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨d', _, rfl⟩ := Finset.mem_image.mp hq
      simp only at hfst
      subst d'
      rfl
    · intro p hp q hq hsnd
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨d', _, rfl⟩ := Finset.mem_image.mp hq
      have hde : d = d' := e.injective hsnd
      subst d'
      rfl
  have hsum : (∑ p ∈ P, a p.1 p.2) = ∑ d, a d (e d) := by
    dsimp [P]
    rw [Finset.sum_image]
    intro d _ d' _ hpair
    exact congrArg Prod.fst hpair
  have hopt : (∑ p ∈ P, a p.1 p.2) =
      worth a Finset.univ Finset.univ := by
    rw [hsum]
    exact minimum_cost_full_assignment_optimal_matching M A hfull hminimum e he C hC
  obtain ⟨u, v, hu, _hv, hdual, htight⟩ :=
    optimal_matching_has_dual_potentials a ha P hP hopt
  let vg : B → S → ℝ := fun b s =>
    if hd : A.Delivers b s then v ⟨(b, s), hd⟩ else C
  refine ⟨C, u, vg, hu, ?_, ?_⟩
  · intro d b s
    by_cases hd : A.Delivers b s
    · simpa [vg, hd, a] using hdual d (⟨(b, s), hd⟩ : O)
    · simp only [vg, dif_neg hd]
      linarith [hu d, M.cost_nonneg d b s]
  · intro d b s htrade
    have hd : A.Delivers b s := ⟨d, htrade⟩
    have horder : e d = (⟨(b, s), hd⟩ : O) := by
      apply Subtype.ext
      have hb : (e d).1.1 = b := A.courier_unique (he d) htrade
      have hed : A.Trades b (e d).1.2 d := by
        simpa [hb] using he d
      have hs : (e d).1.2 = s := by
        have hp : some ((e d).1.2, d) = some (s, d) := hed.symm.trans htrade
        exact congrArg Prod.fst (Option.some.inj hp)
      exact Prod.ext hb hs
    have hmem : (d, e d) ∈ P := by
      simp [P]
    have h := htight (d, e d) hmem
    rw [horder] at h
    simpa [vg, hd, a] using h
