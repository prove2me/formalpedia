-- Prove2me | solution 1 for SpilloverDuopoly.Switchers.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T23:01:25.208288+00:00
-- url     : https://prove2.me/submissions/28316a35-ce52-45d3-a37f-527be30ffb4e

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Model

set_option autoImplicit false

namespace SpilloverDuopoly.Switchers.Aux3c0d

open SpilloverDuopoly.Switchers

lemma shareA_self (G : Params) (p : ℝ) (h : G.u0 ≤ G.CS p) : G.shareA p p = G.lam := by
  unfold Params.shareA
  rw [if_neg (by intro hh; exact lt_irrefl _ hh.2), if_pos ⟨h, rfl⟩]

lemma shareB_self (G : Params) (p : ℝ) (h : G.u0 ≤ G.CS p) : G.shareB p p = 1 - G.lam := by
  unfold Params.shareB
  rw [if_neg (by intro hh; exact lt_irrefl _ hh.2), if_pos ⟨h, rfl⟩]

lemma shareA_lt (G : Params) (x p : ℝ) (h : G.u0 ≤ G.CS p) (hx : x < p) :
    G.shareA x p = 1 := by
  unfold Params.shareA
  have h1 : G.CS p < G.CS x := by unfold Params.CS; linarith
  rw [if_pos ⟨le_trans h h1.le, h1⟩]

lemma shareB_lt (G : Params) (x p : ℝ) (hx : x < p) : G.shareB x p = 0 := by
  unfold Params.shareB
  have h1 : G.CS p < G.CS x := by unfold Params.CS; linarith
  rw [if_neg (by intro hh; exact lt_asymm h1 hh.2),
    if_neg (by intro hh; exact (ne_of_lt h1) hh.2)]

lemma shareA_gt (G : Params) (x p : ℝ) (hx : p < x) : G.shareA x p = 0 := by
  unfold Params.shareA
  have h1 : G.CS x < G.CS p := by unfold Params.CS; linarith
  rw [if_neg (by intro hh; exact lt_asymm h1 hh.2),
    if_neg (by intro hh; exact (ne_of_lt h1) hh.2)]

lemma shareB_gt (G : Params) (x p : ℝ) (h : G.u0 ≤ G.CS p) (hx : p < x) :
    G.shareB x p = 1 := by
  unfold Params.shareB
  have h1 : G.CS x < G.CS p := by unfold Params.CS; linarith
  rw [if_pos ⟨h, h1⟩]

lemma shareA_lt' (G : Params) (p y : ℝ) (hy : y < p) : G.shareA p y = 0 := by
  unfold Params.shareA
  have h1 : G.CS p < G.CS y := by unfold Params.CS; linarith
  rw [if_neg (by intro hh; exact lt_asymm h1 hh.2),
    if_neg (by intro hh; exact (ne_of_lt h1) hh.2)]

lemma shareB_lt' (G : Params) (p y : ℝ) (h : G.u0 ≤ G.CS p) (hy : y < p) :
    G.shareB p y = 1 := by
  unfold Params.shareB
  have h1 : G.CS p < G.CS y := by unfold Params.CS; linarith
  rw [if_pos ⟨le_trans h h1.le, h1⟩]

lemma shareA_gt' (G : Params) (p y : ℝ) (h : G.u0 ≤ G.CS p) (hy : p < y) :
    G.shareA p y = 1 := by
  unfold Params.shareA
  have h1 : G.CS y < G.CS p := by unfold Params.CS; linarith
  rw [if_pos ⟨h, h1⟩]

lemma shareB_gt' (G : Params) (p y : ℝ) (hy : p < y) : G.shareB p y = 0 := by
  unfold Params.shareB
  have h1 : G.CS y < G.CS p := by unfold Params.CS; linarith
  rw [if_neg (by intro hh; exact lt_asymm h1 hh.2),
    if_neg (by intro hh; exact (ne_of_lt h1) hh.2)]

lemma profitA_self (G : Params) (p : ℝ) (h : G.u0 ≤ G.CS p) :
    G.profitA p p = G.lam * (p - G.pStar) + G.delta * G.piS := by
  unfold Params.profitA Params.pStar
  rw [shareA_self G p h, shareB_self G p h]; ring

lemma profitB_self (G : Params) (p : ℝ) (h : G.u0 ≤ G.CS p) :
    G.profitB p p = (1 - G.lam) * (p - G.pStar) + G.delta * G.piS := by
  unfold Params.profitB Params.pStar
  rw [shareA_self G p h, shareB_self G p h]; ring

/-- a real bounded above by every positive number is nonpositive -/
lemma nonpos_of_forall (a : ℝ) (h : ∀ e : ℝ, 0 < e → a ≤ e) : a ≤ 0 := by
  by_contra hc
  replace hc := lt_of_not_ge hc
  have := h (a / 2) (by linarith)
  linarith

end SpilloverDuopoly.Switchers.Aux3c0d

open SpilloverDuopoly.Switchers in
theorem solution (G : Params) (hS : G.Standing) (p : ℝ) (hcov : G.u0 ≤ G.CS p) :
    (G.IsSymEq p ↔ p = G.pStar) ∧
    (G.IsSymEq p → G.profitA p p = G.delta * G.piS ∧ G.profitB p p = G.delta * G.piS) := by
  have hP : G.pStar = G.c - G.delta * (G.piR - G.piS) := rfl
  have key : G.IsSymEq p ↔ p = G.pStar := by
    constructor
    · rintro ⟨-, -, hA, hB⟩
      have hA' : ∀ x : ℝ, G.profitA x p ≤ G.profitA p p := fun x => hA x (Set.mem_univ _)
      have hB' : ∀ y : ℝ, G.profitB p y ≤ G.profitB p p := fun y => hB y (Set.mem_univ _)
      rw [Aux3c0d.profitA_self G p hcov] at hA'
      rw [Aux3c0d.profitB_self G p hcov] at hB'
      have h1 : (1 - G.lam) * (p - G.pStar) ≤ 0 := by
        apply Aux3c0d.nonpos_of_forall
        intro e he
        have := hA' (p - e)
        unfold Params.profitA at this
        rw [Aux3c0d.shareA_lt G _ _ hcov (by linarith), Aux3c0d.shareB_lt G _ _ (by linarith)] at this
        linarith
      have h2 : 0 ≤ G.lam * (p - G.pStar) := by
        have := hA' (p + 1)
        unfold Params.profitA at this
        rw [Aux3c0d.shareA_gt G _ _ (by linarith), Aux3c0d.shareB_gt G _ _ hcov (by linarith)] at this
        linarith
      have h3 : G.lam * (p - G.pStar) ≤ 0 := by
        apply Aux3c0d.nonpos_of_forall
        intro e he
        have := hB' (p - e)
        unfold Params.profitB at this
        rw [Aux3c0d.shareA_lt' G _ _ (by linarith), Aux3c0d.shareB_lt' G _ _ hcov (by linarith)] at this
        linarith
      have h4 : 0 ≤ (1 - G.lam) * (p - G.pStar) := by
        have := hB' (p + 1)
        unfold Params.profitB at this
        rw [Aux3c0d.shareA_gt' G _ _ hcov (by linarith), Aux3c0d.shareB_gt' G _ _ (by linarith)] at this
        linarith
      linarith
    · intro hp
      refine ⟨Set.mem_univ _, Set.mem_univ _, ?_, ?_⟩
      · intro x _
        show G.profitA x p ≤ G.profitA p p
        rw [Aux3c0d.profitA_self G p hcov]
        rcases lt_trichotomy x p with hx | hx | hx
        · unfold Params.profitA
          rw [Aux3c0d.shareA_lt G _ _ hcov hx, Aux3c0d.shareB_lt G _ _ hx]
          rw [hp] at hx ⊢
          nlinarith
        · rw [hx, Aux3c0d.profitA_self G p hcov]
        · unfold Params.profitA
          rw [Aux3c0d.shareA_gt G _ _ hx, Aux3c0d.shareB_gt G _ _ hcov hx, hp]
          simp
      · intro y _
        show G.profitB p y ≤ G.profitB p p
        rw [Aux3c0d.profitB_self G p hcov]
        rcases lt_trichotomy y p with hy | hy | hy
        · unfold Params.profitB
          rw [Aux3c0d.shareA_lt' G _ _ hy, Aux3c0d.shareB_lt' G _ _ hcov hy]
          rw [hp] at hy ⊢
          nlinarith
        · rw [hy, Aux3c0d.profitB_self G p hcov]
        · unfold Params.profitB
          rw [Aux3c0d.shareA_gt' G _ _ hcov hy, Aux3c0d.shareB_gt' G _ _ hy, hp]
          simp
  refine ⟨key, fun h => ?_⟩
  have hp := key.mp h
  rw [Aux3c0d.profitA_self G p hcov, Aux3c0d.profitB_self G p hcov, hp]
  constructor <;> ring
