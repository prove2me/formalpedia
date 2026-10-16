-- Prove2me | solution 1 for PrizeAlloc.Param.winner_prize_inverse
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:15:49.61956+00:00
-- url     : https://prove2.me/submissions/5d206162-6c79-48de-b5e8-6cc287310069

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting
import Definitions.Def_PrizeAlloc_Param_ParametricRule

set_option autoImplicit false
open PrizeAlloc.Interval

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Dietzenbacher and Kondratev, arXiv:2008.08985v2, proof of Theorem 3.
theorem solution {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (hOP : OrderPreserving φ) (hWSM : WinnerStrictMonotone φ) (hEC : EndowmentContinuous φ)
    (l : List U) (hl : IsRanking l) (w : U) (hw : w ∈ l) (hw1 : pos l w = 1) :
    StrictMonoOn (fun E => φ l E w) (Set.Ici 0) ∧
      ContinuousOn (fun E => φ l E w) (Set.Ici 0) ∧
      ¬ BddAbove ((fun E => φ l E w) '' Set.Ici 0) ∧
      ∀ x : ℝ, 0 ≤ x → ∃! E : ℝ, 0 ≤ E ∧ φ l E w = x := by
  classical
  have hmono : StrictMonoOn (fun E => φ l E w) (Set.Ici 0) := by
    intro E hE E' _ hlt
    exact hWSM.2 l E E' hl hE hlt w hw hw1
  have hcont := hEC l hl w hw
  have hbudget (E : ℝ) (hE : 0 ≤ E) : E ≤ l.toFinset.card * φ l E w := by
    calc
      E = ∑ j ∈ l.toFinset, φ l E j := (hφ l E hl hE).2.symm
      _ ≤ ∑ _j ∈ l.toFinset, φ l E w := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases heq : j = w
        · subst j; exact le_rfl
        · apply hOP l E hl hE w hw j (List.mem_toFinset.mp hj)
          have hne : l.idxOf w ≠ l.idxOf j := by
            intro h
            exact heq ((List.idxOf_inj hw).mp h).symm
          unfold pos at *
          omega
      _ = _ := by simp
  have hcard : (0 : ℝ) < l.toFinset.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨w,List.mem_toFinset.mpr hw⟩
  have hunbdd : ¬ BddAbove ((fun E => φ l E w) '' Set.Ici 0) := by
    rw [not_bddAbove_iff]
    intro b
    let E : ℝ := l.toFinset.card * (max b 0 + 1)
    have hE : 0 ≤ E := mul_nonneg hcard.le (by positivity)
    refine ⟨φ l E w,⟨E,hE,rfl⟩,?_⟩
    have hb := hbudget E hE
    have hb0 : b ≤ max b 0 := le_max_left _ _
    dsimp [E] at hb
    nlinarith
  refine ⟨hmono,hcont,hunbdd,?_⟩
  intro x hx
  have hzero : φ l 0 w = 0 := by
    have hs := Finset.single_le_sum (s := l.toFinset) (f := φ l 0)
      (fun j hj => (hφ l 0 hl le_rfl).1 j (List.mem_toFinset.mp hj))
      (List.mem_toFinset.mpr hw)
    rw [(hφ l 0 hl le_rfl).2] at hs
    exact le_antisymm hs ((hφ l 0 hl le_rfl).1 w hw)
  obtain ⟨y,⟨E,hE,rfl⟩,hy⟩ := not_bddAbove_iff.mp hunbdd x
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc hE
    (hcont.mono (fun _ h => h.1)) ⟨by simpa [hzero] using hx,hy.le⟩
  refine ⟨e,⟨he.1,heq⟩,?_⟩
  intro e' he'
  exact hmono.injOn he'.1 he.1 (he'.2.trans heq.symm)

#print axioms solution
