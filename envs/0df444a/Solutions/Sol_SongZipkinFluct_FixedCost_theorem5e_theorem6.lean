-- Prove2me | solution 1 for SongZipkinFluct.FixedCost.theorem5e_theorem6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:51:42.686286+00:00
-- url     : https://prove2.me/submissions/a493df7a-e840-493e-afca-539dedeef78b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds
import Definitions.Def_SongZipkinFluct_FixedCost_Policy
import Theorems.Thm_SongZipkinFluct_FixedCost_theorem3
import Theorems.Thm_SongZipkinFluct_FixedCost_theorem4
import Theorems.Thm_SongZipkinFluct_FixedCost_theorem5c
import Theorems.Thm_SongZipkinFluct_FixedCost_theorem5e
import Theorems.Thm_SongZipkinFluct_FixedCost_yplus_exists
import Theorems.Thm_SongZipkinFluct_FixedCost_ystar_exists

open Filter
open SongZipkinFluct.FixedCost
open SongZipkinFluct.FixedCost.Model

theorem solution {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar) :
    ((∃ yplus, IsYPlus M yplus) ∧
      (∀ yplus, IsYPlus M yplus → ∃ ymin, IsYPlusMin yplus ymin) ∧
      (∃ ystar, IsYStar M ystar) ∧
      (∀ yplus, IsYPlus M yplus →
        (∃ Splus, IsSPlus M yplus Splus) ∧ (∃ rplus, IsRPlus M yplus rplus)) ∧
      (∀ ystar, IsYStar M ystar → ∃ rminus, IsRMinus M ystar rminus) ∧
      (∀ yplus ymin, IsYPlus M yplus → IsYPlusMin yplus ymin →
        ∃ rmm, IsRMinusMinus M ymin rmm) ∧
      (∃ rs Ss, IsStageParams M rs Ss)) ∧
    ∀ (yplus : I → ℤ) (ymin : ℤ) (ystar Splus rplus rminus rmm : I → ℤ)
      (rs Ss : ℕ → I → ℤ),
      IsYPlus M yplus → IsYPlusMin yplus ymin → IsYStar M ystar →
      IsSPlus M yplus Splus → IsRPlus M yplus rplus → IsRMinus M ystar rminus →
      IsRMinusMinus M ymin rmm → IsStageParams M rs Ss →
      (∀ i, ∃ r S : ℤ, ∃ᶠ n in atTop, rs n i = r ∧ Ss n i = S) ∧
      ∀ rstar Sstar : I → ℤ,
        (∀ i, ∃ᶠ n in atTop, rs n i = rstar i ∧ Ss n i = Sstar i) →
        IsOptimal M M.K (rSPolicy rstar Sstar) ∧
        ∀ i, (ystar i ≤ Sstar i ∧ Sstar i < Splus i) ∧
          (rmm i ≤ rminus i ∧ rminus i ≤ rstar i ∧ rstar i ≤ rplus i) := by
  obtain ⟨⟨yp0, hyp0⟩, hmin⟩ := yplus_exists M hM hA1
  obtain ⟨ys0, hys0⟩ := ystar_exists M hM hA1
  refine ⟨⟨⟨yp0, hyp0⟩, hmin, ⟨ys0, hys0⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro yplus hyp
    obtain ⟨ymin, hym⟩ := hmin yplus hyp
    obtain ⟨⟨hS, hr, -, -⟩, -⟩ := theorem4 M hM hA1 hK yplus hyp ymin hym ys0 hys0
    exact ⟨hS, hr⟩
  · intro ystar hys
    obtain ⟨ymin, hym⟩ := hmin yp0 hyp0
    exact (theorem4 M hM hA1 hK yp0 hyp0 ymin hym ystar hys).1.2.2.1
  · intro yplus ymin hyp hym
    exact (theorem4 M hM hA1 hK yplus hyp ymin hym ys0 hys0).1.2.2.2
  · have hex : ∀ n : ℕ, ∀ i : I, ∃ p : ℤ × ℤ, 1 ≤ n → IsRSParams M.K (Gfix M n i) p.1 p.2 := by
      intro n i
      by_cases hn : 1 ≤ n
      · obtain ⟨r, S, h⟩ := (theorem3 M hM hA1 hK i n hn).2.1.1
        exact ⟨(r, S), fun _ => h⟩
      · exact ⟨(0, 0), fun h => absurd h hn⟩
    choose p hp using hex
    exact ⟨fun n i => (p n i).1, fun n i => (p n i).2, fun n hn i => hp n i hn⟩
  · intro yplus ymin ystar Splus rplus rminus rmm rs Ss hyp hym hys hSp hrp hrm hrmm hst
    refine ⟨fun i => (theorem5c M hM hA1 hK rs Ss hst i).1, ?_⟩
    intro rstar Sstar hlim
    refine ⟨theorem5e M hM hA1 hK rs Ss hst rstar Sstar hlim, ?_⟩
    intro i
    have h4 := (theorem4 M hM hA1 hK yplus hyp ymin hym ystar hys).2
      Splus rplus rminus rmm rs Ss hSp hrp hrm hrmm hst
    obtain ⟨n, ⟨hr, hS⟩, hn1⟩ := ((hlim i).and_eventually (eventually_ge_atTop 1)).exists
    have := h4 n hn1 i
    rw [hr, hS] at this
    exact this
