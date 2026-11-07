-- Prove2me | solution 2 for SongZipkinFluct.FixedCost.theorem5e_theorem6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:30:38.699012+00:00
-- url     : https://prove2.me/submissions/d7c9cfb3-9237-4090-9a52-59b78e879ba2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds
import Definitions.Def_SongZipkinFluct_FixedCost_Policy
import Theorems.Thm_SongZipkinFluct_FixedCost_theorem3
import Theorems.Thm_SongZipkinFluct_FixedCost_theorem4
import Theorems.Thm_SongZipkinFluct_FixedCost_theorem5e
import Theorems.Thm_SongZipkinFluct_FixedCost_yplus_exists
import Theorems.Thm_SongZipkinFluct_FixedCost_ystar_exists

open Filter
open SongZipkinFluct.FixedCost
open SongZipkinFluct.FixedCost.Model

lemma frequently_of_finite {α : Type*} [DecidableEq α] (f : ℕ → α) (F : Finset α)
    (hF : ∀ᶠ n in atTop, f n ∈ F) : ∃ v ∈ F, ∃ᶠ n in atTop, f n = v := by
  by_contra h
  push Not at h
  have h2 : ∀ᶠ n in atTop, ∀ v ∈ F, f n ≠ v := by
    rw [Filter.eventually_all_finset]
    intro v hv
    exact (h v hv).mono fun n hn => hn
  obtain ⟨n, hn1, hn2⟩ := (hF.and h2).exists
  exact hn2 _ hn1 rfl

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
    have h4 := (theorem4 M hM hA1 hK yplus hyp ymin hym ystar hys).2
      Splus rplus rminus rmm rs Ss hSp hrp hrm hrmm hst
    refine ⟨fun i => ?_, ?_⟩
    · obtain ⟨v, -, hv⟩ := frequently_of_finite (fun n => (rs n i, Ss n i))
        (Finset.Icc (rmm i) (rplus i) ×ˢ Finset.Icc (ystar i) (Splus i))
        ((eventually_ge_atTop 1).mono fun n hn => by
          have := h4 n hn i
          simp only [Finset.mem_product, Finset.mem_Icc]
          omega)
      exact ⟨v.1, v.2, hv.mono fun n hn => by rw [← hn]; exact ⟨rfl, rfl⟩⟩
    intro rstar Sstar hlim
    refine ⟨theorem5e M hM hA1 hK rs Ss hst rstar Sstar hlim, ?_⟩
    intro i
    obtain ⟨n, ⟨hr, hS⟩, hn1⟩ := ((hlim i).and_eventually (eventually_ge_atTop 1)).exists
    have := h4 n hn1 i
    rw [hr, hS] at this
    exact this
