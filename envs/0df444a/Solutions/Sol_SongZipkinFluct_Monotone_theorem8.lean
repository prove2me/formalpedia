-- Prove2me | solution 1 for SongZipkinFluct.Monotone.theorem8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:55:55.744435+00:00
-- url     : https://prove2.me/submissions/f042604e-ee16-4a9a-80a8-8a6a7be1c8cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Condition1
import Definitions.Def_SongZipkinFluct_Monotone_Recursion
import Theorems.Thm_SongZipkinFluct_Monotone_theorem7
import Theorems.Thm_SongZipkinFluct_Monotone_lemma9
import Theorems.Thm_SongZipkinFluct_Monotone_yplus_exists
import Theorems.Thm_SongZipkinFluct_Monotone_theorem2_b
import Theorems.Thm_SongZipkinFluct_Monotone_corollary2

open Filter Topology

namespace SZT8
open SongZipkinFluct.Monotone

/-- If `Δg ≤ Δf` pointwise, the smallest minimizer of `f` is at most that of `g`. -/
lemma smin_le {f g : ℤ → ℝ} (hd : ∀ x, g (x + 1) - g x ≤ f (x + 1) - f x) {a b : ℤ}
    (ha : IsSmallestMinimizer f a) (hb : IsSmallestMinimizer g b) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  have key : ∀ k : ℕ, g (b + k) - g b ≤ f (b + k) - f b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hd (b + k)
      push_cast
      rw [← add_assoc]
      linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a = b + k := ⟨(a - b).toNat, by omega⟩
  have h1 := key k
  rw [← hk] at h1
  have h2 : g b ≤ g a := hb.1 a
  have hbmin : ∀ z, f b ≤ f z := fun z => by
    have h3 : f a ≤ f z := ha.1 z
    linarith
  have := ha.2 hbmin
  omega

theorem main {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1) :
    (∃ yplus : I → ℤ, ∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) ∧
    (∃ ystar : I → ℤ, ∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) ∧
    (∃ ys : ℕ → I → ℤ, (∀ n : ℕ, 1 ≤ n → ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys n i)) ∧
      ∀ i, ∃ y : ℤ, Tendsto (fun n => ys n i) atTop (𝓝 y)) ∧
    ∀ (yplus ystar yinf : I → ℤ) (ys : ℕ → I → ℤ),
      (∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) →
      (∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) →
      (∀ n : ℕ, 1 ≤ n → ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys n i)) →
      (∀ i, Tendsto (fun n => ys n i) atTop (𝓝 (yinf i))) →
      Monotone yplus ∧ Monotone ystar ∧ Monotone yinf := by
  have T7 := theorem7 M hM hA hC
  have L9 := lemma9 M hM hA hC
  obtain ⟨hGlim, hystar⟩ := theorem2_b M hM hA
  have C2 := corollary2 M hM hA
  -- existence of the finite-horizon minimizers
  have hex : ∀ n : ℕ, ∃ y : I → ℤ, 1 ≤ n → ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (y i) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨y, hy⟩ := (T7 n hn).2.2.1
      exact ⟨y, fun _ => hy⟩
    · exact ⟨fun _ => 0, fun h => absurd h hn⟩
  choose ys0 hys0 using hex
  refine ⟨yplus_exists M hM hA, hystar, ⟨ys0, hys0, C2 ys0 hys0⟩, ?_⟩
  intro yplus ystar yinf ys hyp hyst hys hyinf
  have hβ : 0 < M.β := by
    unfold Model.β; have := hM.μ_pos; have := hM.α_pos; positivity
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · -- myopic levels, via Lemma 9
    refine smin_le (f := M.Gplus i) (g := M.Gplus j) (fun x => ?_) (hyp i) (hyp j)
    have := L9 x i j hij
    unfold Δ at this
    unfold Model.Gplus
    push_cast
    nlinarith
  · -- optimal levels, via Theorem 7(b) and the limit G_n → G_∞
    refine smin_le (f := M.Ginf 0 0 i) (g := M.Ginf 0 0 j) (fun x => ?_) (hyst i) (hyst j)
    have hlim : ∀ k : I, Tendsto (fun n : ℕ => M.Gn 0 0 (n + 1) k (x + 1) - M.Gn 0 0 (n + 1) k x)
        atTop (𝓝 (M.Ginf 0 0 k (x + 1) - M.Ginf 0 0 k x)) :=
      fun k => (hGlim k (x + 1)).sub (hGlim k x)
    refine le_of_tendsto_of_tendsto' (hlim j) (hlim i) (fun n => ?_)
    have := (T7 (n + 1) (by omega)).2.1 x hij
    simpa [Δ] using this
  · -- limiting levels, via Theorem 7(c)
    have hle : ∀ᶠ n in atTop, ((ys n i : ℤ) : ℝ) ≤ ((ys n j : ℤ) : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have := (T7 n hn).2.2.2 (ys n) (hys n hn) hij
      exact_mod_cast this
    have hi : Tendsto (fun n => ((ys n i : ℤ) : ℝ)) atTop (𝓝 ((yinf i : ℤ) : ℝ)) :=
      (continuous_of_discreteTopology.tendsto _).comp (hyinf i)
    have hj : Tendsto (fun n => ((ys n j : ℤ) : ℝ)) atTop (𝓝 ((yinf j : ℤ) : ℝ)) :=
      (continuous_of_discreteTopology.tendsto _).comp (hyinf j)
    exact_mod_cast le_of_tendsto_of_tendsto hi hj hle

end SZT8

open SongZipkinFluct.Monotone in
theorem solution {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1) :
    (∃ yplus : I → ℤ, ∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) ∧
    (∃ ystar : I → ℤ, ∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) ∧
    (∃ ys : ℕ → I → ℤ, (∀ n : ℕ, 1 ≤ n → ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys n i)) ∧
      ∀ i, ∃ y : ℤ, Tendsto (fun n => ys n i) atTop (𝓝 y)) ∧
    ∀ (yplus ystar yinf : I → ℤ) (ys : ℕ → I → ℤ),
      (∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) →
      (∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) →
      (∀ n : ℕ, 1 ≤ n → ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys n i)) →
      (∀ i, Tendsto (fun n => ys n i) atTop (𝓝 (yinf i))) →
      Monotone yplus ∧ Monotone ystar ∧ Monotone yinf :=
  SZT8.main M hM hA hC
