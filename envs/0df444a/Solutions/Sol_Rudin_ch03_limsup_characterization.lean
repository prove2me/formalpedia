-- Prove2me | solution 1 for Rudin.ch03_limsup_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-13T14:55:47.521983+00:00
-- url     : https://prove2.me/submissions/c2d736de-62c4-4e02-9790-18c2ed1915c0

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

/-- A subsequential limit of `u` is a cluster point of `u` along `atTop`. -/
private theorem mapClusterPt_of_subseq {X : Type*} [TopologicalSpace X] {u : ℕ → X} {y : X}
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (h : Tendsto (fun k => u (φ k)) atTop (𝓝 y)) :
    MapClusterPt y atTop u := by
  have h1 : map (fun k => u (φ k)) atTop ≤ 𝓝 y := h
  have h2 : map (fun k => u (φ k)) atTop ≤ map u atTop := by
    rw [show (fun k => u (φ k)) = u ∘ φ from rfl, ← map_map]
    exact map_mono hφ.tendsto_atTop
  exact neBot_of_le (le_inf h1 h2)

/-- Rudin, Theorem 3.17: let `s` be a sequence of real numbers and let `s*` be its upper limit
in the extended real number system.  Then (a) `s*` is a subsequential limit of `s`, and (b) if
`x > s*` then `s n < x` for all large `n`; moreover `s*` is the only extended real number with
these two properties. -/
theorem solution (s : ℕ → ℝ) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => ((s (φ k) : ℝ) : EReal)) atTop
          (𝓝 (limsup (fun n => ((s n : ℝ) : EReal)) atTop))) ∧
    (∀ x : EReal, limsup (fun n => ((s n : ℝ) : EReal)) atTop < x →
        ∃ N, ∀ n ≥ N, ((s n : ℝ) : EReal) < x) ∧
    (∀ y : EReal,
        ((∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => ((s (φ k) : ℝ) : EReal)) atTop (𝓝 y)) ∧
          (∀ x : EReal, y < x → ∃ N, ∀ n ≥ N, ((s n : ℝ) : EReal) < x)) →
        y = limsup (fun n => ((s n : ℝ) : EReal)) atTop) := by
  set u : ℕ → EReal := fun n => ((s n : ℝ) : EReal) with hu
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨φ, hφ, hlim⟩ := (MapClusterPt.limsup (u := u) (f := atTop)).tendsto_subseq
    exact ⟨φ, hφ, hlim⟩
  · intro x hx
    exact (eventually_lt_of_limsup_lt hx).exists_forall_of_atTop
  · rintro y ⟨⟨φ, hφ, hlim⟩, hub⟩
    refine le_antisymm ?_ ?_
    · exact (isGreatest_mapClusterPt_limsup (u := u) (f := atTop)).2
        (mapClusterPt_of_subseq hφ hlim)
    · by_contra hlt
      rw [not_le] at hlt
      obtain ⟨x, hx1, hx2⟩ := exists_between hlt
      obtain ⟨N, hN⟩ := hub x hx1
      have hle : limsup u atTop ≤ x :=
        limsup_le_of_le (by isBoundedDefault)
          (eventually_atTop.2 ⟨N, fun n hn => (hN n hn).le⟩)
      exact absurd hx2 (not_lt.2 hle)
