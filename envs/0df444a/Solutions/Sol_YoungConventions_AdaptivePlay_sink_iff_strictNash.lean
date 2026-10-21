-- Prove2me | solution 1 for YoungConventions.AdaptivePlay.sink_iff_strictNash
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:05:43.540506+00:00
-- url     : https://prove2.me/submissions/ab1a9fb1-7c96-41e4-ab84-a4d26025ad63

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_WeaklyAcyclic
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash

set_option autoImplicit false
open YoungConventions.AdaptivePlay

theorem yca_sink_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) :
    IsSink u s ↔ IsStrictNash u s := by
  constructor
  · intro hs i y hy
    by_contra hcon
    push_neg at hcon
    -- hcon : u i s ≤ u i (update s i y)
    have hsy : u i (Function.update s i (s i)) = u i s := by rw [Function.update_eq_self]
    obtain ⟨x₀, hx₀⟩ := Finite.exists_max (fun z : S i => u i (Function.update s i z))
    by_cases hxs : x₀ = s i
    · -- then y is also a best reply
      subst hxs
      apply hs (Function.update s i y)
      refine ⟨i, y, hy, ?_, rfl⟩
      intro z
      have h1 := hx₀ z
      have h2 : u i (Function.update s i (s i)) = u i s := hsy
      linarith
    · apply hs (Function.update s i x₀)
      exact ⟨i, x₀, hxs, hx₀, rfl⟩
  · rintro hs s' ⟨i, x, hx, hbr, rfl⟩
    have h1 := hbr (s i)
    rw [Function.update_eq_self] at h1
    have h2 := hs i x hx
    linarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] (u : ι → (∀ i, S i) → ℝ) :
    (∀ s : ∀ i, S i, IsSink u s ↔ IsStrictNash u s) ∧
      (WeaklyAcyclic u ↔ ∀ s : ∀ i, S i, ∃ s' : ∀ i, S i,
        Relation.ReflTransGen (BestReplyEdge u) s s' ∧ IsStrictNash u s') := by
  refine ⟨yca_sink_iff u, ?_⟩
  unfold WeaklyAcyclic
  simp_rw [yca_sink_iff u]
