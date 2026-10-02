-- Prove2me | solution 1 for SteinitzExchange.Extension.exc_iff_concave_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T17:05:42.864129+00:00
-- url     : https://prove2.me/submissions/100bf7e8-9529-4fa2-bd67-e31b203a528d

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure
import Theorems.Thm_SteinitzExchange_Extension_concaveClosure_concaveOn
import Theorems.Thm_SteinitzExchange_Extension_concaveClosure_eq_of_exc
import Theorems.Thm_SteinitzExchange_Extension_argmaxOn_perturbed_eq_hull
import Theorems.Thm_SteinitzExchange_Extension_exc_iff_argmax_isIntegralBaseSet
import Theorems.Thm_SteinitzExchange_Extension_concave_extension_imp_exc

open Classical
open SteinitzExchange.Extension

-- Reduction of Murota 1996, p. 288, Theorem 4.6 (Extension Theorem).
--
-- The parent equivalence
--
--     `SatisfiesEXC B ω ↔ ∃ ωbar, ConcaveOn ℝ (hull B) ωbar ∧ (∀ x ∈ B, ωbar (toReal x) = ω x) ∧
--                             (∀ p, IsIntegralBasePolytope (argmaxOn (hull B) (fun b => ωbar b + pairing p b)))`
--
-- is discharged here by exhibiting, in the forward direction, the concave closure `ωbar := concaveClosure B ω`
-- as the extension, and delegating each of its ingredients to a child lemma.

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔
      ∃ ωbar : (V → ℝ) → ℝ, ConcaveOn ℝ (hull B) ωbar ∧
        (∀ x ∈ B, ωbar (toReal x) = ω x) ∧
        ∀ p : V → ℝ,
          IsIntegralBasePolytope (argmaxOn (hull B) (fun b => ωbar b + pairing p b)) := by
  classical
  -- `IsIntegralBaseSet` is a conjunction of nonemptiness and the base-exchange property, so
  -- the nonemptiness hypothesis needed by the two `concaveClosure` children is `hB.1`.
  constructor
  · -- Forward direction: an M-concave `ω` extends to the concave closure.
    intro hω
    refine ⟨concaveClosure B ω, ?_, ?_, ?_⟩
    · -- (1) The concave closure is concave on `B̄`, for every `g` (child: concavity of `ĝ`).
      exact concaveClosure_concaveOn B hB.1 ω
    · -- (2) On an integral base set an M-concave function agrees with its concave closure
      --     (Murota 1996, p. 288, Lemma 4.5).
      exact concaveClosure_eq_of_exc B hB ω hω
    · -- (3) For each `p`, the maximizers of `ĝ[p]` over `B̄` are `conv(argmax(g[p]))`, which
      --     Theorem 4.4 makes an integral base polytope.
      intro p
      have har := argmaxOn_perturbed_eq_hull B hB.1 ω p
      have hbase : IsIntegralBaseSet (argmaxB B (perturb ω p)) :=
        (exc_iff_argmax_isIntegralBaseSet B hB ω).mp hω p
      -- `IsIntegralBasePolytope P` unfolds to `∃ B', IsIntegralBaseSet B' ∧ P = hull B'`;
      -- the child identity supplies the equation with `B' = argmaxB B (perturb ω p)`.
      refine ⟨argmaxB B (perturb ω p), hbase, ?_⟩
      exact har
  · -- Reverse direction: a concave extension with integral base polytope maximizers is M-concave.
    rintro ⟨ωbar, hconc, hext, hpoly⟩
    exact concave_extension_imp_exc B hB ω ωbar hconc hext hpoly
