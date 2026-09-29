-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.exc_iff_localization_matroidal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T15:51:05.601455+00:00
-- url     : https://prove2.me/submissions/4b989d94-c253-4c53-bdd1-7c0d07e5778f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization
import Theorems.Thm_SteinitzExchange_LocalSupermod_concaveClosure_eq_of_exc
import Theorems.Thm_SteinitzExchange_LocalSupermod_matroidal_iff_argmax
import Theorems.Thm_SteinitzExchange_LocalSupermod_exc_iff_argmax_isIntegralBaseSet

open SteinitzExchange.LocalSupermod

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔
      ((∀ x ∈ B, concaveClosure B ω (toReal x) = ω x) ∧
        ∀ p₀ : V → ℝ, IsMatroidal (localization (concaveConj B ω) p₀)) := by
  constructor
  · intro hω
    have hclos : ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x :=
      concaveClosure_eq_of_exc B hB ω hω
    have hargmax : ∀ p : V → ℝ, IsIntegralBaseSet (argmaxB B (perturb ω p)) :=
      (exc_iff_argmax_isIntegralBaseSet B hB ω).mp hω
    refine ⟨hclos, fun p₀ => ?_⟩
    exact (matroidal_iff_argmax B hB ω p₀).mpr (hargmax (-p₀))
  · rintro ⟨_, hmat⟩
    apply (exc_iff_argmax_isIntegralBaseSet B hB ω).mpr
    intro p
    simpa only [neg_neg] using (matroidal_iff_argmax B hB ω (-p)).mp (hmat (-p))
