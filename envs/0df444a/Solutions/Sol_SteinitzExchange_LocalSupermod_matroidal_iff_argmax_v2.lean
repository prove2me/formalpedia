-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.matroidal_iff_argmax_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:21:23.029366+00:00
-- url     : https://prove2.me/submissions/719f2a3e-c522-4ba2-aae4-69a2d0bf3a02

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization
import Theorems.Thm_SteinitzExchange_LocalSupermod_localization_eq_min_argmax
import Theorems.Thm_SteinitzExchange_LocalSupermod_baseSet_iff_support_matroidal

open SteinitzExchange.LocalSupermod in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (p₀ : V → ℝ)
    (hconv : ∀ z : V → ℤ, toReal z ∈ hull (argmaxB B (perturb ω (-p₀))) →
      z ∈ argmaxB B (perturb ω (-p₀))) :
    IsMatroidal (localization (concaveConj B ω) p₀) ↔
      IsIntegralBaseSet (argmaxB B (perturb ω (-p₀))) := by
  set A := argmaxB B (perturb ω (-p₀)) with hA
  have hne : A.Nonempty := by
    obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image B (perturb ω (-p₀)) hB.1
    exact ⟨x, Finset.mem_filter.2 ⟨hx, hmax⟩⟩
  have heq : localization (concaveConj B ω) p₀ = supportMin A := by
    funext p
    have hl := localization_eq_min_argmax B hB ω p₀ p
    unfold supportMin
    rw [iInf]
    have hr : (Set.range fun x : (A : Set (V → ℤ)) => pairing p (toReal (x : V → ℤ))) =
        (fun x => pairing p (toReal x)) '' (A : Set (V → ℤ)) := by
      ext y; simp
    rw [hr]
    exact (hl.csInf_eq).symm
  rw [heq]
  exact (baseSet_iff_support_matroidal A hne hconv).symm
