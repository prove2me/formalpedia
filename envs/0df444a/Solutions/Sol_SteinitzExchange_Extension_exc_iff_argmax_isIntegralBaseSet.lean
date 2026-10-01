-- Prove2me | solution 1 for SteinitzExchange.Extension.exc_iff_argmax_isIntegralBaseSet
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @choi
-- created : 2026-10-01T03:34:37.600658+00:00
-- url     : https://prove2.me/submissions/a972a6c9-3640-4d37-b344-208b4141ef20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Theorems.Thm_SteinitzExchange_Extension_exc_add_linear
import Theorems.Thm_SteinitzExchange_Extension_argmax_isIntegralBaseSet
import Theorems.Thm_SteinitzExchange_Extension_exc_iff_exc_loc
import Theorems.Thm_SteinitzExchange_Extension_exists_perturb_hull_argmax
import Theorems.Thm_SteinitzExchange_Extension_midpoint_exchange_mem_base

open SteinitzExchange.Extension

/-- The maximizer characterization follows from linear perturbation invariance in the forward
 direction and from the midpoint geometry of perturbed maximizer base polytopes in the reverse. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ ∀ p : V → ℝ, IsIntegralBaseSet (argmaxB B (perturb ω p)) := by
  classical
  constructor
  · intro hω p
    exact argmax_isIntegralBaseSet B hB (perturb ω p) (exc_add_linear B hB ω hω p)
  · intro hmax
    apply (exc_iff_exc_loc B hB ω).mpr
    intro x hx y hy hxy
    have hxHull : toReal x ∈ hull B := subset_convexHull ℝ _ ⟨x, hx, rfl⟩
    have hyHull : toReal y ∈ hull B := subset_convexHull ℝ _ ⟨y, hy, rfl⟩
    have hmid : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull B :=
      (convex_convexHull ℝ _) hxHull hyHull (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨p, hpmid⟩ := exists_perturb_hull_argmax B hB.1 ω _ hmid
    obtain ⟨u, v, hu, hv, hxu, hyv⟩ := midpoint_exchange_mem_base
      B (argmaxB B (perturb ω p)) hB (hmax p) x y hx hy hxy hpmid
    have hxmem : x - chi u + chi v ∈ B ∧
        ∀ z ∈ B, perturb ω p z ≤ perturb ω p (x - chi u + chi v) :=
      Finset.mem_filter.mp hxu
    have hymem : y + chi u - chi v ∈ B ∧
        ∀ z ∈ B, perturb ω p z ≤ perturb ω p (y + chi u - chi v) :=
      Finset.mem_filter.mp hyv
    refine ⟨u, v, hu, hv, hxmem.1, hymem.1, ?_⟩
    have hsum := add_le_add (hxmem.2 x hx) (hymem.2 y hy)
    dsimp only [perturb] at hsum
    have hpair : pairing p (toReal x) + pairing p (toReal y) =
        pairing p (toReal (x - chi u + chi v)) +
          pairing p (toReal (y + chi u - chi v)) := by
      unfold pairing toReal
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [Pi.sub_apply, Pi.add_apply]
      push_cast
      ring
    linarith only [hsum, hpair]
