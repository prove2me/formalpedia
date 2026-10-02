-- Prove2me | solution 1 for SteinitzExchange.Extension.concave_extension_imp_exc
-- status  : ACCEPTED   (prove)
-- author  : @choi
-- created : 2026-10-01T03:14:45.028993+00:00
-- url     : https://prove2.me/submissions/94c33fbc-b429-4da8-953b-fe2b9f956fed

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure
import Theorems.Thm_SteinitzExchange_Extension_exc_iff_argmax_isIntegralBaseSet
import Theorems.Thm_SteinitzExchange_Extension_toReal_mem_hull_iff

open SteinitzExchange.Extension

/-- A concave extension whose perturbed maximizers are integral base polytopes satisfies (EXC).
The proof passes from the continuous argmax to its integer points, then applies Theorem 4.4.
In fact, agreement on `B` and the integral-base-polytope hypothesis suffice. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (ωbar : (V → ℝ) → ℝ)
    (hconc : ConcaveOn ℝ (hull B) ωbar)
    (hext : ∀ x ∈ B, ωbar (toReal x) = ω x)
    (hpoly : ∀ p : V → ℝ,
      IsIntegralBasePolytope (argmaxOn (hull B) (fun b => ωbar b + pairing p b))) :
    SatisfiesEXC B ω := by
  classical
  apply (exc_iff_argmax_isIntegralBaseSet B hB ω).mpr
  intro p
  obtain ⟨C, hC, hCeq⟩ := hpoly p
  have hCmax : ∀ x ∈ C,
      toReal x ∈ argmaxOn (hull B) (fun b => ωbar b + pairing p b) := by
    intro x hx
    rw [hCeq]
    exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := hC.1
  have hzmax := hCmax z hz
  have hzB : z ∈ B := (toReal_mem_hull_iff B hB z).mp hzmax.1
  have hargmax : argmaxB B (perturb ω p) = C := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ B ∧ ∀ y ∈ B, perturb ω p y ≤ perturb ω p x :=
        Finset.mem_filter.mp hx
      have hxHull : toReal x ∈ hull B := (toReal_mem_hull_iff B hB x).mpr hx'.1
      have hzx : ωbar (toReal z) + pairing p (toReal z) ≤
          ωbar (toReal x) + pairing p (toReal x) := by
        simpa only [perturb, hext z hzB, hext x hx'.1] using hx'.2 z hzB
      have hxmax : toReal x ∈ argmaxOn (hull B) (fun b => ωbar b + pairing p b) :=
        ⟨hxHull, fun c hc => (hzmax.2 c hc).trans hzx⟩
      apply (toReal_mem_hull_iff C hC x).mp
      rw [← hCeq]
      exact hxmax
    · intro hx
      have hxmax := hCmax x hx
      have hxB : x ∈ B := (toReal_mem_hull_iff B hB x).mp hxmax.1
      apply Finset.mem_filter.mpr
      refine ⟨hxB, ?_⟩
      intro y hy
      have hyHull : toReal y ∈ hull B := (toReal_mem_hull_iff B hB y).mpr hy
      simpa only [perturb, hext y hy, hext x hxB] using hxmax.2 (toReal y) hyHull
  rw [hargmax]
  exact hC

