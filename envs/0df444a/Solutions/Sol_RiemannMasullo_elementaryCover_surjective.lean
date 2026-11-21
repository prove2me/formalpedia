-- Prove2me | solution 1 for RiemannMasullo.elementaryCover_surjective
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:39:04.433499+00:00
-- url     : https://prove2.me/submissions/8380dd63-50ed-4e68-aeab-999312b20376

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L277-L279
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
theorem solution (a : Fin r → ℤ) (b : F)
    (x : EuclideanSpace ℝ (Fin m)) (z : Fin n → AddCircle (1 : ℝ)) :
    ∃ t : EuclideanSpace ℝ (Fin n), elementaryCover (x, t) a b = (x, z, a, b) := by
  classical
  refine ⟨WithLp.toLp 2 (fun i ↦ (z i).out), ?_⟩
  unfold elementaryCover
  exact Prod.ext rfl (Prod.ext (funext fun i ↦ QuotientAddGroup.out_eq' (z i)) rfl)
