-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_eq_of_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:41.094206+00:00
-- url     : https://prove2.me/submissions/338d64fb-dc1a-4ca1-9cbd-5c2e3aa9808a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_eq_of_intertwining

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (p : Ideal R) [p.IsMaximal]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (hfg : (e : M →ₗ[R] N).comp f = g.comp (e : M →ₗ[R] N))
    (n : ℕ) : primaryTorsionTrace p f n = primaryTorsionTrace p g n := by
  rw [primaryTorsionTrace, primaryTorsionTrace]
  apply Finset.sum_congr rfl
  intro i hi
  exact primaryTorsionGradeTrace_eq_of_intertwining p e f g hfg i
end QEC.Coding.AlgebraicGeometry
