-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_comp_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:18:08.29277+00:00
-- url     : https://prove2.me/submissions/aadc8179-3a3c-4628-b41a-bee379e2c33d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_comp_comm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (g.comp f) n =
      primaryTorsionTrace p (f.comp g) n := by
  rw [primaryTorsionTrace, primaryTorsionTrace]
  apply Finset.sum_congr rfl
  intro i hi
  exact primaryTorsionGradeTrace_comp_comm p f g i
end QEC.Coding.AlgebraicGeometry
