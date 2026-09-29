-- Prove2me | solution 1 for Submodule.finiteAdeleEvalAt_finiteIdeleDiagonal_inv_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5a131c34-11b2-59aa-b95c-504a8e7a580d

import Definitions.Def_Submodule_LocalBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_finiteAdeleEvalAt_finiteIdeleDiagonal_inv_mul_eq_one

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D] (w : HeightOneSpectrum (𝓞 ℚ)) (γ : Dˣ)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (γ : D) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) :
    Submodule.finiteAdeleEvalAt D w
      (((Submodule.finiteIdeleDiagonal D γ)⁻¹ * g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
  rw [Units.val_mul, map_mul, hg, ← map_inv, Submodule.val_finiteIdeleDiagonal_apply, Submodule.finiteAdeleEvalAt_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, Algebra.TensorProduct.one_def]
  congr 1
  exact one_mul _

end S_Submodule_finiteAdeleEvalAt_finiteIdeleDiagonal_inv_mul_eq_one
end P2MW
export P2MW.S_Submodule_finiteAdeleEvalAt_finiteIdeleDiagonal_inv_mul_eq_one (solution)
