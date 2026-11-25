-- Prove2me | solution 1 for PI.WAU.B.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:20.366272+00:00
-- url     : https://prove2.me/submissions/66fe3063-e343-46f4-b234-b3f7ae0c3ae3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Theorems.Thm_PI_WAU_B_fmat_inv_mul
import Theorems.Thm_PI_WAU_B_fmat_mul_inv
import Theorems.Thm_PI_WAU_B_half
import Theorems.Thm_PI_WAU_B_mulVec_lam


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct
variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)
namespace PI.WAU.B
theorem _root_.solution (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y) :
    y⁻¹ * x ∈ I.Kset := by
  show ∀ w, w ∈ I.Lf ↔
    (((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _) *ᵥ w ∈ I.Lf
  have hco : (((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _) =
      I.fmat y⁻¹ * I.fmat x := rfl
  intro w
  rw [hco]
  constructor
  · intro hw
    exact mulVec_lam hm hgen _ (half I m hm hgen hx hy he) hw
  · intro hw
    have h2 := mulVec_lam hm hgen _ (half I m hm hgen hy hx he.symm) hw
    have h1 : I.fmat x⁻¹ * I.fmat y * (I.fmat y⁻¹ * I.fmat x) = 1 := by
      rw [mul_assoc, ← mul_assoc (I.fmat y), fmat_mul_inv, one_mul, fmat_inv_mul]
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h2
end PI.WAU.B
