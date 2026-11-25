-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.scU_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:21.050162+00:00
-- url     : https://prove2.me/submissions/e5ff7a6d-8580-4dfb-8aa6-3bf8e02c0a82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Theorems.Thm_PI_UnitaryApproxFinWork_cT_smul_one
import Theorems.Thm_PI_UnitaryApproxFinWork_scU_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {n : Type} [Fintype n] [DecidableEq n]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {A : Type} [CommRing A] (ρ : A →+* A) (J : Matrix n n A) (a b : A) (h : a * b = 1)
    (hρ : ρ a * a = 1) : scU (n := n) a b h ∈ PI.UnitaryApproxDefs.UJ ρ J := by
  show PI.UnitaryApproxDefs.cT ρ ((scU (n := n) a b h : GL n A) : Matrix n n A) * J *
    ((scU (n := n) a b h : GL n A) : Matrix n n A) = J
  rw [scU_val, cT_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    mul_comm, hρ, one_smul]
end PI.UnitaryApproxFinWork
