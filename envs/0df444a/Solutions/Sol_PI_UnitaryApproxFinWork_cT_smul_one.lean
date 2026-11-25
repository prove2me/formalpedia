-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.cT_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:10.847809+00:00
-- url     : https://prove2.me/submissions/b8027353-aaec-4218-9bd0-836eee229c75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral

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
theorem _root_.solution {A : Type} [CommRing A] (ρ : A →+* A) (a : A) :
    PI.UnitaryApproxDefs.cT ρ (a • (1 : Matrix n n A)) = ρ a • 1 := by
  ext i j
  simp only [PI.UnitaryApproxDefs.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]
end PI.UnitaryApproxFinWork
