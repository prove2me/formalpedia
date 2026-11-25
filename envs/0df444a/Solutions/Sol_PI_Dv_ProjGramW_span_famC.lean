-- Prove2me | solution 1 for PI.Dv.ProjGramW.span_famC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:09.855108+00:00
-- url     : https://prove2.me/submissions/3fc02400-12a9-4b4e-b3fd-557ecce49be0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_famC_mul
import Theorems.Thm_PI_Dv_ProjGramW_famC_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
namespace PI.Dv.ProjGramW
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    Submodule.span K (Set.range (famC b C)) = Submodule.span K (Set.range b) := by
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have e : b j = famC (famC b C) C⁻¹ j := by
      rw [famC_mul, Matrix.mul_nonsing_inv C hCu, famC_one]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end PI.Dv.ProjGramW
