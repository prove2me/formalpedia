-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.finrank_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:59.76064+00:00
-- url     : https://prove2.me/submissions/2d296420-745e-4813-80ce-096388aa2b1b

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_algebraMap_eq_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_evRing_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_ker_evRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_le_ptIdeal_of_nontrivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ} (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) [IsLocalRing (locR K p)]
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
theorem _root_.solution : Module.finrank ℂ (ResidueField (locR K p)) = 1 := by
  have hK : K ≤ ptI p := le_ptIdeal_of_nontrivial (K := K) (p := p)
  rw [finrank_eq_one_iff_of_nonzero' (1 : ResidueField (locR K p)) one_ne_zero]
  intro w
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective w
  refine ⟨evRing K hK x, ?_⟩
  rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply ℂ (locR K p) (ResidueField (locR K p)),
    IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ker_evRing (K := K) (p := p) hK, RingHom.mem_ker, map_sub, algebraMap_eq_psi, evRing_psi, eval_C,
    sub_self]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
