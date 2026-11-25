-- Prove2me | solution 1 for PI.Dv.Tr.ge_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:28.729983+00:00
-- url     : https://prove2.me/submissions/6ca2dd94-e594-428a-b948-a3c175362380

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFiniteOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Theorems.Thm_PI_Dv_Tr_chi_norm
import Theorems.Thm_PI_Dv_Tr_ge_apply
import Theorems.Thm_P2M_PI_Dv_Tr_normAt_smul__30a616144aad
import Theorems.Thm_P2M_PI_Dv_Tr_normAt_sum_le__185993638e0c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ)
    (s : T.S) (v : InfinitePlace K) (x : A.V) :
    Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x) ≤
      ((Fintype.card G : ℝ) * ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ))) *
        Formalism.HermitianLatticesTheory.normAt A.b A.X v x := by
  rw [ge_apply]
  refine (normAt_sum_le' A.b A.X v _ _).trans ?_
  have hterm : ∀ y : G, Formalism.HermitianLatticesTheory.normAt A.b A.X v
      ((((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) • ρ y x) ≤
      ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) * Formalism.HermitianLatticesTheory.normAt A.b A.X v x := by
    intro y
    rw [normAt_smul', hA.2.2]
    exact mul_le_mul_of_nonneg_right (chi_norm T s y⁻¹ v.embedding) (Real.sqrt_nonneg _)
  refine (Finset.sum_le_sum fun y _ => hterm y).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring
end PI.Dv.Tr
