-- Prove2me | solution 1 for PI.Dv.Tr.epsSum_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:06.792974+00:00
-- url     : https://prove2.me/submissions/a3d9359b-c254-4c2e-ad99-f05f7d885b66

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
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_MemRangeIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSLat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PI_Dv_Tr_normAt_smul__30a616144aad
import Theorems.Thm_P2M_PI_Dv_Tr_normAt_sum_le__185993638e0c
import Theorems.Thm_PI_Dv_Tr_chi_pow
import Theorems.Thm_PI_Dv_Tr_phi_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
open Classical
namespace PI.Dv.Tr
theorem _root_.solution (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ) (Q : Pair K G) (g : G)
    (v : InfinitePlace K) (y : A.V) :
    Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ.asAlgebraHom (epsSum Q * MonoidAlgebra.of K G g) y) ≤
      (Fintype.card Q.H : ℝ) * Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
  rw [phi_apply]
  refine (normAt_sum_le' A.b A.X v _ _).trans (le_of_eq ?_)
  have hterm : ∀ h : Q.H, Formalism.HermitianLatticesTheory.normAt A.b A.X v ((((Q.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y)) =
      Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
    intro h
    rw [normAt_smul', hA.2.2, hA.2.2]
    have hn : ‖v.embedding ((((Q.chi h)⁻¹ : Kˣ) : K))‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, chi_pow, map_one]) Fintype.card_ne_zero
    rw [hn, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end PI.Dv.Tr
