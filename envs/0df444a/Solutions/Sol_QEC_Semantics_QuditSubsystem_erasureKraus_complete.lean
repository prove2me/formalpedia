-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureKraus_complete
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:01:56.546712+00:00
-- url     : https://prove2.me/submissions/2a555945-75cd-480d-9d48-9e48ed1bbc14

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_one_reference
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem solution (S : QuditSubsystem q) :
    (S.erasureKraus).Complete := by
  let b := stdOrthonormalBasis Complex S.selectedSystem
  have hfactorized : S.erasureFactorizedKraus.Complete := by
    rw [FiniteKrausFamily.Complete]
    calc
      ∑ a, (LinearMap.adjoint (S.erasureFactorizedKraus.operator a)).comp
          (S.erasureFactorizedKraus.operator a) =
          ∑ a, S.extendLocal (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro a _
            simpa only [erasureFactorizedKraus, LinearMap.adjoint_adjoint] using
              S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
                (b a) (b a)
      _ = S.extendLocal (∑ a,
          (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap) := by
            symm
            unfold QuditSubsystem.extendLocal
            induction (Finset.univ : Finset (Fin (Module.finrank Complex S.selectedSystem)))
                using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
                rw [Finset.sum_insert ha, TensorProduct.map_add_left, ih,
                  Finset.sum_insert ha]
      _ = S.extendLocal 1 := by
            congr 1
            simpa [Module.End.one_eq_id] using congrArg ContinuousLinearMap.toLinearMap
              (OrthonormalBasis.sum_rankOne_eq_id b)
      _ = 1 := S.extendLocal_one_reference
  change (S.erasureFactorizedKraus.unitaryTransport S.registerFactorization.symm
    (identityTransport S.complementSystem)).Complete
  exact S.erasureFactorizedKraus.unitaryTransport_complete S.registerFactorization.symm
    (identityTransport S.complementSystem) hfactorized
