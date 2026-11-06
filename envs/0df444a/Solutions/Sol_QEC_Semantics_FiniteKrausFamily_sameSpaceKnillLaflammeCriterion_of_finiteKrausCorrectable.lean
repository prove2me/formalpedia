-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:48:15.36319+00:00
-- url     : https://prove2.me/submissions/5896478f-7d05-4ff7-a4e2-8de712590f3b

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_of_recovery_branch_scalar
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_branch_scalar_of_finiteKraus_correctedBy
import Theorems.Thm_QEC_Semantics_QuantumChannel_exists_finiteKrausFamily_representation


set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (recovery : QuantumChannel H H)
    (h : FiniteKrausCorrectable ι H H C E recovery) :
    E.sameSpaceKnillLaflammeCriterion C := by
  classical
  rcases h with ⟨_hE_complete, hcorrected⟩
  rcases QuantumChannel.exists_finiteKrausFamily_representation recovery with
    ⟨m, R, hR_complete, hR_map⟩
  have hcorrect_finite : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : Fin m, (R.operator r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R.operator r)))) =
        rho.toOperator := by
    intro rho hρ
    calc
      (∑ r : Fin m, (R.operator r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R.operator r))))
          = R.inducedMap (E.inducedMap rho.toOperator) := by
            exact (FiniteKrausFamily.inducedMap_apply R
              (E.inducedMap rho.toOperator)).symm
      _ = recovery.toLinearMap (E.inducedMap rho.toOperator) := by
            rw [hR_map]
      _ = rho.toOperator := hcorrected rho hρ
  rcases exists_recovery_branch_scalar_of_finiteKraus_correctedBy
      E C R.operator hR_complete hcorrect_finite with
    ⟨branchScalar, hbranch⟩
  exact sameSpaceKnillLaflammeCriterion_of_recovery_branch_scalar
    E C R.operator hR_complete branchScalar hbranch
end QEC.Semantics.FiniteKrausFamily
