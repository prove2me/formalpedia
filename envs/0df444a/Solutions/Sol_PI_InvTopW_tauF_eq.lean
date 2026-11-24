-- Prove2me | solution 1 for PI.InvTopW.tauF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:02:58.224873+00:00
-- url     : https://prove2.me/submissions/a95386fa-ca0f-4358-bbba-543a383a9b23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Theorems.Thm_PI_InvTopW_sum_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
variable (I : AutInst)
namespace PI.InvTopW
theorem _root_.solution (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    tauF I t = ∑ k, basisE I k ⊗ₜ[I.F] (coord I k t).2 := by
  conv_lhs => rw [← sum_coord I t]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show (1 : I.E) ⊗ₜ[I.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F (coord I k t) *
      (basisE I k ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl
end PI.InvTopW
