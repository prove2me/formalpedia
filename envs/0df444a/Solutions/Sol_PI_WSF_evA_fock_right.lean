-- Prove2me | solution 1 for PI.WSF.evA_fock_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:25.03209+00:00
-- url     : https://prove2.me/submissions/80518325-1c70-4fc5-9b20-06097ca1134c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory
namespace PI.WSF
theorem _root_.solution {σ : Type*} (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f g = ∑ m ∈ g.support,
      f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  classical
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support),
    Finset.sum_subset (Finset.subset_union_right : g.support ⊆ f.support ∪ g.support)]
  · intro m _ hm
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]
  · intro m _ hm
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]
end PI.WSF
