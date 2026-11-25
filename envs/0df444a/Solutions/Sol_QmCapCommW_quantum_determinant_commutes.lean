-- Prove2me | solution 1 for QmCapCommW.quantum_determinant_commutes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:14.585009+00:00
-- url     : https://prove2.me/submissions/4bd23db3-527d-468b-a4bc-84f7331a725c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_QuantumDeterminantCommutes
import Theorems.Thm_Formalism_REAL_qDetCentral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open QmCapCommW
namespace QmCapCommW
theorem _root_.solution : QdetCommute := by
  intro A _ _ n E hE u v
  have hc : ∀ c d, Commute (qdet E u) (E c d) := fun c d => qDetCentral A n E hE u c d
  have hT : ∀ w a b, Commute (qdet E u) (Tm E w a b) := by
    intro w a b
    unfold Tm
    refine Commute.add_right ?_ (hc a b)
    split_ifs
    · exact Algebra.commute_algebraMap_right w _
    · exact Commute.zero_right _
  have key : Commute (qdet E u) (qdet E v) := by
    show Commute (qdet E u) (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin n => Tm E (v - (k : ℂ)) (id (σ k)) (id k)).prod)
    refine Commute.sum_right _ _ _ fun σ _ => ?_
    refine Commute.mul_right Commute.intCast_right ?_
    refine Commute.list_prod_right _ _ fun y hy => ?_
    simp only [List.mem_ofFn] at hy
    obtain ⟨k, rfl⟩ := hy
    exact hT _ _ _
  exact key.eq
end QmCapCommW
