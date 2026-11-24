-- Prove2me | solution 1 for PI.FJMS.gR_pos_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:23.64357+00:00
-- url     : https://prove2.me/submissions/bfb9443b-7b2b-493b-b305-01718e3387d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Theorems.Thm_PI_FJMS_sum_range_emb
import Theorems.Thm_PI_FJMP_pderiv_eq_zero_of_noVar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
variable {σ κ : Type*} [Fintype κ]
namespace PI.FJMS
theorem _root_.solution {m : ℕ} (u v : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (P : MvPolynomial σ ℂ) (hA : ∀ c, c ∉ Set.range j → NoVar P (u c))
    (hB : ∀ c, c ∉ Set.range j → NoVar P (v c)) (hin : ∀ k, pos (j k) = true) :
    gR u v pos P = ∑ k, X (u (j k)) * pderiv (v (j k)) P := by
  unfold gR
  rw [sum_range_emb j hj _ (fun c hc => ?_)]
  · exact Finset.sum_congr rfl (fun k _ => by rw [if_pos (hin k)])
  · split_ifs
    · rw [pderiv_eq_zero_of_noVar (hB c hc), mul_zero]
    · rw [pderiv_eq_zero_of_noVar (hA c hc), mul_zero, neg_zero]
end PI.FJMS
