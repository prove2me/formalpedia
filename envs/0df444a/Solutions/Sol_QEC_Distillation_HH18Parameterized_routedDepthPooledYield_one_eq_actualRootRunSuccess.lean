-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPooledYield_one_eq_actualRootRunSuccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:59:21.293796+00:00
-- url     : https://prove2.me/submissions/a02ce053-4919-4a30-83ad-879f50389633

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthOutputSlots_card_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_eq_sum_div_card
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathYieldFactor_one_eq_actualRootRunSuccess

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (routedDepthPooledYield h hdegree epsilon hsmall 1 : ℝ) =
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).successProbability := by
  classical
  rw [routedDepthPooledYield_eq_sum_div_card]
  simp_rw [routedDepthPathYieldFactor_one_eq_actualRootRunSuccess h hdegree epsilon hsmall]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (routedDepthOutputSlots m w 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (routedDepthOutputSlots_card_pos m w 1)
  field_simp [hcard]
end QEC.Distillation.HH18Parameterized
