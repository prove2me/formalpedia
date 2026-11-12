-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.z_family_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:02:04.500847+00:00
-- url     : https://prove2.me/submissions/72ea0a74-32f6-48ac-9752-fdb616856fd8

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_z_selected_trace

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype
namespace QEC.Coding.BDL26CoboundaryContainment
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n (zFamily S n W)) =
      ((pZ S n β (zFamily S n W) : ℝ) : ℂ) := z_selected_trace S n β _
end QEC.Coding.BDL26CoboundaryContainment
