-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.gibbs_eq_thermal_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:06:57.471732+00:00
-- url     : https://prove2.me/submissions/c713ab39-3b6d-40d7-a7bf-ebfd09f8d036

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_dressed_commute_hamiltonian
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Semantics_Davies_hamiltonianGibbs_eq_physicalGibbsState
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_physicalGibbsState_eq_thermalReferenceState

section
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
private theorem H_commutes_X : Commute (hamiltonian S (n+2)) (dressedPauliPair S n).x :=
  (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))).symm
end QEC.Coding.BDL26PairedDecoderGibbs
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_416
namespace QEC.Coding.BDL26PairedDecoderGibbs
theorem _root_.solution (beta : ℝ) :
    gibbs S (n+2) beta = (dressedPauliPair S n).thermalReferenceState (auxiliaryGibbs S n beta) := by
  apply DensityOperator.ext_toOperator
  have h := Davies.hamiltonianGibbs_eq_physicalGibbsState (dressedPauliPair S n)
    (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _)
    (H_commutes_X S n) (H_commutes_Z S n) beta
  exact h.trans (congrArg DensityOperator.toOperator
    ((dressedPauliPair S n).physicalGibbsState_eq_thermalReferenceState
      (hamiltonian S (n+2)) (H_commutes_Z S n) (CSSGibbs.hamiltonian_symmetric _ _) beta))
end QEC.Coding.BDL26PairedDecoderGibbs
