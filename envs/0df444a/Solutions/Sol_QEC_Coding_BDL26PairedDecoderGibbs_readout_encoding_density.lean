-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.readout_encoding_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:15:55.607146+00:00
-- url     : https://prove2.me/submissions/a6a2a7eb-560d-4331-a3e1-59345156e10d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_readout_encoding
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator


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
theorem _root_.solution (beta : ℝ) (rho : DensityOperator Qubit.QubitSpace) :
    (readout S n).mapDensity ((encoding S n beta).mapDensity rho) = rho := by
  apply DensityOperator.ext_toOperator
  exact readout_encoding S n beta rho.toOperator
end QEC.Coding.BDL26PairedDecoderGibbs
