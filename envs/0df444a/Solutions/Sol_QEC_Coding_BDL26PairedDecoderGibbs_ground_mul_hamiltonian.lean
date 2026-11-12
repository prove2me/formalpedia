-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.ground_mul_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:13:02.221328+00:00
-- url     : https://prove2.me/submissions/bccef9be-8718-4be9-aba0-0fb37f5fe1f0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_atom_mul_hamiltonian
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_syndromeEnergy_ground_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24
namespace QEC.Coding.BDL26PairedDecoderGibbs
theorem _root_.solution :
    groundProjector S n * hamiltonian S (n+2) =
      (groundEnergy S n : ℂ) • groundProjector S n := by
  have h := atom_mul_hamiltonian S n (zeroVisible S n)
  rw [atom_zero] at h
  have hz := (syndromeEnergy_ground_iff S n (zeroVisible S n)).mpr rfl
  rwa [hz] at h
end QEC.Coding.BDL26PairedDecoderGibbs
