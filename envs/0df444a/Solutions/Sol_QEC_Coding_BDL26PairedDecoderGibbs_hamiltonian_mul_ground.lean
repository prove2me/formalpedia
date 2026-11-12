-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.hamiltonian_mul_ground
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:09:52.404333+00:00
-- url     : https://prove2.me/submissions/fc048945-d64e-4d8a-a8c8-11915680f6fc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_hamiltonian_mul_atom
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
    hamiltonian S (n+2) * groundProjector S n =
      (groundEnergy S n : ℂ) • groundProjector S n := by
  have h := hamiltonian_mul_atom S n (zeroVisible S n)
  rw [atom_zero] at h
  have hz := (syndromeEnergy_ground_iff S n (zeroVisible S n)).mpr rfl
  rwa [hz] at h
end QEC.Coding.BDL26PairedDecoderGibbs
