-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.actual_ground_energy_projector
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T15:31:12.742549+00:00
-- url     : https://prove2.me/submissions/f5c3f331-d774-46c4-a772-93a4771b026c

import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_actual_energy_projector
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_syndromeEnergy_ground_iff
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
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

theorem solution :
    Davies.hamiltonianEnergyProjector (hamiltonian S (n+2))
      (CSSGibbs.hamiltonian_symmetric _ _) (groundEnergy S n) = groundProjector S n := by
  rw [actual_energy_projector, groupedEnergyProjector]
  simp only [syndromeEnergy_ground_iff]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, atom_zero]
