-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.channel_zero_frequency
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T18:03:08.464585+00:00
-- url     : https://prove2.me/submissions/9e7ba8a0-a9f0-42b8-9c1e-d5e1dbda936c

import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_nonzero_frequency
import Theorems.Thm_QEC_Semantics_Davies_sum_frequencyComponent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24

theorem solution (A : Op S n) :
    channel S n (Davies.actualFrequency (hamiltonian S (n+2))
      (CSSGibbs.hamiltonian_symmetric _ _) A 0) = channel S n A := by
  let b := Davies.hamiltonianBasis (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _)
  let e := Davies.hamiltonianEnergies (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _)
  let : Nonempty (Fin (Module.finrank ℂ (Register S n))) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  let i : Fin (Module.finrank ℂ (Register S n)) := Classical.choice inferInstance
  let w : Davies.Frequency e := ⟨0, (Davies.mem_frequencies e 0).mpr ⟨i,i,sub_self _⟩⟩
  have hs := congrArg (channel S n) (Davies.sum_frequencyComponent b e A)
  rw [map_sum, Finset.sum_eq_single w] at hs
  · exact hs
  · intro v _ hv
    apply channel_nonzero_frequency
    intro hz
    exact hv (Subtype.ext hz)
  · simp
