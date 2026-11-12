-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.channel_raw_projector
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T18:03:09.076346+00:00
-- url     : https://prove2.me/submissions/f6c41336-a1bb-40ad-9d5d-1ee735a7afc7

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

theorem solution
    (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2)))) :
    channel S n (projector S (n+2) w) =
      if w ∈ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2))
      then groundProjector S n else 0 := by
  by_cases hw : w ∈ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2))
  · rw [if_pos hw]
    obtain ⟨s, _, hs⟩ := Finset.mem_map.mp hw
    rw [← hs]
    exact channel_atom S n s
  · rw [if_neg hw]
    have hz : projector S (n+2) w = 0 :=
      CSSGibbs.projector_eq_zero_of_not_realizable _ _ (row_orthogonal S (n+2)) w hw
    rw [hz, map_zero]
