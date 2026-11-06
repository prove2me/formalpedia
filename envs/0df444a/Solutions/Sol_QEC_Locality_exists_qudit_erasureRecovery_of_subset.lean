-- Prove2me | solution 1 for QEC.Locality.exists_qudit_erasureRecovery_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:02:22.872309+00:00
-- url     : https://prove2.me/submissions/662a2745-a964-4828-bc7f-252e356a76b0

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecoverableFromRegister_mono


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {q : ι → Nat} (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (C : QuantumCode (Qudit.QuditRegister q))
    (hRecovery : ∃ recovery : QuantumChannel T.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) T.complementSystem C
        T.erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  exact QuditSubsystem.erasureRecoverableFromRegister_mono S T hST C hRecovery
end QEC.Locality
