-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.mem_cssCarrier_iff_checkGenerator_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:38:45.012655+00:00
-- url     : https://prove2.me/submissions/16a7eab3-0809-4066-9a46-da875d1bf7af

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Theorems.Thm_QEC_Coding_PauliSymplectic_fixed_generatedStabilizer_iff_fixed_generators


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PuncturedReedMuller
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18PuncturedReedMuller
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (PhysicalSite m w)) :
    psi ∈ (cssCode h).stabilizer.code.carrier ↔
      ∀ check, toQubitOperator (checkGenerator w r m check) psi = psi := by
  rcases binaryCSSStabilizerCodeOfParityChecks_spec
      (zParityCheck w r m) (xParityCheck w r m)
      (parityCheckRows_orthogonal h) with
    ⟨_hchecks, hgenerated, _hsign, _hcommutes, hfixed⟩
  calc
    psi ∈ (cssCode h).stabilizer.code.carrier ↔
        ∀ S, S ∈ (stabilizer h).generatedGroup →
          toQubitOperator S psi = psi := hfixed psi
    _ ↔ ∀ S, GeneratedStabilizer (checkGenerator w r m) S →
          toQubitOperator S psi = psi := by
      change
        (∀ S, S ∈
            (binaryCSSStabilizerCodeOfParityChecks
              (zParityCheck w r m) (xParityCheck w r m)
              (parityCheckRows_orthogonal h)).generatedGroup →
            toQubitOperator S psi = psi) ↔
          ∀ S, GeneratedStabilizer (checkGenerator w r m) S →
            toQubitOperator S psi = psi
      rw [← hgenerated]
      rfl
    _ ↔ ∀ check, toQubitOperator (checkGenerator w r m check) psi = psi :=
      fixed_generatedStabilizer_iff_fixed_generators (checkGenerator w r m) psi
end QEC.Distillation.HH18PuncturedReedMuller
