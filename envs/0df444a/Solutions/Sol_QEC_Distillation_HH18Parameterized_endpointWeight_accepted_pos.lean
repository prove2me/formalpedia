-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.endpointWeight_accepted_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:13:26.144357+00:00
-- url     : https://prove2.me/submissions/e4b94b9a-7bbc-4a9c-8325-c3997a970c6e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_eq_acceptedBernoulliMass


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < endpointWeight h hdegree (noisyResources m w epsilon) .accepted := by
  rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  exact acceptedBernoulliMass_pos h epsilon
end QEC.Distillation.HH18Parameterized
