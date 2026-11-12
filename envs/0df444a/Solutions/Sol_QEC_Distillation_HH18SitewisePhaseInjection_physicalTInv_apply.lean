-- Prove2me | solution 1 for QEC.Distillation.HH18SitewisePhaseInjection.physicalTInv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:30:47.205454+00:00
-- url     : https://prove2.me/submissions/b2d2f052-5ef6-42e8-95c9-2f70408f78c4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_physicalT_eq_allSiteT
import Theorems.Thm_QEC_Distillation_Triorthogonal_allSiteT_apply


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SitewisePhaseInjection
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
namespace QEC.Distillation.HH18SitewisePhaseInjection
theorem _root_.solution (psi : QubitRegister PhysicalSite)
    (bits : Bitstring PhysicalSite) :
    HH18PuncturedReedMuller.physicalTInv 0 4 psi bits =
      OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
        psi bits := by
  have hinverse :
      HH18PuncturedReedMuller.physicalT 0 4
          (HH18PuncturedReedMuller.physicalTInv 0 4 psi) = psi := by
    change (HH18PuncturedReedMuller.physicalT 0 4).toLinearEquiv
      ((HH18PuncturedReedMuller.physicalT 0 4).toLinearEquiv.symm psi) = psi
    exact (HH18PuncturedReedMuller.physicalT 0 4).toLinearEquiv.apply_symm_apply psi
  have hcoordinate :=
    congrArg (fun state : QubitRegister PhysicalSite => state bits) hinverse
  rw [HH18PuncturedReedMuller.physicalT_eq_allSiteT] at hcoordinate
  change Triorthogonal.allSiteT
      (HH18PuncturedReedMuller.physicalTInv 0 4 psi) bits = psi bits
    at hcoordinate
  rw [Triorthogonal.allSiteT_apply] at hcoordinate
  calc
    HH18PuncturedReedMuller.physicalTInv 0 4 psi bits =
        OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle *
              (HammingWeight
                (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
          (OneQubitMagic.phaseAmplitude
              (Real.pi / 4 *
                (HammingWeight
                  (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
            HH18PuncturedReedMuller.physicalTInv 0 4 psi bits) := by
              rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
              have hangle :
                  HH18PhaseInjection.tInvIdealAngle *
                        (HammingWeight
                          (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real) +
                      Real.pi / 4 *
                        (HammingWeight
                          (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real) =
                    0 := by
                unfold HH18PhaseInjection.tInvIdealAngle
                ring
              rw [hangle, OneQubitMagic.phaseAmplitude_zero, one_mul]
    _ = OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
        psi bits := by rw [hcoordinate]
end QEC.Distillation.HH18SitewisePhaseInjection
