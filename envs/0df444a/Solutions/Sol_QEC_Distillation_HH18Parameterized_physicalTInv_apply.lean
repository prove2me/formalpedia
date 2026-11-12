-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.physicalTInv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:35:23.080168+00:00
-- url     : https://prove2.me/submissions/30a47380-78d9-4645-b0ae-9a701967dfe7

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_physicalT_eq_allSiteT
import Theorems.Thm_QEC_Distillation_Triorthogonal_allSiteT_apply


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (m w : Nat) (psi : PhysicalRegister m w)
    (bits : Bitstring (PhysicalSite m w)) :
    HH18PuncturedReedMuller.physicalTInv w m psi bits =
      OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
        psi bits := by
  have hinverse :
      HH18PuncturedReedMuller.physicalT w m
          (HH18PuncturedReedMuller.physicalTInv w m psi) = psi := by
    change (HH18PuncturedReedMuller.physicalT w m).toLinearEquiv
      ((HH18PuncturedReedMuller.physicalT w m).toLinearEquiv.symm psi) = psi
    exact (HH18PuncturedReedMuller.physicalT w m).toLinearEquiv.apply_symm_apply psi
  have hcoordinate :=
    congrArg (fun state : PhysicalRegister m w => state bits) hinverse
  rw [HH18PuncturedReedMuller.physicalT_eq_allSiteT] at hcoordinate
  change Triorthogonal.allSiteT
      (HH18PuncturedReedMuller.physicalTInv w m psi) bits = psi bits
    at hcoordinate
  rw [Triorthogonal.allSiteT_apply] at hcoordinate
  calc
    HH18PuncturedReedMuller.physicalTInv w m psi bits =
        OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle *
              (HammingWeight
                (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
          (OneQubitMagic.phaseAmplitude
              (Real.pi / 4 *
                (HammingWeight
                  (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
            HH18PuncturedReedMuller.physicalTInv w m psi bits) := by
              rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
              have hangle :
                  HH18PhaseInjection.tInvIdealAngle *
                        (HammingWeight
                          (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real) +
                      Real.pi / 4 *
                        (HammingWeight
                          (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real) =
                    0 := by
                unfold HH18PhaseInjection.tInvIdealAngle
                ring
              rw [hangle, OneQubitMagic.phaseAmplitude_zero, one_mul]
    _ = OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
        psi bits := by rw [hcoordinate]
end QEC.Distillation.HH18Parameterized
