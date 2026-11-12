-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:33:43.515819+00:00
-- url     : https://prove2.me/submissions/8ddda09e-78f2-4007-9e55-f19d980dc7d5

import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisObservable_adjoint
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem solution {q : Nat} (a : OddRow q)
    (outcome : StabilizerOutcome) :
    LinearMap.adjoint (logicalABasisProjector a outcome) =
      logicalABasisProjector a outcome := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold logicalABasisProjector
  apply LinearMap.IsSymmetric.smul
  · have hreal : starRingEnd Complex ((2 : Complex)⁻¹) =
        (2 : Complex)⁻¹ := by
      rw [map_inv₀]
      have htwo : starRingEnd Complex (2 : Complex) = 2 :=
        map_natCast (starRingEnd Complex) 2
      rw [htwo]
    simpa only [one_div] using hreal
  · apply LinearMap.IsSymmetric.add
    · exact LinearMap.IsSymmetric.one
    · apply LinearMap.IsSymmetric.smul
      · cases outcome <;> simp [StabilizerOutcome.sign]
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact logicalABasisObservable_adjoint a