-- Prove2me | solution 1 for PI.WGL.glRel_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:58.546636+00:00
-- url     : https://prove2.me/submissions/fbf9f649-dba0-40e2-a3e7-43cd50f9beda

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (c : ℂ) :
    Formalism.REAL.GlRel (fun a b => E a b + if a = b then algebraMap ℂ A c else 0) := by
  have key : ∀ (p : Prop) [Decidable p] (y : A),
      (if p then algebraMap ℂ A c else 0) * y = y * (if p then algebraMap ℂ A c else 0) := by
    intro p _ y
    split_ifs
    · exact Algebra.commutes c y
    · simp
  intro i j k l
  simp only
  have h1 := key (i = j) (E k l)
  have h2 := key (k = l) (E i j)
  have h3 := key (i = j) (if k = l then algebraMap ℂ A c else 0)
  calc (E i j + if i = j then algebraMap ℂ A c else 0) * (E k l + if k = l then algebraMap ℂ A c else 0) -
        (E k l + if k = l then algebraMap ℂ A c else 0) * (E i j + if i = j then algebraMap ℂ A c else 0)
      = (E i j * E k l - E k l * E i j)
        + ((if i = j then algebraMap ℂ A c else 0) * E k l - E k l * (if i = j then algebraMap ℂ A c else 0))
        - ((if k = l then algebraMap ℂ A c else 0) * E i j - E i j * (if k = l then algebraMap ℂ A c else 0))
        + ((if i = j then algebraMap ℂ A c else 0) * (if k = l then algebraMap ℂ A c else 0)
          - (if k = l then algebraMap ℂ A c else 0) * (if i = j then algebraMap ℂ A c else 0)) := by
        noncomm_ring
    _ = E i j * E k l - E k l * E i j := by rw [h1, h2, h3]; abel
    _ = (if j = k then E i l else 0) - (if l = i then E k j else 0) := hE i j k l
    _ = _ := by
        by_cases hjk : j = k <;> by_cases hli : l = i
        · subst hjk; subst hli; simp
        · have hil : ¬ i = l := fun h => hli h.symm
          simp [hjk, hli, hil]
        · have hkj : ¬ k = j := fun h => hjk h.symm
          simp [hjk, hli, hkj]
        · simp [hjk, hli]
end PI.WGL
