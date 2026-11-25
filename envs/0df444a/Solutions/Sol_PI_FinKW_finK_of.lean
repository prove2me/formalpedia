-- Prove2me | solution 1 for PI.FinKW.finK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:25.242501+00:00
-- url     : https://prove2.me/submissions/3e88b07b-c87e-4928-9642-f794d8b563c5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_VecVMulVec
import Theorems.Thm_PI_FinKW_vecV_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge
namespace PI.FinKW
theorem _root_.solution (hT : MemLocTo) (hF : MemLocFrom) (hS : LiftV) : PI.AdBridgeSteps.FinK := by
  intro I h
  have hL : ∀ x, x ∈ I.Lf ↔ ∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x => ⟨hT I x, hF I x⟩
  constructor
  · intro hst v y
    obtain ⟨x, hxv, hxw⟩ := hS I v y
    have ex : x ∈ I.Lf ↔ y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL x]
      constructor
      · intro H
        have := H v
        rwa [hxv] at this
      · intro H w
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw]
          exact zero_mem _
    have egx : ofHAFin I h *ᵥ x ∈ I.Lf ↔
        ((Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) :
            GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) *ᵥ y ∈
          Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL]
      constructor
      · intro H
        have := H v
        rwa [vecV_mulVec, hxv] at this
      · intro H w
        rw [vecV_mulVec]
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw, Matrix.mulVec_zero]
          exact zero_mem _
    exact ex.symm.trans ((hst x).trans egx)
  · intro hK x
    rw [hL x, hL (ofHAFin I h *ᵥ x)]
    refine forall_congr' fun v => ?_
    rw [vecV_mulVec]
    exact hK v (vecV I v x)
end PI.FinKW
