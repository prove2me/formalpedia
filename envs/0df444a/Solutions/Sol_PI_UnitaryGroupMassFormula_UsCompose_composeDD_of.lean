-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.composeDD_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:54.928923+00:00
-- url     : https://prove2.me/submissions/af5ed070-f562-49fb-8219-0acd5a21dde9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_bd_steps
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_toFS
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_opApply_mk
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_inDD_mk
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_shape_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_shape_flatMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution (hP : DegDP) (hD : DegD) (hE : Expand) : ComposeDD := by
  intro k j ρ Wp Wq _ _ _ _ _ o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ h₁ h₂
  obtain ⟨L₁, hB₁, hE₁⟩ := toFS h₁
  obtain ⟨L₂, hB₂, hE₂⟩ := toFS h₂
  set L : FS k (j + ρ) :=
    L₁.flatMap fun e₁ => (steps k j ρ e₁.2 L₂).map fun e => (mulSC e₁.1 e.1, e.2) with hLdef
  have hB : Bd k j ρ (κ₁ + κ₂ + j * o₁) (o₁ + o₂) L := by
    intro e he
    rw [hLdef, List.mem_flatMap] at he
    obtain ⟨e₁, he₁, he⟩ := he
    rw [List.mem_map] at he
    obtain ⟨e₂, he₂, rfl⟩ := he
    obtain ⟨d₁, l₁, lie₁⟩ := hB₁ e₁ he₁
    obtain ⟨d₂, l₂, lie₂⟩ := bd_steps hP hD lie₁ hB₂ e₂ he₂
    refine ⟨?_, ?_, lie₂⟩
    · calc (e₁.1.1 * e₂.1.1).totalDegree ≤ e₁.1.1.totalDegree + e₂.1.1.totalDegree :=
            totalDegree_mul _ _
        _ ≤ κ₁ + (κ₂ + j * o₁) :=
            Nat.add_le_add d₁ (d₂.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ l₁) _))
        _ = κ₁ + κ₂ + j * o₁ := by ring
    · show e₂.2.length ≤ o₁ + o₂
      omega
  refine ⟨L.map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ), inDD_mk L hB, ?_⟩
  intro F hF g hg hDg
  rw [opApply_mk L (fun e he => (hB e he).2.2) F g, hE₁]
  have hfun : opApply Θ₂ F = shape k j ρ F L₂ := funext (hE₂ F)
  rw [hfun, hLdef, shape_flatMap]
  show _ = (L₁.map fun e => sv k j ρ e.1 g • Rw e.2 (shape k j ρ F L₂) g).sum
  congr 1
  apply List.map_congr_left
  intro e₁ he₁
  rw [shape_mul, hE k j ρ _ (o₁ + o₂) F hF e₁.2 L₂ (hB₁ e₁ he₁).2.2 (fun e he => (hB₂ e he).2.2)
    (fun e he => by have := (hB₂ e he).2.1; have := (hB₁ e₁ he₁).2.1; omega) g hg hDg]
end PI.UnitaryGroupMassFormula.UsCompose
