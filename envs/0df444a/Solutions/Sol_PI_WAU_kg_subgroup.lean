-- Prove2me | solution 1 for PI.WAU.kg_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:24.885235+00:00
-- url     : https://prove2.me/submissions/3bb213e5-cd70-46d6-8290-6101e6a6e0d0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionA
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct Matrix
namespace PI.WAU
theorem _root_.solution : KgSubgroup := by
  intro I g _hg
  have stab : ∀ a : I.Gf, a ∈ I.Kset → ∀ x, x ∈ I.Lf ↔ I.fmat a *ᵥ x ∈ I.Lf := fun a ha => ha
  have kset_mul : ∀ a b : I.Gf, a ∈ I.Kset → b ∈ I.Kset → a * b ∈ I.Kset := by
    intro a b ha hb
    show ((a * b : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_mul]
    exact Subgroup.mul_mem _ ha hb
  have kset_inv : ∀ a : I.Gf, a ∈ I.Kset → a⁻¹ ∈ I.Kset := by
    intro a ha
    show ((a⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_inv]
    exact Subgroup.inv_mem _ ha
  have fmat_mul : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := by
    intro a b
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have fmat_inv_mul : ∀ a : I.Gf, I.fmat a⁻¹ * I.fmat a = 1 := by
    intro a
    simp [Formalism.MainNotions.S.AutInst.fmat]
  refine ⟨{ carrier := I.Kg g, one_mem' := ?one, mul_mem' := ?mul, inv_mem' := ?inv }, rfl⟩
  case one =>
    refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · show ((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
      rw [OneMemClass.coe_one]
      exact Subgroup.one_mem _
    · simp [Formalism.MainNotions.S.AutInst.fmat]
  case mul =>
    intro a b ha hb
    obtain ⟨haK, haL⟩ := ha
    obtain ⟨hbK, hbL⟩ := hb
    refine ⟨kset_mul a b haK hbK, fun y hy => ?_⟩
    obtain ⟨z1, hz1, e1⟩ := hbL y hy
    obtain ⟨z2, hz2, e2⟩ := haL y hy
    refine ⟨I.fmat a *ᵥ z1 + z2, Submodule.add_mem _ ((stab a haK z1).mp hz1) hz2, ?_⟩
    calc (I.fmat (a * b) - 1) *ᵥ y
        = I.fmat a *ᵥ ((I.fmat b - 1) *ᵥ y) + (I.fmat a - 1) *ᵥ y := by
          rw [fmat_mul, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one]
          simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
          abel
      _ = I.fmat a *ᵥ ((g : I.E ⊗[I.F] Af I.F) • z1) + (g : I.E ⊗[I.F] Af I.F) • z2 := by rw [e1, e2]
      _ = (g : I.E ⊗[I.F] Af I.F) • (I.fmat a *ᵥ z1 + z2) := by rw [Matrix.mulVec_smul, smul_add]
  case inv =>
    intro a ha
    obtain ⟨haK, haL⟩ := ha
    refine ⟨kset_inv a haK, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := haL y hy
    refine ⟨-(I.fmat a⁻¹ *ᵥ z), Submodule.neg_mem _ ((stab a⁻¹ (kset_inv a haK) z).mp hz), ?_⟩
    calc (I.fmat a⁻¹ - 1) *ᵥ y = -(I.fmat a⁻¹ *ᵥ ((I.fmat a - 1) *ᵥ y)) := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_sub, fmat_inv_mul, Matrix.mul_one, Matrix.sub_mulVec,
            Matrix.sub_mulVec, Matrix.one_mulVec, neg_sub]
      _ = (g : I.E ⊗[I.F] Af I.F) • -(I.fmat a⁻¹ *ᵥ z) := by
          rw [e, Matrix.mulVec_smul, smul_neg]
end PI.WAU
