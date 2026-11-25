-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.relIdx_ne_zero_of_le_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:16.436365+00:00
-- url     : https://prove2.me/submissions/8cd1ff47-6e63-4b1c-a46c-09096f1c8c2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply
section
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
section Idx
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
private theorem relIndex_ne_zero_of_finite_cover {A B : AddSubgroup V} {ι : Type*} [Finite ι] (φ : ι → V)
    (hφ : ∀ i, φ i ∈ B) (hcov : ∀ b ∈ B, ∃ i, b - φ i ∈ A) : A.relIndex B ≠ 0 := by
  have hsurj : Function.Surjective (fun i => ((⟨φ i, hφ i⟩ : B) : B ⧸ A.addSubgroupOf B)) := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨i, hi⟩ := hcov b b.2
    refine ⟨i, ?_⟩
    show ((⟨φ i, hφ i⟩ : B) : B ⧸ A.addSubgroupOf B) = (b : B ⧸ A.addSubgroupOf B)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hi
  haveI : Finite (B ⧸ A.addSubgroupOf B) := Finite.of_surjective _ hsurj
  exact AddSubgroup.index_ne_zero_of_finite
end Idx
section Theta
variable {a : ℕ} {b c : ℤ} {d : ℕ}
end Theta
end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {A A' B : AddSubgroup V} (h : A ≤ A') (hA : A.relIndex B ≠ 0) :
    A'.relIndex B ≠ 0 := by
  haveI : Finite (B ⧸ A.addSubgroupOf B) :=
    Nat.finite_of_card_ne_zero (α := B ⧸ A.addSubgroupOf B) hA
  refine relIndex_ne_zero_of_finite_cover (ι := B ⧸ A.addSubgroupOf B) (fun q => ((q.out : B) : V))
    (fun q => q.out.2) ?_
  intro b hb
  refine ⟨((⟨b, hb⟩ : B) : B ⧸ A.addSubgroupOf B), h ?_⟩
  have e : -((((⟨b, hb⟩ : B) : B ⧸ A.addSubgroupOf B)).out) + (⟨b, hb⟩ : B) ∈ A.addSubgroupOf B := by
    rw [← QuotientAddGroup.eq]
    exact QuotientAddGroup.out_eq' _
  rw [AddSubgroup.mem_addSubgroupOf] at e
  simpa [neg_add_eq_sub] using e
end PI.UnitaryGroupMassFormula.UnimodLocStd
