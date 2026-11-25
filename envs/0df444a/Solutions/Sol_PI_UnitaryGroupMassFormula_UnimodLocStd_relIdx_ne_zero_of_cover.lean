-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.relIdx_ne_zero_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:14.06394+00:00
-- url     : https://prove2.me/submissions/d0e54f1f-99eb-4f12-ab39-79b4045a1b20

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
theorem _root_.solution {A B : AddSubgroup V} {ι : Type*} [Finite ι] (φ : ι → V)
    (hφ : ∀ i, φ i ∈ B) (hcov : ∀ b ∈ B, ∃ i, b - φ i ∈ A) : A.relIndex B ≠ 0 :=
  relIndex_ne_zero_of_finite_cover φ hφ hcov
end PI.UnitaryGroupMassFormula.UnimodLocStd
