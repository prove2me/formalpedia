-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.comm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:42.855614+00:00
-- url     : https://prove2.me/submissions/b9867a3b-f33c-4078-8589-75794982553f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_relIdx_map_smul
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
private theorem relIndex_ne_zero_of_le {A B : AddSubgroup V} (h : B ≤ A) : A.relIndex B ≠ 0 :=
  relIndex_ne_zero_of_finite_cover (ι := Unit) (fun _ => 0) (fun _ => B.zero_mem)
    (fun b hb => ⟨(), by simpa using h hb⟩)
private theorem relIndex_ne_zero_trans' {A B C : AddSubgroup V} (h : A.relIndex B ≠ 0)
    (h' : B.relIndex C ≠ 0) : A.relIndex C ≠ 0 := by
  exact AddSubgroup.relIndex_ne_zero_trans h h'
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
theorem _root_.solution {S X : AddSubgroup V} {w : ℂ} (hw : w ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hS : (S.map (smulHom (N : ℂ))).relIndex S ≠ 0) (h1 : S.relIndex X ≠ 0) (h2 : X.relIndex S ≠ 0)
    (ha : ∀ x ∈ X, (N : ℂ) • w • x ∈ X) (hb : ∀ x ∈ X, (N : ℂ) • w⁻¹ • x ∈ X) :
    S.relIndex (X.map (smulHom w)) ≠ 0 ∧ (X.map (smulHom w)).relIndex S ≠ 0 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNXS : (X.map (smulHom (N : ℂ))).relIndex (S.map (smulHom (N : ℂ))) ≠ 0 := by
    rw [relIdx_map_smul hN']; exact h2
  have t1 : (X.map (smulHom (N : ℂ))).relIndex X ≠ 0 :=
    relIndex_ne_zero_trans' (relIndex_ne_zero_trans' hNXS hS) h1
  have hcomm : (X.map (smulHom w)).map (smulHom (N : ℂ)) =
      (X.map (smulHom (N : ℂ))).map (smulHom w) := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext v
    simp only [AddMonoidHom.comp_apply, smulHom_apply, smul_smul, mul_comm]
  have t2 : ((X.map (smulHom w)).map (smulHom (N : ℂ))).relIndex
      (X.map (smulHom w)) ≠ 0 := by
    rw [hcomm, relIdx_map_smul hw]; exact t1
  have t3 : X.relIndex ((X.map (smulHom w)).map (smulHom (N : ℂ))) ≠ 0 := by
    refine relIndex_ne_zero_of_le ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa using ha x hx
  have t4 : (X.map (smulHom w)).relIndex (X.map (smulHom (N : ℂ))) ≠ 0 := by
    refine relIndex_ne_zero_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(N : ℂ) • w⁻¹ • x, hb x hx, ?_⟩
    rw [smulHom_apply, smulHom_apply, smul_smul, smul_smul]
    congr 1
    rw [mul_comm w, mul_assoc, mul_inv_cancel₀ hw, mul_one]
  exact ⟨relIndex_ne_zero_trans' (relIndex_ne_zero_trans' h1 t3) t2,
    relIndex_ne_zero_trans' t4 (relIndex_ne_zero_trans' hNXS hS)⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
