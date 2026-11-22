-- Prove2me | solution 1 for QECCertificates.rowDot_hammingNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:10.520868+00:00
-- url     : https://prove2.me/submissions/b38429e2-12c1-4cc5-9ac1-8c2e3f32860a

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.readOff_nil
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (z : Vec n₂) :
    hammingNorm (fun a : Fin n₁ => ∑ b, v (Sum.inl (a, b)) * z b) ≤ hammingNorm v := by
  classical
  rcases isEmpty_or_nonempty (Fin n₂) with hemp | hne
  · change (Finset.univ.filter (fun a : Fin n₁ => (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    have hzero : ∀ a : Fin n₁, (∑ b : Fin n₂, v (Sum.inl (a, b)) * z b) = 0 :=
      fun a => Finset.sum_eq_zero fun b _ => (hemp.false b).elim
    simp only [hzero, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
      Nat.zero_le]
  · obtain ⟨b₀⟩ := hne
    change (Finset.univ.filter (fun a : Fin n₁ => (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    let g : Fin n₁ → Fin n₂ := fun a =>
      if h : ∃ b, v (Sum.inl (a, b)) ≠ 0 then Classical.choose h else b₀
    refine Finset.card_le_card_of_injOn
      (fun a => (Sum.inl (a, g a) : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂))) ?_ ?_
    · intro a ha
      have hne : (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0 := (Finset.mem_filter.mp ha).2
      have hex : ∃ b, v (Sum.inl (a, b)) ≠ 0 := by
        by_contra hcon
        exact hne (Finset.sum_eq_zero fun b _ => by
          have hb : v (Sum.inl (a, b)) = 0 := by by_contra hb'; exact hcon ⟨b, hb'⟩
          rw [hb, zero_mul])
      have hg : v (Sum.inl (a, g a)) ≠ 0 := by
        dsimp only [g]
        rw [dif_pos hex]
        exact Classical.choose_spec hex
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
    · intro a _ a' _ h
      exact congrArg Prod.fst (Sum.inl_injective h)
end QECCertificates
