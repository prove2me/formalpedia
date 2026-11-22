-- Prove2me | solution 1 for QECCertificates.colDot_hammingNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:12.394656+00:00
-- url     : https://prove2.me/submissions/5be5e857-a136-4186-addc-e933eb0b19ba

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
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (w : Vec r₁) :
    hammingNorm (fun t : Fin r₂ => ∑ i, v (Sum.inr (i, t)) * w i) ≤ hammingNorm v := by
  classical
  rcases isEmpty_or_nonempty (Fin r₁) with hemp | hne
  · change (Finset.univ.filter (fun t : Fin r₂ => (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    have hzero : ∀ t : Fin r₂, (∑ i : Fin r₁, v (Sum.inr (i, t)) * w i) = 0 :=
      fun t => Finset.sum_eq_zero fun i _ => (hemp.false i).elim
    simp only [hzero, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
      Nat.zero_le]
  · obtain ⟨i₀⟩ := hne
    change (Finset.univ.filter (fun t : Fin r₂ => (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    let g : Fin r₂ → Fin r₁ := fun t =>
      if h : ∃ i, v (Sum.inr (i, t)) ≠ 0 then Classical.choose h else i₀
    refine Finset.card_le_card_of_injOn
      (fun t => (Sum.inr (g t, t) : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂))) ?_ ?_
    · intro t ht
      have hne : (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0 := (Finset.mem_filter.mp ht).2
      have hex : ∃ i, v (Sum.inr (i, t)) ≠ 0 := by
        by_contra hcon
        exact hne (Finset.sum_eq_zero fun i _ => by
          have hi : v (Sum.inr (i, t)) = 0 := by by_contra hi'; exact hcon ⟨i, hi'⟩
          rw [hi, zero_mul])
      have hg : v (Sum.inr (g t, t)) ≠ 0 := by
        dsimp only [g]
        rw [dif_pos hex]
        exact Classical.choose_spec hex
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
    · intro t _ t' _ h
      exact congrArg Prod.snd (Sum.inr_injective h)
end QECCertificates
