-- Prove2me | solution 1 for RLCDiscrepancy.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:13:20.020984+00:00
-- url     : https://prove2.me/submissions/d4f3fa1a-d068-475b-9b11-ecacea67abad

import Mathlib
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_fourier
import Definitions.Def_RLCDiscrepancy_dual

section
set_option autoImplicit false
namespace RLCDiscrepancy.Dev.E8
open RLCDiscrepancy

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

noncomputable abbrev B : LinearMap.BilinForm F (Fin n → F) := dotProductBilin F F

lemma B_apply (x y : Fin n → F) : B x y = x ⬝ᵥ y := rfl

lemma B_refl : (B : LinearMap.BilinForm F (Fin n → F)).IsRefl := fun x y h => by
  simpa [B_apply, dotProduct_comm] using h

lemma B_nondeg : (B : LinearMap.BilinForm F (Fin n → F)).Nondegenerate := by
  constructor
  · intro x hx
    exact dotProduct_eq_zero_iff.1 hx
  · intro y hy
    refine dotProduct_eq_zero_iff.1 ?_
    intro w
    rw [dotProduct_comm]; exact hy w

lemma mem_dual_iff (C : Submodule F (Fin n → F)) (y : Fin n → F) :
    y ∈ dual C ↔ y ∈ LinearMap.BilinForm.orthogonal B C := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rfl

lemma dual_dual (C : Submodule F (Fin n → F)) : dual (dual C) = C := by
  have : dual C = LinearMap.BilinForm.orthogonal B C := Submodule.ext (mem_dual_iff C)
  have h2 : dual (dual C) = LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B C) := by
    rw [← this]; exact Submodule.ext (mem_dual_iff _)
  rw [h2]
  exact LinearMap.BilinForm.orthogonal_orthogonal B_nondeg B_refl C

lemma card_code (C : Submodule F (Fin n → F)) :
    (codeFinset C).card = Fintype.card F ^ Module.finrank F C := by
  classical
  have h := Module.card_eq_pow_finrank (K := F) (V := C)
  rw [← h, Fintype.card_subtype]
  simp [codeFinset]

lemma card_mul (C : Submodule F (Fin n → F)) :
    (codeFinset C).card * (codeFinset (dual C)).card = Fintype.card F ^ n := by
  have hd : dual C = LinearMap.BilinForm.orthogonal B C := Submodule.ext (mem_dual_iff C)
  rw [card_code, card_code, ← pow_add, hd, LinearMap.BilinForm.finrank_orthogonal B_nondeg]
  have h1 : Module.finrank F C ≤ Module.finrank F (Fin n → F) := Submodule.finrank_le C
  rw [Module.finrank_fin_fun] at h1 ⊢
  congr 1
  omega

lemma zero_mem_code (C : Submodule F (Fin n → F)) : (0 : Fin n → F) ∈ codeFinset C := by
  simp

open Classical in
lemma sum_char (ψ : AddChar F ℂ) (hψ : ψ ≠ 0) (C : Submodule F (Fin n → F)) (x : Fin n → F) :
    ∑ y ∈ codeFinset (dual C), ψ (x ⬝ᵥ y) =
      if x ∈ C then ((codeFinset (dual C)).card : ℂ) else 0 := by
  classical
  split_ifs with hx
  · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))]
    · simp
    · intro y hy
      rw [mem_codeFinset] at hy
      rw [hy x hx, AddChar.map_zero_eq_one]
  · rw [← dual_dual C] at hx
    simp only [dual, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, not_forall] at hx
    obtain ⟨y0, hy0, hc⟩ := hx
    have hy0' : y0 ∈ dual C := hy0
    obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hψ
      ext b
      simp [hcon b]
    set S := ∑ y ∈ codeFinset (dual C), ψ (x ⬝ᵥ y) with hS
    set c := y0 ⬝ᵥ x with hcdef
    have hc' : x ⬝ᵥ y0 ≠ 0 := by rwa [dotProduct_comm]
    have key : S = S * ψ a := by
      rw [hS, Finset.sum_mul]
      refine Finset.sum_nbij' (fun y => y - (a / (x ⬝ᵥ y0)) • y0)
        (fun y => y + (a / (x ⬝ᵥ y0)) • y0) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        rw [mem_codeFinset] at hy ⊢
        exact (dual C).sub_mem hy ((dual C).smul_mem _ hy0')
      · intro y hy
        rw [mem_codeFinset] at hy ⊢
        exact (dual C).add_mem hy ((dual C).smul_mem _ hy0')
      · intro y _; simp
      · intro y _; simp
      · intro y _
        rw [← AddChar.map_add_eq_mul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        have e : a / (x ⬝ᵥ y0) * (x ⬝ᵥ y0) = a := by field_simp
        rw [e]; congr 1; ring
    have : S * (1 - ψ a) = 0 := by rw [mul_sub, mul_one, ← key]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm ha

end RLCDiscrepancy.Dev.E8

namespace RLCDiscrepancy
open RLCDiscrepancy.Dev.E8 in
theorem chk_eq_8 {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 0) (C : Submodule F (Fin n → F)) (f : (Fin n → F) → ℝ)
    (hf : ∑ x, f x = (Fintype.card F : ℝ) ^ n) :
    relDev C f = 1 / ((codeFinset C).card : ℝ) * (∑ x ∈ codeFinset C, f x) - 1 ∧
      (relDev C f : ℂ) = (∑ y ∈ codeFinset (dual C), fourier ψ f y) - 1 ∧
      (relDev C f : ℂ) = ∑ y ∈ codeFinset (dual C) \ {0}, fourier ψ f y := by
  classical
  have hq : (Fintype.card F : ℂ) ^ n ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast Fintype.card_ne_zero
  have hqR : (Fintype.card F : ℝ) ^ n ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast Fintype.card_ne_zero
  have hcard := card_mul C
  have hcardC : ((codeFinset C).card : ℝ) ≠ 0 := by
    have : (codeFinset C).card ≠ 0 := Finset.card_ne_zero.2 ⟨0, zero_mem_code C⟩
    exact_mod_cast this
  have hcardD : (((codeFinset (dual C)).card : ℕ) : ℂ) ≠ 0 := by
    have : (codeFinset (dual C)).card ≠ 0 := Finset.card_ne_zero.2 ⟨0, zero_mem_code _⟩
    exact_mod_cast this
  have h1 : relDev C f = 1 / ((codeFinset C).card : ℝ) * (∑ x ∈ codeFinset C, f x) - 1 := by
    simp [relDev, div_eq_inv_mul]
  have hcardC' : ((codeFinset C).card : ℂ) * ((codeFinset (dual C)).card : ℂ) =
      (Fintype.card F : ℂ) ^ n := by exact_mod_cast hcard
  have h2 : (relDev C f : ℂ) = (∑ y ∈ codeFinset (dual C), fourier ψ f y) - 1 := by
    have hsum : ∑ y ∈ codeFinset (dual C), fourier ψ f y =
        ((codeFinset (dual C)).card : ℂ) / (Fintype.card F : ℂ) ^ n *
          ∑ x ∈ codeFinset C, (f x : ℂ) := by
      unfold fourier
      rw [← Finset.sum_div]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_char ψ hψ C]
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      have : Finset.univ.filter (fun x => x ∈ C) = codeFinset C := by
        ext x; simp
      rw [this, div_eq_mul_inv, div_eq_mul_inv, mul_comm, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hsum, h1]
    push_cast
    have : ((codeFinset (dual C)).card : ℂ) / (Fintype.card F : ℂ) ^ n =
        1 / ((codeFinset C).card : ℂ) := by
      rw [← hcardC']
      have : ((codeFinset C).card : ℂ) ≠ 0 := by exact_mod_cast hcardC
      field_simp
    rw [this]
  have h0 : fourier ψ f 0 = 1 := by
    unfold fourier
    simp only [dotProduct_zero, AddChar.map_zero_eq_one, mul_one]
    rw [← Complex.ofReal_sum, hf]
    push_cast
    exact div_self hq
  refine ⟨h1, h2, ?_⟩
  rw [h2, ← Finset.sum_sdiff (Finset.singleton_subset_iff.2 (zero_mem_code (dual C)))]
  simp [h0]
end RLCDiscrepancy
end

theorem solution : type_of% @RLCDiscrepancy.chk_eq_8 := @RLCDiscrepancy.chk_eq_8
