-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:48.572882+00:00
-- url     : https://prove2.me/submissions/13f6a0c8-7063-427d-8c4e-76cc66402968

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_mulL
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_opMono_inr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_sub
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_mulL
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
variable (ε : Fin m → Bool)
namespace PositivityTheory.Rg.Sw.LC.B1
theorem _root_.solution (Γ : Finset (σ →₀ ℕ)) (hΓ : ∀ γ ∈ Γ, ∀ k ∈ γ.support, inF1 ε k) :
    ∀ N, ∀ γ ∈ Γ, (Γ.filter (γ < ·)).card ≤ N →
      ∃ P : Sym m n, SymbolInFirstFamily ε P ∧ ∀ δ ∈ Γ, op P (monomial δ 1) = if δ = γ then 1 else 0 := by
  classical
  intro N
  induction N with
  | zero =>
    intro γ hγ hc
    exact aux Γ hΓ γ hγ (fun δ hδ => by
      exfalso
      have : 0 < (Γ.filter (γ < ·)).card := Finset.card_pos.mpr ⟨δ, hδ⟩
      omega)
  | succ N ih =>
    intro γ hγ hc
    refine aux Γ hΓ γ hγ fun δ hδ => ih δ (Finset.mem_filter.mp hδ).1 ?_
    have hlt : (Γ.filter (δ < ·)).card < (Γ.filter (γ < ·)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, lt_trans (Finset.mem_filter.mp hδ).2 hx.2⟩
      · have := hsub hδ
        rw [Finset.mem_filter] at this
        exact lt_irrefl _ this.2
    omega
where
  aux (Γ : Finset (σ →₀ ℕ)) (hΓ : ∀ γ ∈ Γ, ∀ k ∈ γ.support, inF1 ε k) (γ : σ →₀ ℕ) (hγ : γ ∈ Γ)
      (hex : ∀ δ ∈ Γ.filter (γ < ·), ∃ P : Sym m n, SymbolInFirstFamily ε P ∧ ∀ δ' ∈ Γ, op P (monomial δ' 1) = if δ' = δ then 1 else 0) :
      ∃ P : Sym m n, SymbolInFirstFamily ε P ∧ ∀ δ ∈ Γ, op P (monomial δ 1) = if δ = γ then 1 else 0 := by
    classical
    choose! Q hQ using hex
    let g : ℂ := ∏ k, (((γ k).factorial : ℕ) : ℂ)
    let D : (σ →₀ ℕ) → ℂ := fun δ => g⁻¹ * ∏ k, ((δ k).descFactorial (γ k) : ℂ)
    refine ⟨(g⁻¹ : ℂ) • monomial (Finsupp.mapDomain Sum.inr γ) 1 -
      ∑ δ ∈ Γ.filter (γ < ·), D δ • (monomial (Finsupp.mapDomain Sum.inl (δ - γ)) 1 * Q δ), ?_, ?_⟩
    · refine sf_sub ε (sf_smul ε _ (sf_inr ε γ (hΓ γ hγ) 1)) (sf_sum ε _ _ fun δ hδ => sf_smul ε _ ?_)
      refine sf_mulL ε _ (fun k hk => ?_) (hQ δ hδ).1 1
      have : (δ - γ) k ≠ 0 := Finsupp.mem_support_iff.mp hk
      exact hΓ δ (Finset.mem_filter.mp hδ).1 k (Finsupp.mem_support_iff.mpr (by
        rw [Finsupp.tsub_apply] at this; omega))
    · intro δ' hδ'
      rw [sub_eq_add_neg, op_add, ← neg_one_smul ℂ (∑ δ ∈ _, _), op_smul, op_smul, op_sum, op_monomial, opMono_inr]
      have hsum : ∑ δ ∈ Γ.filter (γ < ·), op (D δ • (monomial (Finsupp.mapDomain Sum.inl (δ - γ)) 1 * Q δ))
          (monomial δ' 1 : PX m n) = if γ < δ' then D δ' • (monomial (δ' - γ) 1 : PX m n) else 0 := by
        rw [Finset.sum_congr rfl fun δ hδ => by rw [op_smul, op_mulL, (hQ δ hδ).2 δ' hδ']]
        simp only [mul_ite, mul_one, mul_zero, smul_ite, smul_zero]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_filter, hδ', true_and]
      rw [hsum]
      have hmain : (g⁻¹ : ℂ) • (1 : ℂ) • (monomial (δ' - γ) (∏ k, ((δ' k).descFactorial (γ k) : ℂ)) : PX m n) =
          D δ' • monomial (δ' - γ) 1 := by
        rw [one_smul, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, mul_one]
      rw [hmain]
      by_cases hlt : γ < δ'
      · rw [if_pos hlt, if_neg (ne_of_gt hlt)]; simp
      · rw [if_neg hlt]
        by_cases he : δ' = γ
        · subst he
          rw [if_pos rfl]
          have hD : D δ' = 1 := by
            simp only [D, g, Nat.descFactorial_self]
            rw [inv_mul_cancel₀]
            exact Finset.prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast Nat.factorial_ne_zero _
          rw [hD, one_smul, tsub_self, ← C_apply, C_1]; simp
        · rw [if_neg he]
          have hnle : ¬ γ ≤ δ' := fun hle => hlt (lt_of_le_of_ne hle (Ne.symm he))
          obtain ⟨k, hk⟩ : ∃ k, δ' k < γ k := by
            by_contra hcon
            push_neg at hcon
            exact hnle (fun k => hcon k)
          have hD : D δ' = 0 := by
            simp only [D]
            rw [Finset.prod_eq_zero (Finset.mem_univ k) (by exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr hk),
              mul_zero]
          rw [hD, zero_smul]; simp
end PositivityTheory.Rg.Sw.LC.B1
