-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.freq_to_beta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:12.358562+00:00
-- url     : https://prove2.me/submissions/c3783ada-2a15-463f-887e-0a4b84c5c70e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_freq_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_nonempty_Psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_cc_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hχ : IsHermFam χ) (hf : X.IsFreqZ X.g χ) :
    ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧ χ = X.embH β ∧
      ∀ i k, IsIntegral ℤ (((X.g * dEnat E ^ 2 : ℕ) : E) * β i k) := by
  have hreal : ∀ τ i, (χ τ i i).im = 0 := fun τ i => by
    have := congrArg Complex.im (hχ τ i i)
    simp only [Complex.conj_im] at this
    linarith
  have hcc_int : ∀ γ : 𝓞 E, IsIntegral ℤ (cc (γ : E)) := fun γ => isIntegral_cc γ.isIntegral_coe

  obtain ⟨ω01, hω01, hi01⟩ := X.freq_entry χ hf (fun τ => χ τ 0 1)
    (fun γ => ![![0, (γ : E)], ![cc (γ : E), 0]])
    (fun γ i k => by fin_cases i <;> fin_cases k <;> simp [isIntegral_zero, γ.isIntegral_coe, hcc_int])
    (fun γ i k => by fin_cases i <;> fin_cases k <;> simp [cc_cc, cc_zero])
    (fun γ => by
      rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_zero, mul_zero, zero_add, add_zero, emb_cc]
      rw [hχ τ 0 1]
      simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring)

  have hdiag : ∀ j : Fin 2, ∃ ω : E, (∀ τ : X.Ψ, χ τ j j = τ.1 ω) ∧
      IsIntegral ℤ (((X.g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
    intro j
    refine X.freq_entry χ hf (fun τ => χ τ j j)
      (fun γ i k => if i = j ∧ k = j then (γ : E) + cc (γ : E) else 0)
      (fun γ i k => by split_ifs; exact γ.isIntegral_coe.add (hcc_int γ); exact isIntegral_zero)
      (fun γ i k => by
        by_cases h : i = j ∧ k = j
        · rw [if_pos h, if_pos ⟨h.2, h.1⟩, show cc ((γ : E) + cc (γ : E)) = cc (γ : E) + cc (cc (γ : E)) from
            map_add (IsCMField.complexConj E) _ _, cc_cc, add_comm]
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), cc_zero])
      (fun γ => ?_)
    rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hs : ∑ i, ∑ k, χ τ i k * τ.1 (if i = j ∧ k = j then (γ : E) + cc (γ : E) else 0) =
        χ τ j j * τ.1 ((γ : E) + cc (γ : E)) := by
      rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [hk]
      · simp
      · intro i _ hi; apply Finset.sum_eq_zero; intro k _; simp [hi]
      · simp
    rw [hs, map_add, emb_cc]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, hreal]
    ring
  obtain ⟨ω00, hω00, hi00⟩ := hdiag 0
  obtain ⟨ω11, hω11, hi11⟩ := hdiag 1
  obtain ⟨τ0⟩ := X.nonempty_Psi
  have hcc_diag : ∀ (ω : E) (j : Fin 2), (∀ τ : X.Ψ, χ τ j j = τ.1 ω) → cc ω = ω := by
    intro ω j hω
    apply τ0.1.injective
    rw [emb_cc, ← hω τ0, ← hχ τ0 j j]
  refine ⟨!![ω00, ω01; cc ω01, ω11], fun i k => ?_, ?_, fun i k => ?_⟩
  · fin_cases i <;> fin_cases k <;> simp [cc_cc, hcc_diag ω00 0 hω00, hcc_diag ω11 1 hω11]
  · funext τ i k
    fin_cases i <;> fin_cases k
    · simp [Data.embH, hω00 τ]
    · simp [Data.embH, hω01 τ]
    · simp only [Data.embH]
      simp [hχ τ 0 1, hω01 τ, emb_cc]
    · simp [Data.embH, hω11 τ]
  · unfold dEnat
    fin_cases i <;> fin_cases k
    · simpa using hi00
    · simpa using hi01
    · have := isIntegral_cc hi01
      simpa [cc_mul, cc] using this
    · simpa using hi11
end ReciprocityTheory.ChartRestriction.G.FD.DataX
