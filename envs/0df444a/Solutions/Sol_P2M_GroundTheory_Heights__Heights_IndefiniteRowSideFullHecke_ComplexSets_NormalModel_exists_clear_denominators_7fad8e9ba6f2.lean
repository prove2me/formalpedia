-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_exists_clear_denominators_7fad8e9ba6f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:13.098885+00:00
-- url     : https://prove2.me/submissions/ef9db53b-7ab7-4b04-b775-28b3f65db436

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelGraph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalModel
theorem _root_.solution {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hb : ∀ i, eval x (b i) ≠ 0) (q : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    ∃ (N : ℕ) (r : MvPolynomial (Fin n) ℂ),
      rename Sum.inl ((∏ i, b i) ^ N) * q - rename Sum.inl r ∈ M.ideal ∧
        eval x r = eval x (∏ i, b i) ^ N *
          eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q := by
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  set w : Fin n ⊕ Fin M.m → ℂ := Sum.elim x fun i => eval x (a i) / eval x (b i) with hw
  induction q using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, C c, ?_, ?_⟩
    · simp
    · simp
  | add p q hp hq =>
    obtain ⟨N₁, r₁, h₁, e₁⟩ := hp
    obtain ⟨N₂, r₂, h₂, e₂⟩ := hq
    refine ⟨N₁ + N₂, B ^ N₂ * r₁ + B ^ N₁ * r₂, ?_, ?_⟩
    · have hid : rename Sum.inl (B ^ (N₁ + N₂)) * (p + q) - rename Sum.inl (B ^ N₂ * r₁ + B ^ N₁ * r₂) =
          rename Sum.inl (B ^ N₂) * (rename Sum.inl (B ^ N₁) * p - rename Sum.inl r₁) +
            rename Sum.inl (B ^ N₁) * (rename Sum.inl (B ^ N₂) * q - rename Sum.inl r₂) := by
        simp only [map_mul, map_add, map_pow]
        ring
      rw [hid]
      exact M.ideal.add_mem (M.ideal.mul_mem_left _ h₁) (M.ideal.mul_mem_left _ h₂)
    · rw [eval_add, eval_add, eval_mul, eval_mul, e₁, e₂, eval_pow, eval_pow]
      ring
  | mul_X p s hp =>
    obtain ⟨N, r, h, e⟩ := hp
    rcases s with j | i
    · refine ⟨N, r * X j, ?_, ?_⟩
      · have hid : rename Sum.inl (B ^ N) * (p * X (Sum.inl j)) - rename Sum.inl (r * X j) =
            X (Sum.inl j) * (rename Sum.inl (B ^ N) * p - rename Sum.inl r) := by
          simp only [map_mul, rename_X]
          ring
        rw [hid]
        exact M.ideal.mul_mem_left _ h
      · rw [eval_mul, eval_mul, e, eval_X, eval_X]
        simp only [hw, Sum.elim_inl]
        ring
    · set Cᵢ : MvPolynomial (Fin n) ℂ := ∏ j ∈ Finset.univ.erase i, b j with hC
      have hBC : B = b i * Cᵢ := (Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)).symm
      refine ⟨N + 1, r * a i * Cᵢ, ?_, ?_⟩
      · have hid : rename Sum.inl (B ^ (N + 1)) * (p * X (Sum.inr i)) - rename Sum.inl (r * a i * Cᵢ) =
            rename Sum.inl Cᵢ * (rename Sum.inl (b i) * X (Sum.inr i)) *
                (rename Sum.inl (B ^ N) * p - rename Sum.inl r) +
              rename Sum.inl Cᵢ * rename Sum.inl r *
                (rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i)) := by
          rw [pow_succ, hBC]
          simp only [map_mul, map_pow]
          ring
        rw [hid]
        exact M.ideal.add_mem (M.ideal.mul_mem_left _ h) (M.ideal.mul_mem_left _ (hab i))
      · rw [eval_mul, eval_mul, eval_mul, eval_X, pow_succ, hBC]
        have e' : eval x r = eval x (b i * Cᵢ) ^ N * eval w p := by rw [← hBC]; exact e
        rw [e']
        simp only [hw, Sum.elim_inr, eval_mul]
        field_simp [hb i]
end NormalModel
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
