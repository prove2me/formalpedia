-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.central_projector_irrep_action
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:38:20.288193+00:00
-- url     : https://prove2.me/submissions/b261ce6b-66ad-458b-8d70-98340e7c0ddc

import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_character_orthogonality
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_irreducible_twirl
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [DecidableEq A] {n : ℕ}
private lemma scalar_of_commute (U : UnitaryIrrep G n) (X : Mat n)
    (hx : ∀ g, X * U.rho g = U.rho g * X) : ∃ c : ℂ, X = c • (1 : Mat n) := by
  have hC (g : G) : conjugationMap U g X = X := by
    change U.rho g * (X * (U.rho g)ᴴ) = X
    rw [← Matrix.mul_assoc, ← hx, Matrix.mul_assoc, (U.unitary g).2, Matrix.mul_one]
  have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨Matrix.trace X / n, ?_⟩
  simpa only [hC, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hg, one_smul] using irreducible_twirl U X
private lemma character_mul_comm (F : IrrepFamily G A) (a : A) (g h : G) :
    character (F.irrep a) (g*h) = character (F.irrep a) (h*g) := by
  simp only [character, (F.irrep a).mul]
  exact Matrix.trace_mul_comm _ _


set_option autoImplicit false

set_option autoImplicit false

theorem solution {G A : Type*} [Group G] [Fintype G] [DecidableEq A] (F : IrrepFamily G A) (a b : A) :
    ((F.dim a : ℂ) / Fintype.card G) •
      (∑ g : G, character (F.irrep a) g⁻¹ • (F.irrep b).rho g) =
      if a = b then (1 : Mat (F.dim b)) else 0 := by
  classical
  let S : Mat (F.dim b) := ∑ g : G, character (F.irrep a) g⁻¹ • (F.irrep b).rho g
  have hS (h : G) : S * (F.irrep b).rho h = (F.irrep b).rho h * S := by
    have h1 := Equiv.sum_comp (Equiv.mulRight h)
      (fun k : G => character (F.irrep a) (h*k⁻¹) • (F.irrep b).rho k)
    have h2 := Equiv.sum_comp (Equiv.mulLeft h)
      (fun k : G => character (F.irrep a) (k⁻¹*h) • (F.irrep b).rho k)
    dsimp at h1 h2
    simp only [mul_inv_rev, mul_inv_cancel_left] at h1
    simp only [mul_inv_rev, inv_mul_cancel_right] at h2
    calc
      S * (F.irrep b).rho h = ∑ g, character (F.irrep a) g⁻¹ • (F.irrep b).rho (g*h) := by
        simp [S, Matrix.sum_mul, Matrix.smul_mul, (F.irrep b).mul]
      _ = ∑ k, character (F.irrep a) (h*k⁻¹) • (F.irrep b).rho k := h1
      _ = ∑ k, character (F.irrep a) (k⁻¹*h) • (F.irrep b).rho k := by
        simp_rw [character_mul_comm F a h]
      _ = ∑ g, character (F.irrep a) g⁻¹ • (F.irrep b).rho (h*g) := h2.symm
      _ = (F.irrep b).rho h * S := by
        simp [S, Matrix.mul_sum, Matrix.mul_smul, (F.irrep b).mul]
  obtain ⟨c,hc⟩ := scalar_of_commute (F.irrep b) S hS
  have htrace : Matrix.trace S = (Fintype.card G : ℂ) * (if a = b then 1 else 0) := by
    have h := character_orthogonality F b a
    have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have he : Matrix.trace S = ∑ g, character (F.irrep b) g * character (F.irrep a) g⁻¹ := by
      simp [S, Matrix.trace_sum, Matrix.trace_smul, character, mul_comm]
    rw [he]
    apply (mul_left_cancel₀ (inv_ne_zero hg))
    simpa [← mul_assoc, hg, eq_comm] using h
  have hct : c * (F.dim b : ℂ) = (Fintype.card G : ℂ) * (if a = b then 1 else 0) := by
    simpa [hc, Matrix.trace_smul, Matrix.trace_one] using htrace
  change ((F.dim a : ℂ) / Fintype.card G) • S = _
  rw [hc,smul_smul]
  split_ifs with hab
  · subst b
    have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hd : (F.dim a : ℂ) ≠ 0 := by exact_mod_cast (F.irrep a).positive.ne'
    simp at hct
    have he : (F.dim a : ℂ) / Fintype.card G * c = 1 := by
      field_simp
      linear_combination hct
    rw [he,one_smul]
  · have hd : (F.dim b : ℂ) ≠ 0 := by exact_mod_cast (F.irrep b).positive.ne'
    have hz : c = 0 := (mul_eq_zero.mp (by simpa [hab] using hct)).resolve_right hd
    simp [hz]