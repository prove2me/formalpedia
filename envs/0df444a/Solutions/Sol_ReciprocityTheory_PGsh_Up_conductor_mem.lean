-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.conductor_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:14.70896+00:00
-- url     : https://prove2.me/submissions/81acbdfb-4090-442f-9735-6cdf5f23e509

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
private lemma valuation_coeff_prod_X_sub_C_le_one {n : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (s : Finset (Fin n)) (k : ℕ) :
    v ((∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))).coeff k) ≤ 1 := by
  have h : (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))) =
      (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (⟨a τ', ha τ'⟩ : v.integer))).map v.integer.subtype := by
    simp [Polynomial.map_prod]
  rw [h, Polynomial.coeff_map]
  exact (Valuation.mem_integer_iff _ _).1 (Subtype.prop _)
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) (τ : Fin n) (u : Fin h → C)
    (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => if y.1 = τ then fder a τ * u y.2 else 0) ∈ F.pts := by
  classical
  have hdeg : (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).natDegree < n := by
    rw [Polynomial.natDegree_finset_prod_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_lt (Fin.pos τ) one_pos
  have heval : ∀ τ', (∏ τ'' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ''))).eval (a τ') =
      if τ' = τ then fder a τ else 0 := by
    intro τ'
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    split_ifs with h
    · subst h
      rfl
    · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)
  refine ⟨fun x => (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff x.1 * u x.2,
    fun x => ?_, ?_⟩
  · rw [map_mul]
    exact mul_le_one₀ (valuation_coeff_prod_X_sub_C_le_one ha _ _) (zero_le) (hu _)
  · rw [hF]
    funext y
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, freeMat, Matrix.of_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsum : ∑ k : Fin n, a y.1 ^ (k : ℕ) *
        ((∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff k * u y.2) =
        (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).eval (a y.1) * u y.2 := by
      rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul,
        ← Fin.sum_univ_eq_sum_range (fun i => _ * a y.1 ^ i * u y.2)]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, heval]
    split_ifs <;> simp
end ReciprocityTheory.PGsh.Up
