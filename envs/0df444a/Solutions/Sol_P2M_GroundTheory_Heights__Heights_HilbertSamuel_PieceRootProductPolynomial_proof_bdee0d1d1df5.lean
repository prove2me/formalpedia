-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_proof_bdee0d1d1df5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:56:10.959275+00:00
-- url     : https://prove2.me/submissions/6128488a-c8b8-4193-a387-c3659929d0ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceRootProductPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_bound_37ce09f513ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_monic_of_coeffs_c20b2a3a7093

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PieceRootProductPolynomial
theorem _root_.solution (h1 : PieceCoefficientsHolomorphic.Statement)
    (h2 : MonicRootGrowth.Statement) (h3 : GrowthOffHypersurfacePolynomial.Statement) :
    PieceRootProductPolynomial.Statement := by
  intro n d N k A Z c m Q O F hm hQ hroot hcov hO hF hOF hk
  have hhol := h1 n d N A Z c Q O F hcov hO hF hOF
  obtain ⟨C, M, hC⟩ := h2 d m hm
  have hfin : ∀ y : Fin d → ℂ, eval y Q ≠ 0 → {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.Finite :=
    fun y hy => (hcov y hy).1.subset (fun x hx => ⟨hx.1, hx.2.2⟩)

  have hprod : ∀ (y : Fin d → ℂ) (hy : eval y Q ≠ 0),
      (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}, (Polynomial.X - Polynomial.C (∑ j, c j * x j))) =
        ∏ x ∈ (hfin y hy).toFinset, (Polynomial.X - Polynomial.C (∑ j, c j * x j)) :=
    fun y hy => finprod_mem_eq_finite_toFinset_prod _ (hfin y hy)
  have hcard : ∀ (y : Fin d → ℂ) (hy : eval y Q ≠ 0), (hfin y hy).toFinset.card = k :=
    fun y hy => by rw [← Set.ncard_eq_toFinset_card _ (hfin y hy), hk y hy]

  have hgrowth : ∀ (i : ℕ) (y : Fin d → ℂ), eval y Q ≠ 0 →
      ‖(∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i‖ ≤
        ((k.choose i : ℝ) * |C| ^ (k - i)) * (1 + ‖y‖) ^ (M * (k - i)) := by
    intro i y hy
    rw [hprod y hy]
    have hb := PieceRootProductPolynomial.coeff_bound (hfin y hy).toFinset (fun x => ∑ j, c j * x j)
      (|C| * (1 + ‖y‖) ^ M) (fun x hx => by
        obtain ⟨hxZ, -, hxy⟩ := (Set.Finite.mem_toFinset _).1 hx
        have h := hC y _ (hxy ▸ hroot x hxZ)
        exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) i
    rw [hcard y hy] at hb
    calc _ ≤ _ := hb
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hp : ∀ i : ℕ, ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i = eval y p :=
    fun i => h3 d Q _ _ _ hQ (hhol i) (hgrowth i)
  choose p hp using hp
  refine ⟨Polynomial.X ^ k + ∑ j : Fin k, Polynomial.C (p j) * Polynomial.X ^ (j : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_, fun y hy => ?_⟩
  · rw [Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt _
  · have hmon : (∏ x ∈ (hfin y hy).toFinset, (Polynomial.X - Polynomial.C (∑ j, c j * x j))).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _)
    have hdeg : (∏ x ∈ (hfin y hy).toFinset,
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).natDegree = k := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _),
        Finset.sum_congr rfl (fun x _ => Polynomial.natDegree_X_sub_C _), Finset.sum_const, smul_eq_mul,
        mul_one, hcard y hy]
    ext i
    rw [Polynomial.coeff_map, PieceRootProductPolynomial.coeff_monic_of_coeffs]
    by_cases hi : i < k
    · rw [if_pos hi, hp i y hy]
    · rw [if_neg hi, hprod y hy]
      by_cases hik : i = k
      · rw [if_pos hik, map_one, hik, ← hdeg]
        exact hmon.coeff_natDegree.symm
      · rw [if_neg hik, map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
end PieceRootProductPolynomial
end GroundTheory.Heights₂.Heights.HilbertSamuel
