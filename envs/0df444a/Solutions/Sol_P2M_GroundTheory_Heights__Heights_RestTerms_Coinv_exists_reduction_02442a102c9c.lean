-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_exists_reduction_02442a102c9c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:31:53.870016+00:00
-- url     : https://prove2.me/submissions/6b38b38b-5040-44f3-8fac-f37eada7ae1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_prod_X_add_eq_pow_fb0dfdb72940
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_ne_top_235876379a14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}
variable [CharZero K]
namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv
theorem _root_.solution (b : Fin f) (k : Fin n) :
    ∃ c : ℕ → MvPolynomial ↥(Finset.Ioi k) K,
      X (b, k) ^ ((k : ℕ) + 1) + ∑ j ∈ range ((k : ℕ) + 1),
        rename (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) (c j) * X (b, k) ^ j ∈
        psumIdeal K f n := by
  classical
  set ψ := rename (R := K) (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) with hψ
  have hinj : Function.Injective (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) := by
    intro s t h
    exact Subtype.ext (Prod.ext_iff.mp h).2
  set A' : Polynomial (MvPolynomial ↥(Finset.Ioi k) K) :=
    ∏ s : ↥(Finset.Ioi k), (Polynomial.X + Polynomial.C (X s)) with hA'
  have hA'm : A'.Monic := Polynomial.monic_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_add_C _)
  have hA'deg : A'.natDegree = n - 1 - k := by
    rw [hA', Polynomial.natDegree_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_add_C _)]
    simp [Fin.card_Ioi]
  set Sh' := (Polynomial.X ^ n : Polynomial (MvPolynomial ↥(Finset.Ioi k) K)) /ₘ A' with hSh'
  have hk : (k : ℕ) < n := k.isLt
  have hSdeg : Sh'.natDegree = (k : ℕ) + 1 := by
    rw [hSh', Polynomial.natDegree_divByMonic _ hA'm, Polynomial.natDegree_X_pow, hA'deg]
    omega
  have hSlead : Sh'.leadingCoeff = 1 := by
    rw [hSh', Polynomial.leadingCoeff_divByMonic_of_monic hA'm]
    · simp
    · rw [Polynomial.degree_eq_natDegree hA'm.ne_zero, Polynomial.degree_X_pow, hA'deg]
      exact_mod_cast (by omega : n - 1 - (k : ℕ) ≤ n)

  set I := psumIdeal K f n
  have : Nontrivial (MvPolynomial (Fin f × Fin n) K ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr psumIdeal_ne_top
  set π := Ideal.Quotient.mk I
  have hsplit := prod_X_add_eq_pow (K := K) (f := f) (n := n) b
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => k < i)] at hsplit
  have hfilt : Finset.univ.filter (fun i : Fin n => k < i) = Finset.Ioi k := by
    ext i; simp
  rw [hfilt] at hsplit
  have hmapA : A'.map (π.comp ψ.toRingHom) =
      ∏ i ∈ Finset.Ioi k, (Polynomial.X + Polynomial.C (π (X (b, i)))) := by
    rw [hA', Polynomial.map_prod, ← Finset.prod_coe_sort (Finset.Ioi k)]
    simp [hψ, π]
  have key : Sh'.map (π.comp ψ.toRingHom) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ k < i),
        (Polynomial.X + Polynomial.C (π (X (b, i)))) := by
    rw [hSh', Polynomial.map_divByMonic _ hA'm, Polynomial.map_pow, Polynomial.map_X]
    refine (Polynomial.div_modByMonic_unique _ (0 : Polynomial (MvPolynomial (Fin f × Fin n) K ⧸ I))
      (hA'm.map (π.comp ψ.toRingHom)) ⟨?_, ?_⟩).1
    · rw [zero_add, hmapA, hsplit]
    · rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun h => (hA'm.map (π.comp ψ.toRingHom)).ne_zero
        (Polynomial.degree_eq_bot.mp h))
  have hev : π (Polynomial.eval (-X (b, k)) (Sh'.map ψ.toRingHom)) = 0 := by
    rw [← Polynomial.eval₂_at_apply π, ← Polynomial.eval_map, Polynomial.map_map, key,
      Polynomial.eval_prod]
    refine Finset.prod_eq_zero (i := k) (by simp) ?_
    simp
  have hmem : Polynomial.eval (-X (b, k)) (Sh'.map ψ.toRingHom) ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hev

  refine ⟨fun j => (-1) ^ ((k : ℕ) + 1 + j) * Sh'.coeff j, ?_⟩
  have hdegmap : (Sh'.map ψ.toRingHom).natDegree = (k : ℕ) + 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective (rename_injective _ hinj), hSdeg]
  rw [Polynomial.eval_eq_sum_range, hdegmap, Finset.sum_range_succ] at hmem
  have htop : (Sh'.map ψ.toRingHom).coeff ((k : ℕ) + 1) = 1 := by
    rw [Polynomial.coeff_map, ← hSdeg]
    change ψ (Sh'.leadingCoeff) = 1
    rw [hSlead, map_one]
  rw [htop, one_mul] at hmem
  have := Ideal.mul_mem_left I ((-1) ^ ((k : ℕ) + 1)) hmem
  convert this using 1
  rw [mul_add, Finset.mul_sum, neg_pow (X (b, k) : MvPolynomial (Fin f × Fin n) K), ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_map, neg_pow (X (b, k) : MvPolynomial (Fin f × Fin n) K)]
  simp only [map_mul, map_pow, map_neg, map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Coinv
