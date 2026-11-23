-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.exists_torus_coeff_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:02.483551+00:00
-- url     : https://prove2.me/submissions/fd233668-284b-4b34-9118-86d63ddf6b57

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
private lemma sum_primitiveRoot_pow_mul_inv_pow_eq_ite {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ}
    (ha : a < N) (hb : b < N) :
    ∑ j : Fin N, (ζ ^ a * ζ⁻¹ ^ b) ^ (j : ℕ) = if a = b then (N : ℂ) else 0 := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
  have hz : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ a * ζ⁻¹ ^ b) ^ j) N]
  split_ifs with hab
  · subst hab
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    simp
  · have hω1 : ζ ^ a * ζ⁻¹ ^ b ≠ 1 := by
      intro h
      apply hab
      apply hζ.pow_inj ha hb
      rwa [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hz)] at h
    have hωN : (ζ ^ a * ζ⁻¹ ^ b) ^ N = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a, Nat.mul_comm b, pow_mul, pow_mul, inv_pow,
        hζ.pow_eq_one]
      simp
    rw [geom_sum_eq hω1, hωN]
    simp
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∃ z : ι → ℂ, (∀ i, ‖z i‖ = 1) ∧ ‖coeff s g‖ ≤ ‖eval z g‖ := by
  classical
  by_cases hs : s ∈ g.support
  swap
  · refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [show coeff s g = 0 by simpa using hs, norm_zero]
    exact norm_nonneg _
  obtain ⟨N, hN⟩ : ∃ N, N = g.totalDegree + 1 := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by omega
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN0⟩
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hN0
  have hlt : ∀ d ∈ g.support, ∀ i, d i < N := by
    intro d hd i
    have h1 : d i ≤ d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    have h2 := le_totalDegree hd
    omega
  let z : (ι → Fin N) → ι → ℂ := fun k i => ζ ^ (k i : ℕ)
  let c : (ι → Fin N) → ℂ := fun k => ∏ i, ζ⁻¹ ^ ((k i : ℕ) * s i)
  have key : ∑ k, eval (z k) g * c k = (N : ℂ) ^ Fintype.card ι * coeff s g := by
    calc ∑ k, eval (z k) g * c k
        = ∑ d ∈ g.support, coeff d g * ∏ i, ∑ j : Fin N, (ζ ^ d i * ζ⁻¹ ^ s i) ^ (j : ℕ) := by
          simp only [eval_eq', Finset.sum_mul, z, c]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm (d i), Nat.mul_comm (s i)]
      _ = ∑ d ∈ g.support, coeff d g * (if d = s then (N : ℂ) ^ Fintype.card ι else 0) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          congr 1
          simp_rw [sum_primitiveRoot_pow_mul_inv_pow_eq_ite hζ (hlt d hd _) (hlt s hs _)]
          split_ifs with hds
          · subst hds
            simp
          · obtain ⟨i, hi⟩ : ∃ i, d i ≠ s i := by
              by_contra h
              push_neg at h
              exact hds (Finsupp.ext h)
            exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
      _ = (N : ℂ) ^ Fintype.card ι * coeff s g := by
          rw [Finset.sum_eq_single s (fun d _ hd => by simp [hd]) (fun h => absurd hs h)]
          simp [mul_comm]
  by_contra hcon
  push_neg at hcon
  have hlt2 : ∀ k, ‖eval (z k) g * c k‖ < ‖coeff s g‖ := by
    intro k
    have hc : ‖c k‖ = 1 := by simp [c, norm_prod, norm_pow, norm_inv, hζn]
    rw [norm_mul, hc, mul_one]
    exact hcon (z k) (fun i => by simp [z, norm_pow, hζn])
  have hsum := norm_sum_le (Finset.univ : Finset (ι → Fin N)) (fun k => eval (z k) g * c k)
  have hsum2 : ∑ k, ‖eval (z k) g * c k‖ < ∑ _k : ι → Fin N, ‖coeff s g‖ :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hlt2 k)
  rw [key, norm_mul, norm_pow, Complex.norm_natCast] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul] at hsum2
  push_cast at hsum2
  linarith
end ReciprocityTheory.MultiplicativeHeights
