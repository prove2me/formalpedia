-- Prove2me | solution 1 for WaitJudge.Generic.gammaStarN_eq_gammaStar31
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:54:54.250157+00:00
-- url     : https://prove2.me/submissions/8e818478-d764-45ac-aa7f-563005fd021a

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting

set_option autoImplicit false
open WaitJudge.Generic

lemma mm_deriv_eval (N k : ℕ) (hk : k ≤ N) (q : Polynomial ℝ) (hq : q.natDegree ≤ N) (t : ℝ) :
    (1 / (k.factorial : ℝ)) * ((Polynomial.derivative^[k] q).eval t)
      = ∑ m ∈ Finset.Icc k N, q.coeff m * (m.choose k : ℝ) * t ^ (m - k) := by
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have h1 : Polynomial.derivative^[k] q = k.factorial • Polynomial.hasseDeriv k q := by
    rw [← Polynomial.factorial_smul_hasseDeriv]; rfl
  have h2 : (Polynomial.hasseDeriv k q).natDegree < N - k + 1 := by
    have := Polynomial.natDegree_hasseDeriv_le q k
    omega
  rw [h1, Polynomial.eval_smul, Polynomial.eval_eq_sum_range' h2]
  have h3 : Finset.Icc k N = Finset.Ico k (N + 1) := by ext; simp [Nat.lt_succ_iff]
  rw [h3, Finset.sum_Ico_eq_sum_range, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
  have : N + 1 - k = N - k + 1 := by omega
  rw [this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.hasseDeriv_coeff]
  have : k + i - k = i := by omega
  rw [this, add_comm i k]
  field_simp

theorem solution (N : ℕ) (ε : ℕ → ℝ) :
    gammaStarDualN N ε = gammaStar31 N ε := by
  unfold gammaStarDualN gammaStar31
  congr 1
  ext y
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    set q : Polynomial ℝ := ∑ m ∈ Finset.range (N + 1), Polynomial.C (lam m) * Polynomial.X ^ m with hqdef
    have hdeg : q.natDegree ≤ N := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using hm)
    have hc : ∀ m ≤ N, q.coeff m = lam m := by
      intro m hm
      rw [hqdef, Polynomial.finset_sum_coeff]
      simp [Polynomial.coeff_C_mul_X_pow, Nat.lt_succ_iff, hm]
    refine ⟨q, ⟨hdeg, ?_⟩, ?_⟩
    · intro k hk t ht
      rw [mm_deriv_eval N k hk q hdeg t]
      refine (hlam k hk t ht).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hc m (Finset.mem_Icc.1 hm).2]
    · rw [hqdef, Polynomial.eval_finset_sum]
      simp
  · rintro ⟨q, ⟨hdeg, hq⟩, rfl⟩
    refine ⟨fun m => q.coeff m, ?_, ?_⟩
    · intro k hk t ht
      have := hq k hk t ht
      rw [mm_deriv_eval N k hk q hdeg t] at this
      exact this
    · rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
      simp
