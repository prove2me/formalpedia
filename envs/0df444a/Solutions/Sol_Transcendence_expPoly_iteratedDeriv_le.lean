-- Prove2me | solution 1 for Transcendence.expPoly_iteratedDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:13:03.74926+00:00
-- url     : https://prove2.me/submissions/d311856e-d99e-4cb3-8c63-739a0a1d9a6c

import Mathlib

/-!
# All derivatives of an exponential polynomial from its first `N`

Let `f(z) = ∑ⱼ Pⱼ(z) e^{wⱼ z}` with `Pⱼ = 0` or `deg Pⱼ < qⱼ`, `∑ⱼ qⱼ = N` and `‖wⱼ‖ ≤ W`, and
suppose `‖f⁽ˢ⁾(c)‖ ≤ D` for `s < N`. Induct on `N`. If `N = 0`, every `Pⱼ` is zero. Otherwise pick
`j₀` with `q_{j₀} ≠ 0` and peel that frequency: `g = f' - w_{j₀} f = ∑ⱼ Qⱼ(z) e^{wⱼ z}` with
`Qⱼ = Pⱼ' + (wⱼ - w_{j₀}) Pⱼ` has the same shape, with `q_{j₀}` lowered by one. Since
`g⁽ˢ⁾(c) = f⁽ˢ⁺¹⁾(c) - w_{j₀} f⁽ˢ⁾(c)`, the first `N - 1` derivatives of `g` at `c` are at most
`D (W + 1)`, so by induction `‖g⁽ⁿ⁾(c)‖ ≤ D (W + 1)^{n + N}`. Finally
`f⁽ⁿ⁺¹⁾(c) = g⁽ⁿ⁾(c) + w_{j₀} f⁽ⁿ⁾(c)` gives the bound for `f` by induction on `n`, because
`D (W + 1)^{n + N} + W · D (W + 1)^{n + N} = D (W + 1)^{n + 1 + N}`.
-/

open Finset Polynomial in
theorem solution {ι : Type*} [Fintype ι] (w : ι → ℂ) (W : ℝ) (hW0 : 0 ≤ W)
    (hW : ∀ j, ‖w j‖ ≤ W) (c : ℂ) (N : ℕ) (q : ι → ℕ) (P : ι → ℂ[X])
    (hP : ∀ j, P j = 0 ∨ (P j).natDegree < q j) (hN : ∑ j, q j = N) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ s < N, ‖iteratedDeriv s (fun z => ∑ j, (P j).eval z * Complex.exp (w j * z)) c‖ ≤ D)
    (n : ℕ) :
    ‖iteratedDeriv n (fun z => ∑ j, (P j).eval z * Complex.exp (w j * z)) c‖
      ≤ D * (W + 1) ^ (n + N) := by
  classical
  -- the derivative of `∑ Rⱼ(z) e^{wⱼ z}` is `∑ (Rⱼ' + wⱼ Rⱼ)(z) e^{wⱼ z}`
  have hder : ∀ (R : ι → ℂ[X]) (z : ℂ),
      HasDerivAt (fun y => ∑ j, (R j).eval y * Complex.exp (w j * y))
        (∑ j, (derivative (R j) + C (w j) * R j).eval z * Complex.exp (w j * z)) z :=
    fun R z => HasDerivAt.fun_sum fun j _ => by
      have h2 : HasDerivAt (fun y => Complex.exp (w j * y)) (Complex.exp (w j * z) * w j) z := by
        simpa using ((hasDerivAt_id z).const_mul (w j)).cexp
      exact (((R j).hasDerivAt z).mul h2).congr_deriv (by simp only [eval_add, eval_mul, eval_C]; ring)
  have hdiff : ∀ R : ι → ℂ[X], Differentiable ℂ (fun y => ∑ j, (R j).eval y * Complex.exp (w j * y)) :=
    fun R z => (hder R z).differentiableAt
  induction N generalizing q P D n with
  | zero =>
    have hP0 : ∀ j, P j = 0 := fun j => (hP j).resolve_right (by
      rw [Finset.sum_eq_zero_iff.1 hN j (Finset.mem_univ j)]; exact Nat.not_lt_zero _)
    simp only [hP0, eval_zero, zero_mul, Finset.sum_const_zero]
    rw [show (fun _ : ℂ => (0 : ℂ)) = 0 from rfl, iteratedDeriv_const_zero, norm_zero]
    positivity
  | succ N ih =>
    obtain ⟨j0, -, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hN.trans_ne N.succ_ne_zero)
    obtain ⟨Q, hQ⟩ : ∃ Q : ι → ℂ[X], ∀ j, Q j = derivative (P j) + C (w j - w j0) * P j :=
      ⟨_, fun _ => rfl⟩
    -- `f^{(k+1)}(c) = g^{(k)}(c) + w_{j₀} f^{(k)}(c)` with `g = ∑ Qⱼ(z) e^{wⱼ z}`
    have hsucc : ∀ k, iteratedDeriv (k + 1) (fun z => ∑ j, (P j).eval z * Complex.exp (w j * z)) c
        = iteratedDeriv k (fun z => ∑ j, (Q j).eval z * Complex.exp (w j * z)) c
          + w j0 * iteratedDeriv k (fun z => ∑ j, (P j).eval z * Complex.exp (w j * z)) c := by
      intro k
      have hd : deriv (fun z => ∑ j, (P j).eval z * Complex.exp (w j * z))
          = (fun z => ∑ j, (Q j).eval z * Complex.exp (w j * z))
            + fun z => w j0 * ∑ j, (P j).eval z * Complex.exp (w j * z) := by
        funext z
        rw [(hder P z).deriv, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hQ, eval_add, eval_mul, eval_C]; ring
      rw [iteratedDeriv_succ', hd, iteratedDeriv_add (hdiff Q).contDiff.contDiffAt
        ((hdiff P).const_mul _).contDiff.contDiffAt,
        iteratedDeriv_const_mul _ (hdiff P).contDiff.contDiffAt]
    -- the degree budget drops by one, at `j₀`
    have hQd : ∀ j, Q j = 0 ∨ (Q j).natDegree < Function.update q j0 (q j0 - 1) j := by
      intro j
      rw [hQ]
      by_cases hj : j = j0
      · subst hj
        simp only [sub_self, map_zero, zero_mul, add_zero, Function.update_self]
        rcases hP j with h | h
        · left; simp [h]
        · by_cases hd : (P j).natDegree = 0
          · left; exact derivative_of_natDegree_zero hd
          · right; have := natDegree_derivative_le (P j); omega
      · rw [Function.update_of_ne hj]
        rcases hP j with h | h
        · left; simp [h]
        · right
          calc (derivative (P j) + C (w j - w j0) * P j).natDegree
              ≤ max (derivative (P j)).natDegree (C (w j - w j0) * P j).natDegree :=
                natDegree_add_le _ _
            _ ≤ (P j).natDegree :=
                max_le ((natDegree_derivative_le _).trans (Nat.sub_le _ _)) (natDegree_C_mul_le _ _)
            _ < q j := h
    have hsum' : ∑ j, Function.update q j0 (q j0 - 1) j = N := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ j0), Finset.sdiff_singleton_eq_erase]
      have h2 := Finset.add_sum_erase Finset.univ q (Finset.mem_univ j0)
      omega
    have hDG : ∀ s < N,
        ‖iteratedDeriv s (fun z => ∑ j, (Q j).eval z * Complex.exp (w j * z)) c‖ ≤ D * (W + 1) := by
      intro s hs
      rw [eq_sub_of_add_eq (hsucc s).symm]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      exact (add_le_add (hD (s + 1) (by omega))
        (mul_le_mul (hW j0) (hD s (by omega)) (norm_nonneg _) hW0)).trans_eq (by ring)
    have ih' := ih (Function.update q j0 (q j0 - 1)) Q hQd hsum' (D * (W + 1)) (by positivity) hDG
    induction n with
    | zero =>
      exact (hD 0 (by omega)).trans (le_mul_of_one_le_right hD0 (one_le_pow₀ (by linarith)))
    | succ n ihn =>
      rw [hsucc n]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      exact (add_le_add (ih' n) (mul_le_mul (hW j0) ihn (norm_nonneg _) hW0)).trans_eq (by ring)
