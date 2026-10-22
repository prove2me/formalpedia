-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P09.weyl_phase_space_normalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:07:29.121371+00:00
-- url     : https://prove2.me/submissions/0028b28e-7669-49c5-8233-78f92a8d6d0f

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
noncomputable section
open scoped BigOperators ComplexConjugate
open QAlgorithms.Papers.Independent.Support21.P09
open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)
open QAlgorithms
open Matrix
open Fin.NatCast
open scoped ComplexOrder

theorem g68r_pd_eq {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) :
    pureDensity v = Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)) := by
  ext a b; rfl

theorem g68r_conj_pd {I : Type*} [Fintype I] (A : Matrix I I ℂ) (v : EuclideanSpace ℂ I) :
    A * pureDensity v * A.conjTranspose = pureDensity (act A v) := by
  rw [g68r_pd_eq, g68r_pd_eq, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  rfl

theorem g68r_pd_phase {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) (c : ℂ) (hc : ‖c‖ = 1) :
    pureDensity (c • v) = pureDensity v := by
  ext a b
  simp only [pureDensity, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, map_mul]
  have : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  linear_combination (v a * conj (v b)) * this

theorem g68r_S_mulVec (n : ℕ) (hn : 1 ≤ n) (v : Fin (n+1) → ℂ) :
    positiveShift (n+1) *ᵥ v = fun a => v (a - 1) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, positiveShift, Matrix.conjTranspose_apply,
    QAlgorithms.Papers.Independent.Frontier18.P17.shift]
  rw [Finset.sum_eq_single (a - 1)]
  · rw [if_pos]; · simp
    rw [Fin.val_sub, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
    have := a.isLt
    rw [show n + 1 - 1 + ↑a = ↑a + (n + 1) - 1 by omega]
  · intro b _ hb
    rw [if_neg, star_zero, zero_mul]
    intro h; apply hb
    ext
    rw [h, Fin.val_sub, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
    have := a.isLt
    rw [show n + 1 - 1 + ↑a = ↑a + (n + 1) - 1 by omega]
  · simp

theorem g68r_Spow_mulVec (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (v : Fin (n+1) → ℂ) :
    (positiveShift (n+1)) ^ j *ᵥ v = fun a => v (a - (j : Fin (n+1))) := by
  induction j generalizing v with
  | zero => funext a; simp
  | succ j ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, g68r_S_mulVec n hn, ih]
    funext a
    congr 1
    rw [Nat.cast_succ, sub_add_eq_sub_sub]

def g68r_om (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

theorem g68r_clock (m : ℕ) : clock m = Matrix.diagonal (fun a : Fin m => g68r_om m ^ a.val) := by
  unfold clock g68r_om
  congr 1
  funext a
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem g68r_Tpow_mulVec (m : ℕ) (l : ℕ) (v : Fin m → ℂ) :
    (clock m) ^ l *ᵥ v = fun a => g68r_om m ^ (a.val * l) * v a := by
  rw [g68r_clock, Matrix.diagonal_pow]
  funext a; rw [Matrix.mulVec_diagonal]; simp [pow_mul]

theorem g68r_om_pow_m (m : ℕ) (hm : m ≠ 0) : g68r_om m ^ m = 1 :=
  (Complex.isPrimitiveRoot_exp m hm).pow_eq_one

theorem g68r_om_mod (m : ℕ) (hm : m ≠ 0) (x : ℕ) : g68r_om m ^ x = g68r_om m ^ (x % m) := by
  conv_lhs => rw [← Nat.mod_add_div x m, pow_add, pow_mul, g68r_om_pow_m m hm, one_pow, mul_one]

theorem g68r_om_norm (m : ℕ) (x : ℕ) : ‖g68r_om m ^ x‖ = 1 := by
  rw [norm_pow, g68r_om, Complex.norm_exp]
  simp

theorem g68r_vec (n : ℕ) (hn : 1 ≤ n) (psi : EuclideanSpace ℂ (Fin (n+1))) (p : Fin (n+1) × Fin (n+1)) :
    WithLp.ofLp (act (positiveShift (n+1) ^ p.1.val * clock (n+1) ^ p.2.val) psi) =
      fun a => g68r_om (n+1) ^ ((a - p.1).val * p.2.val) * psi (a - p.1) := by
  show (positiveShift (n+1) ^ p.1.val * clock (n+1) ^ p.2.val) *ᵥ WithLp.ofLp psi = _
  rw [← Matrix.mulVec_mulVec, g68r_Tpow_mulVec, g68r_Spow_mulVec n hn, Fin.cast_val_eq_self]

theorem g68r_om_sub (m : ℕ) [NeZero m] (a b : Fin m) :
    g68r_om m ^ (a - b).val * g68r_om m ^ b.val = g68r_om m ^ a.val := by
  have hm : m ≠ 0 := NeZero.ne m
  rw [← pow_add, g68r_om_mod m hm, g68r_om_mod m hm a.val]
  congr 1
  rw [Fin.val_sub, Nat.mod_add_mod]
  have := b.isLt
  rw [show m - ↑b + ↑a + ↑b = ↑a + m by omega, Nat.add_mod_right]

theorem g68r_geom (m : ℕ) [NeZero m] (x y : Fin m) :
    ∑ l : Fin m, (g68r_om m ^ x.val * conj (g68r_om m ^ y.val)) ^ l.val = if x = y then (m : ℂ) else 0 := by
  have hm : m ≠ 0 := NeZero.ne m
  have hnorm : ∀ z : ℕ, g68r_om m ^ z * conj (g68r_om m ^ z) = 1 := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, g68r_om_norm]; simp
  split_ifs with h
  · subst h; rw [hnorm]; simp
  · set ζ := g68r_om m ^ x.val * conj (g68r_om m ^ y.val) with hζ
    have hcy : conj (g68r_om m ^ y.val) = (g68r_om m ^ y.val)⁻¹ := by
      have h1 := hnorm y.val
      have hne : g68r_om m ^ y.val ≠ 0 := by
        intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
      field_simp
      linear_combination h1
    have hζ1 : ζ ≠ 1 := by
      intro h1
      rw [hζ, hcy, mul_inv_eq_one₀] at h1
      · exact h (Fin.ext ((Complex.isPrimitiveRoot_exp m hm).pow_inj x.isLt y.isLt h1))
      · intro h0
        have := hnorm y.val
        rw [h0, zero_mul] at this; exact zero_ne_one this
    have hζm : ζ ^ m = 1 := by
      rw [hζ, mul_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm x.val, mul_comm y.val, pow_mul,
        pow_mul, g68r_om_pow_m m hm]; simp
    rw [Fin.sum_univ_eq_sum_range (fun i => ζ ^ i), geom_sum_eq hζ1, hζm]; simp

theorem g68r_T_mulVec (m : ℕ) (v : Fin m → ℂ) :
    clock m *ᵥ v = fun a => g68r_om m ^ a.val * v a := by
  simpa using g68r_Tpow_mulVec m 1 v

theorem g68r_Tfinal (n : ℕ) (p : Fin (n+1) × Fin (n+1)) (a : Fin (n+1)) (z : ℂ) :
    g68r_om (n+1) ^ a.val * (g68r_om (n+1) ^ ((a - p.1).val * p.2.val) * z) =
      g68r_om (n+1) ^ p.1.val * (g68r_om (n+1) ^ ((a - p.1).val * (p.2 + 1).val) * z) := by
  have hmne : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have e1 : g68r_om (n+1) ^ ((a - p.1).val * (p.2 + 1).val) =
      g68r_om (n+1) ^ ((a - p.1).val * (p.2.val + 1)) := by
    rw [g68r_om_mod (n+1) hmne, g68r_om_mod (n+1) hmne ((a - p.1).val * (p.2.val + 1))]
    congr 1
    rw [Fin.val_add, Fin.val_one', Nat.mul_mod, Nat.mod_mod, Nat.add_mod_mod, ← Nat.mul_mod]
  rw [e1, ← g68r_om_sub (n+1) a p.1]
  ring

theorem g68r_main (n : ℕ) (hn : 1 ≤ n)
    (psi : EuclideanSpace ℂ (Fin (n+1))) (hpsi : ‖psi‖ = 1) :
    IsPOVM (phaseSpaceEffect (n+1) psi) ∧
    (∀ p, phaseSpaceEffect (n+1) psi p ≠ 0) ∧
    (∀ U ∈ ({positiveShift (n+1), clock (n+1)} : Set _), ∀ p,
      ∃ q, U * phaseSpaceEffect (n+1) psi p * U.conjTranspose =
        phaseSpaceEffect (n+1) psi q) := by
  have hm0 : ((n+1) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsq : ∑ c, psi c * conj (psi c) = 1 := by
    have h := EuclideanSpace.norm_eq psi
    rw [hpsi] at h
    have h2 : ∑ c, ‖psi c‖ ^ 2 = 1 := by
      have := congrArg (· ^ 2) h
      simp only [one_pow] at this
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at this
      exact this.symm
    have : ∑ c, psi c * conj (psi c) = ((∑ c, ‖psi c‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [this, h2]; simp
  have hent : ∀ p a b, phaseSpaceEffect (n+1) psi p a b =
      (1 / (((n+1 : ℕ)) : ℂ)) * ((g68r_om (n+1) ^ ((a - p.1).val * p.2.val) * psi (a - p.1)) *
        conj (g68r_om (n+1) ^ ((b - p.1).val * p.2.val) * psi (b - p.1))) := by
    intro p a b
    simp only [phaseSpaceEffect, Matrix.smul_apply, smul_eq_mul]
    congr 1
    show (WithLp.ofLp (act _ psi)) a * conj ((WithLp.ofLp (act _ psi)) b) = _
    rw [g68r_vec n hn]
  refine ⟨⟨fun p => ?_, ?_⟩, ?_, ?_⟩
  · unfold phaseSpaceEffect
    refine Matrix.PosSemidef.smul ?_ ?_
    · rw [g68r_pd_eq]; exact Matrix.posSemidef_vecMulVec_self_star _
    · positivity
  · ext a b
    rw [Matrix.sum_apply, Fintype.sum_prod_type]
    simp only [hent]
    have hin : ∀ j : Fin (n+1), ∑ l : Fin (n+1), (1 / (((n+1 : ℕ)) : ℂ)) * ((g68r_om (n+1) ^ ((a - j).val * l.val) * psi (a - j)) *
        conj (g68r_om (n+1) ^ ((b - j).val * l.val) * psi (b - j))) =
        (1 / (((n+1 : ℕ)) : ℂ)) * (psi (a - j) * conj (psi (b - j))) *
          ∑ l : Fin (n+1), (g68r_om (n+1) ^ (a - j).val * conj (g68r_om (n+1) ^ (b - j).val)) ^ l.val := by
      intro j
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [mul_pow, ← pow_mul, map_mul, ← map_pow, ← pow_mul]
      ring
    simp only [hin, g68r_geom, sub_left_inj, Matrix.one_apply]
    split_ifs with h
    · subst h
      have : ∀ j : Fin (n+1), (1 / (((n+1 : ℕ)) : ℂ)) * (psi (a - j) * conj (psi (a - j))) * (((n+1 : ℕ)) : ℂ) =
          psi (a - j) * conj (psi (a - j)) := by
        intro j; field_simp
      simp only [this]
      rw [← hsq]
      exact (Equiv.subLeft a).sum_comp (fun c => psi c * conj (psi c))
    · simp
  · intro p h
    have hne : WithLp.ofLp psi ≠ 0 := by
      intro h0
      have : psi = 0 := by
        ext c; exact congrFun h0 c
      rw [this, norm_zero] at hpsi; exact zero_ne_one hpsi
    obtain ⟨c, hc⟩ : ∃ c, psi c ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hne (funext hcon)
    have := congrFun (congrFun h (c + p.1)) (c + p.1)
    rw [hent] at this
    simp only [add_sub_cancel_right, Matrix.zero_apply] at this
    have hω : g68r_om (n+1) ^ (c.val * p.2.val) * conj (g68r_om (n+1) ^ (c.val * p.2.val)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, g68r_om_norm]; simp
    have hp : psi c * conj (psi c) ≠ 0 := by
      rw [Complex.mul_conj]; exact Complex.ofReal_ne_zero.mpr (Complex.normSq_pos.mpr hc).ne'
    apply hp
    have h3 : (1 / (((n+1 : ℕ)) : ℂ)) * (psi c * conj (psi c)) = 0 := by
      rw [← this, map_mul]
      linear_combination (-(1 / (((n+1 : ℕ)) : ℂ)) * (psi c * conj (psi c))) * hω
    rcases mul_eq_zero.mp h3 with h4 | h4
    · simp at h4; exact absurd h4 hm0
    · exact h4
  · intro U hU p
    have hconj : ∀ (V : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (q : Fin (n+1) × Fin (n+1)),
        V * phaseSpaceEffect (n+1) psi q * V.conjTranspose =
          (1 / (((n+1 : ℕ)) : ℂ)) • pureDensity (act V (act (positiveShift (n+1) ^ q.1.val * clock (n+1) ^ q.2.val) psi)) := by
      intro V q
      rw [phaseSpaceEffect, Matrix.mul_smul, Matrix.smul_mul, g68r_conj_pd]
    rcases hU with rfl | hU
    · refine ⟨(p.1 + 1, p.2), ?_⟩
      rw [hconj, phaseSpaceEffect]
      congr 2
      apply WithLp.ofLp_injective
      funext a
      show (positiveShift (n+1) *ᵥ WithLp.ofLp (act _ psi)) a = WithLp.ofLp (act _ psi) a
      rw [g68r_S_mulVec n hn, g68r_vec n hn, g68r_vec n hn]
      simp only
      rw [sub_sub]
      rw [add_comm (1 : Fin (n+1))]
    · rw [Set.mem_singleton_iff] at hU
      subst hU
      refine ⟨(p.1, p.2 + 1), ?_⟩
      have hv : act (clock (n+1)) (act (positiveShift (n+1) ^ p.1.val * clock (n+1) ^ p.2.val) psi) =
          (g68r_om (n+1) ^ p.1.val) • act (positiveShift (n+1) ^ (p.1, p.2 + 1).1.val *
            clock (n+1) ^ (p.1, p.2 + 1).2.val) psi := by
        apply WithLp.ofLp_injective
        funext a
        show (clock (n+1) *ᵥ WithLp.ofLp (act _ psi)) a = g68r_om (n+1) ^ p.1.val * WithLp.ofLp (act _ psi) a
        rw [g68r_T_mulVec, g68r_vec n hn, g68r_vec n hn]
        simp only
        exact g68r_Tfinal n p a _
      rw [hconj, phaseSpaceEffect, hv, g68r_pd_phase _ _ (g68r_om_norm (n+1) _)]
theorem solution (k : ℕ) (hk : 2 ≤ k)
    (psi : EuclideanSpace ℂ (Fin (2 ^ k))) (hpsi : ‖psi‖ = 1) :
    IsPOVM (phaseSpaceEffect (2 ^ k) psi) ∧
    (∀ p, phaseSpaceEffect (2 ^ k) psi p ≠ 0) ∧
    (∀ U ∈ ({positiveShift (2 ^ k), clock (2 ^ k)} : Set _), ∀ p,
      ∃ q, U * phaseSpaceEffect (2 ^ k) psi p * U.conjTranspose =
        phaseSpaceEffect (2 ^ k) psi q) := by
  revert psi
  obtain ⟨n, hn⟩ : ∃ n, 2 ^ k = n + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hn1 : 1 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  rw [hn]
  intro psi hpsi
  exact g68r_main n hn1 psi hpsi
