-- Prove2me | solution 1 for TSPSDPGap.claim_4_18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:43:22.926593+00:00
-- url     : https://prove2.me/submissions/89dd3219-4272-4471-b5fd-8c97fcd38cf2

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat
import Definitions.Def_TSPSDPGap_aHat

namespace TSPSDPGap

namespace Aux_R6

open Finset

/-- additive character `x ↦ exp(2πi x / n)` on `ℤ`. -/
noncomputable def E (n : ℕ) (x : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) / (n : ℂ))

/-- the Fourier vectors `v_k(u) = exp(-2πi k u / n)`. -/
noncomputable def V (n k u : ℕ) : ℂ := E n (-((k : ℤ) * (u : ℤ)))

lemma E_add (n : ℕ) (a b : ℤ) : E n (a + b) = E n a * E n b := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_zero (n : ℕ) : E n 0 = 1 := by
  simp [E]

lemma E_mul_n (n : ℕ) (hn : 0 < n) (c : ℤ) : E n ((n : ℤ) * c) = 1 := by
  unfold E
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((((n : ℤ) * c : ℤ)) : ℂ) / (n : ℂ)
      = (c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [div_eq_iff hnC]
    push_cast
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I c

lemma E_periodic (n : ℕ) (hn : 0 < n) (a b : ℤ) (h : (n : ℤ) ∣ a - b) : E n a = E n b := by
  obtain ⟨c, hc⟩ := h
  have e : a = b + (n : ℤ) * c := by linarith
  rw [e, E_add, E_mul_n n hn, mul_one]

lemma E_one_iff (n : ℕ) (hn : 0 < n) (d : ℤ) : E n d = 1 ↔ (n : ℤ) ∣ d := by
  constructor
  · intro h
    unfold E at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨q, hq⟩ := h
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [div_eq_iff hnC] at hq
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) * ((d : ℂ) - (n : ℂ) * (q : ℂ)) = 0 := by
      linear_combination hq
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
    have h3 : (d : ℂ) = (n : ℂ) * (q : ℂ) := by
      have := (mul_eq_zero.mp h2).resolve_left h2pi
      linear_combination this
    exact ⟨q, by exact_mod_cast h3⟩
  · rintro ⟨c, rfl⟩
    exact E_mul_n n hn c

lemma E_pow (n : ℕ) (d : ℤ) (u : ℕ) : E n ((u : ℤ) * d) = (E n d) ^ u := by
  induction u with
  | zero => simp [E_zero]
  | succ u ih =>
    rw [pow_succ, ← ih, ← E_add]
    congr 1
    push_cast
    ring

lemma orth (n : ℕ) (hn : 0 < n) (d : ℤ) :
    ∑ u : Fin n, E n (((u : ℕ) : ℤ) * d) = if (n : ℤ) ∣ d then (n : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun u => E n ((u : ℤ) * d)) n]
  simp only [E_pow]
  split_ifs with h
  · rw [(E_one_iff n hn d).mpr h]
    simp
  · have hne : E n d ≠ 1 := fun h1 => h ((E_one_iff n hn d).mp h1)
    rw [geom_sum_eq hne]
    have hp : (E n d) ^ n = 1 := by
      rw [← E_pow]
      exact E_mul_n n hn d
    rw [hp, sub_self, zero_div]

lemma dvd_iff_eq (n : ℕ) (s t : Fin n) :
    (n : ℤ) ∣ ((t : ℕ) : ℤ) - ((s : ℕ) : ℤ) ↔ s = t := by
  have hs := s.isLt
  have ht := t.isLt
  constructor
  · intro h
    have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    ext
    omega
  · rintro rfl
    simp

lemma V_zero (n k : ℕ) : V n k 0 = 1 := by
  simp [V, E_zero]

/-- Fourier inversion: a vector with vanishing Fourier coefficients is zero. -/
lemma inv_zeroC (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ)
    (h : ∀ k : Fin n, ∑ s : Fin n, z s * V n k s = 0) : z = 0 := by
  funext t
  have e1 : ∀ k : Fin n, (∑ s : Fin n, z s * V n k s) * E n (((k : ℕ) : ℤ) * ((t : ℕ) : ℤ))
      = ∑ s : Fin n, z s * E n (((k : ℕ) : ℤ) * (((t : ℕ) : ℤ) - ((s : ℕ) : ℤ))) := by
    intro k
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    unfold V
    rw [mul_assoc, ← E_add]
    congr 2
    ring
  have key : ∑ k : Fin n, (∑ s : Fin n, z s * V n k s) * E n (((k : ℕ) : ℤ) * ((t : ℕ) : ℤ))
      = (n : ℂ) * z t := by
    rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_comm]
    rw [Finset.sum_eq_single t]
    · rw [← Finset.mul_sum, orth n hn, if_pos (by simp)]
      ring
    · intro s _ hst
      rw [← Finset.mul_sum, orth n hn, if_neg, mul_zero]
      rw [dvd_iff_eq]
      exact hst
    · intro h
      exact absurd (Finset.mem_univ t) h
  have h0 : (n : ℂ) * z t = 0 := by
    rw [← key]
    simp [h]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_eq_zero.mp h0).resolve_left hnC

lemma inv_zeroR (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (h : ∀ k : Fin n, ∑ s : Fin n, ((x s : ℝ) : ℂ) * V n k s = 0) : x = 0 := by
  have hz := inv_zeroC n hn (fun s => ((x s : ℝ) : ℂ)) h
  funext s
  have := congrFun hz s
  simpa using this

lemma mod2 (a n : ℕ) (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma E_modn (n : ℕ) (hn : 0 < n) (k x : ℕ) :
    E n (-((k : ℤ) * (((x % n : ℕ)) : ℤ))) = E n (-((k : ℤ) * (x : ℤ))) := by
  apply E_periodic n hn
  have hmd : (((x % n : ℕ)) : ℤ) + (n : ℤ) * (((x / n : ℕ)) : ℤ) = (x : ℤ) := by
    exact_mod_cast Nat.mod_add_div x n
  refine ⟨(k : ℤ) * (((x / n : ℕ)) : ℤ), ?_⟩
  linear_combination (-(k : ℤ)) * hmd

lemma circ_symm (m i : ℕ) (s t : Fin m) : circBasis m i s t = circBasis m i t s := by
  unfold circBasis
  simp only [Matrix.of_apply]
  ring

/-- `circBasis n i` acts on the Fourier vector `v_k` by the scalar `2 cos(2π i k / n)`. -/
lemma circ_eig (n i k : ℕ) (hi1 : 1 ≤ i) (hin : i < n) (s : Fin n) :
    ∑ t : Fin n, ((circBasis n i s t : ℝ) : ℂ) * V n k t
      = ((2 * Real.cos (2 * Real.pi * i * k / n) : ℝ) : ℂ) * V n k s := by
  have hn : 0 < n := by omega
  have hs := s.isLt
  obtain ⟨t1, ht1⟩ : ∃ t1 : Fin n, (t1 : ℕ) = ((s : ℕ) + i) % n :=
    ⟨⟨_, Nat.mod_lt _ hn⟩, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ t2 : Fin n, (t2 : ℕ) = ((s : ℕ) + n - i) % n :=
    ⟨⟨_, Nat.mod_lt _ hn⟩, rfl⟩
  have h1 : ∀ t : Fin n, (((t : ℕ) + n - s) % n = i ↔ t = t1) := by
    intro t
    have := t.isLt
    rw [Fin.ext_iff, ht1]
    rw [mod2 _ _ (by omega), mod2 ((s : ℕ) + i) n (by omega)]
    split_ifs <;> omega
  have h2 : ∀ t : Fin n, (((s : ℕ) + n - t) % n = i ↔ t = t2) := by
    intro t
    have := t.isLt
    rw [Fin.ext_iff, ht2]
    rw [mod2 _ _ (by omega), mod2 ((s : ℕ) + n - i) n (by omega)]
    split_ifs <;> omega
  have hc : ∀ t : Fin n, ((circBasis n i s t : ℝ) : ℂ)
      = (if t = t1 then (1 : ℂ) else 0) + (if t = t2 then (1 : ℂ) else 0) := by
    intro t
    unfold circBasis
    simp only [Matrix.of_apply, Nat.mod_eq_of_lt hin, h1, h2]
    split_ifs <;> norm_num
  have hsum : ∑ t : Fin n, ((circBasis n i s t : ℝ) : ℂ) * V n k t = V n k t1 + V n k t2 := by
    calc ∑ t : Fin n, ((circBasis n i s t : ℝ) : ℂ) * V n k t
        = ∑ t : Fin n, ((if t = t1 then V n k t else 0) + (if t = t2 then V n k t else 0)) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [hc t]
          split_ifs <;> ring
      _ = V n k t1 + V n k t2 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
            if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  rw [hsum]
  have e1 : V n k t1 = V n k s * E n (-((k : ℤ) * (i : ℤ))) := by
    unfold V
    rw [ht1, E_modn n hn, ← E_add]
    congr 1
    push_cast
    ring
  have e2 : V n k t2 = V n k s * E n ((k : ℤ) * (i : ℤ)) := by
    unfold V
    rw [ht2, E_modn n hn, ← E_add]
    apply E_periodic n hn
    refine ⟨-(k : ℤ), ?_⟩
    push_cast [Nat.cast_sub (show i ≤ (s : ℕ) + n by omega)]
    ring
  have hcos : E n ((k : ℤ) * (i : ℤ)) + E n (-((k : ℤ) * (i : ℤ)))
      = ((2 * Real.cos (2 * Real.pi * i * k / n) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.two_cos]
    unfold E
    congr 1 <;> congr 1 <;> push_cast <;> ring
  rw [e1, e2, ← hcos]
  ring

lemma comb_apply (n : ℕ) (c : ℕ → ℝ) (s t : Fin n) :
    (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t
      = ∑ i ∈ Finset.Icc 1 (n / 2), c i * circBasis n i s t := by
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]

lemma comb_symm (n : ℕ) (c : ℕ → ℝ) (s t : Fin n) :
    (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t
      = (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) t s := by
  rw [comb_apply, comb_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [circ_symm]

lemma comb_eig (n k : ℕ) (hn2 : 2 ≤ n) (c : ℕ → ℝ) (s : Fin n) :
    ∑ t : Fin n, (((∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t : ℝ) : ℂ) * V n k t
      = ((2 * ∑ i ∈ Finset.Icc 1 (n / 2), c i * Real.cos (2 * Real.pi * i * k / n) : ℝ) : ℂ)
          * V n k s := by
  calc ∑ t : Fin n, (((∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t : ℝ) : ℂ) * V n k t
      = ∑ i ∈ Finset.Icc 1 (n / 2), ((c i : ℝ) : ℂ)
          * ∑ t : Fin n, ((circBasis n i s t : ℝ) : ℂ) * V n k t := by
        simp only [comb_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun t _ => by ring))
    _ = ∑ i ∈ Finset.Icc 1 (n / 2), ((c i : ℝ) : ℂ)
          * (((2 * Real.cos (2 * Real.pi * i * k / n) : ℝ) : ℂ) * V n k s) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_Icc.mp hi
        rw [circ_eig n i k hi'.1 (by omega) s]
    _ = ((2 * ∑ i ∈ Finset.Icc 1 (n / 2), c i * Real.cos (2 * Real.pi * i * k / n) : ℝ) : ℂ)
          * V n k s := by
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => by ring)

/-- column form of `comb_eig`, using symmetry. -/
lemma comb_eig_col (n k : ℕ) (hn2 : 2 ≤ n) (c : ℕ → ℝ) (t : Fin n) :
    ∑ s : Fin n, (((∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t : ℝ) : ℂ) * V n k s
      = ((2 * ∑ i ∈ Finset.Icc 1 (n / 2), c i * Real.cos (2 * Real.pi * i * k / n) : ℝ) : ℂ)
          * V n k t := by
  rw [← comb_eig n k hn2 c t]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [comb_symm]

lemma mem_spec {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (r : ℝ) :
    r ∈ spectrum ℝ M ↔ ∃ v : ι → ℝ, v ≠ 0 ∧ M.mulVec v = r • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  have key : ∀ v : ι → ℝ, (algebraMap ℝ (Matrix ι ι ℝ) r - M).mulVec v = r • v - M.mulVec v := by
    intro v
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [key, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [key, h, sub_self]

/-- spectrum of a real symmetric matrix diagonalised by the Fourier vectors. -/
lemma spec_circ (n : ℕ) (hn : 0 < n) (C : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ)
    (hsym : ∀ s t, C s t = C t s)
    (heig : ∀ (k : Fin n) (s : Fin n),
      ∑ t : Fin n, ((C s t : ℝ) : ℂ) * V n k t = ((lam k : ℝ) : ℂ) * V n k s) :
    spectrum ℝ C = Set.range lam := by
  ext r
  rw [mem_spec]
  constructor
  · rintro ⟨x, hx0, hx⟩
    by_contra hr
    apply hx0
    apply inv_zeroR n hn x
    intro k
    have hne : r ≠ lam k := fun h => hr ⟨k, h.symm⟩
    have key : ((r : ℝ) : ℂ) * ∑ s : Fin n, ((x s : ℝ) : ℂ) * V n k s
        = ((lam k : ℝ) : ℂ) * ∑ s : Fin n, ((x s : ℝ) : ℂ) * V n k s := by
      have hxs : ∀ s, ((r : ℝ) : ℂ) * ((x s : ℝ) : ℂ)
          = ∑ t : Fin n, ((C s t : ℝ) : ℂ) * ((x t : ℝ) : ℂ) := by
        intro s
        have := congrFun hx s
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
        rw [← Complex.ofReal_mul, ← this]
        simp only [Complex.ofReal_sum, Complex.ofReal_mul]
      calc ((r : ℝ) : ℂ) * ∑ s : Fin n, ((x s : ℝ) : ℂ) * V n k s
          = ∑ s : Fin n, (∑ t : Fin n, ((C s t : ℝ) : ℂ) * ((x t : ℝ) : ℂ)) * V n k s := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [← hxs s]
            ring
        _ = ∑ t : Fin n, ((x t : ℝ) : ℂ) * ∑ s : Fin n, ((C t s : ℝ) : ℂ) * V n k s := by
            simp only [Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [hsym s t]
            ring
        _ = ∑ t : Fin n, ((x t : ℝ) : ℂ) * (((lam k : ℝ) : ℂ) * V n k t) := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [heig k t]
        _ = ((lam k : ℝ) : ℂ) * ∑ s : Fin n, ((x s : ℝ) : ℂ) * V n k s := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t _ => by ring)
    have hne' : ((r : ℝ) : ℂ) - ((lam k : ℝ) : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hne
    have h0 : (((r : ℝ) : ℂ) - ((lam k : ℝ) : ℂ)) * ∑ s : Fin n, ((x s : ℝ) : ℂ) * V n k s = 0 := by
      rw [sub_mul, key, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hne'
  · rintro ⟨k, rfl⟩
    refine ⟨fun s => (V n k s).re, ?_, ?_⟩
    · intro h
      have h1 := congrFun h ⟨0, hn⟩
      simp only [Fin.val_mk, V_zero, Complex.one_re, Pi.zero_apply] at h1
      exact absurd h1 (by norm_num)
    · ext s
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      have := congrArg Complex.re (heig k s)
      rw [Complex.re_sum] at this
      simp only [Complex.re_ofReal_mul] at this
      exact this

end Aux_R6

end TSPSDPGap

namespace TSPSDPGap

namespace Aux_R6

open Finset

/-- `b̂ₖ` (same formula as `bHat`). -/
noncomputable def bH (g n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2), coeffB g n i * Real.cos (2 * Real.pi * i * k / n)

lemma tel (θ : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    2 * Real.sin (θ / 2) * ∑ i ∈ Finset.Ico 1 M, Real.cos (i * θ)
      = Real.sin ((M - 1 / 2) * θ) - Real.sin (θ / 2) := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, Nat.cast_one]
    rw [show ((1:ℝ) - 1 / 2) * θ = θ / 2 by ring, sub_self]
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM, mul_add, ih, Nat.cast_succ,
      show ((M:ℝ) + 1 - 1 / 2) * θ = M * θ + θ / 2 by ring,
      show ((M:ℝ) - 1 / 2) * θ = M * θ - θ / 2 by ring, Real.sin_add, Real.sin_sub]
    ring

lemma cos_sum (m j : ℕ) (hm : 1 ≤ m) (hj1 : 1 ≤ j) (hj2 : j < 2 * m) :
    2 * ∑ i ∈ Finset.Ico 1 m, Real.cos (Real.pi * i * j / m) + Real.cos (Real.pi * m * j / m)
      = -1 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hj2R : (j:ℝ) < 2 * m := by exact_mod_cast hj2
  have hj1R : (1:ℝ) ≤ j := by exact_mod_cast hj1
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.pi * j / m := ⟨_, rfl⟩
  have e1 : ∀ i : ℕ, Real.pi * (i:ℝ) * j / m = i * θ := by
    intro i; rw [hθ]; ring
  have hcm : Real.cos (Real.pi * (m:ℝ) * j / m) = Real.cos (j * Real.pi) := by
    rw [show Real.pi * (m:ℝ) * j / m = j * Real.pi * ((m:ℝ) / m) by ring, div_self hmR.ne',
      mul_one]
  rw [hcm]
  simp only [e1]
  have hsinpos : 0 < Real.sin (θ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hθ]
      exact div_pos (div_pos (mul_pos Real.pi_pos (by linarith)) hmR) (by norm_num)
    · rw [hθ, div_div, div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  have htel := tel θ m hm
  have hmθ : ((m:ℝ) - 1 / 2) * θ = j * Real.pi - θ / 2 := by
    have : (m:ℝ) * θ = j * Real.pi := by
      rw [hθ, mul_div_assoc', div_eq_iff hmR.ne']; ring
    linear_combination this
  have hend : Real.sin (((m:ℝ) - 1 / 2) * θ) = -Real.cos (j * Real.pi) * Real.sin (θ / 2) := by
    rw [hmθ, Real.sin_sub, Real.sin_nat_mul_pi]
    ring
  have hprod : Real.sin (θ / 2) * (2 * ∑ i ∈ Finset.Ico 1 m, Real.cos (i * θ)
      + Real.cos (j * Real.pi) + 1) = 0 := by
    linear_combination htel + hend
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · linarith

lemma gauss (g : ℕ) : 2 * ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) = g * ((g:ℝ) - 1) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ g)]
      have e : ∑ j ∈ Finset.Ico 1 g, (((g + 1 : ℕ) : ℝ) - j)
          = ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) + ∑ j ∈ Finset.Ico 1 g, (1:ℝ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        push_cast
        ring
      rw [e, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ g)]
      push_cast
      linear_combination ih

/-- `∑ aᵢ = 1`, `∑ bᵢ = 1` (so `â₀ = b̂₀ = 1`) and the relation between `b̂ₖ` and `âₖ` for `k ≠ 0`. -/
lemma coeff_facts (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    aHat g n 0 = 1 ∧ bH g n 0 = 1 ∧
    ∀ k : ℕ, 1 ≤ k → k < n →
      bH g n k = (-(g:ℝ) - ((n:ℝ) - g) * aHat g n k) / ((n:ℝ) * ((g:ℝ) - 1)) := by
  obtain ⟨q, hq⟩ := hgn
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> omega
    · exact h
  have hn4 : 4 ≤ n := by rw [hq]; nlinarith
  have hneven : Even n := by rw [hq]; exact hg.mul_right q
  obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
  have hm2 : 2 * m = n := by rw [hm]; exact Nat.two_mul_div_two_of_even hneven
  have hm1 : 1 ≤ m := by omega
  have hm2R : 2 * (m:ℝ) = n := by exact_mod_cast hm2
  have hmR : (0:ℝ) < m := by exact_mod_cast hm1
  have hg0 : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hng : (0:ℝ) < (n:ℝ) - g := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hg1 : (0:ℝ) < (g:ℝ) - 1 := by
    have : (2:ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hn0 : (0:ℝ) < n := by linarith
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hA_lt : ∀ i ∈ Finset.Ico 1 m, coeffA g n i = 1 / ((n:ℝ) - g) * (2 + 4 / (g:ℝ) *
      ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (Real.pi * i * j / m)) := by
    intro i hi
    unfold coeffA
    rw [← hm, if_pos (Finset.mem_Ico.mp hi).2]
  have hA_m : coeffA g n m = 1 / ((n:ℝ) - g) * (1 + 2 / (g:ℝ) *
      ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (Real.pi * m * j / m)) := by
    unfold coeffA
    rw [← hm, if_neg (lt_irrefl m)]
  obtain ⟨S1, hS1⟩ : ∃ S1 : ℝ, S1 = ∑ i ∈ Finset.Ico 1 m,
      ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (Real.pi * i * j / m) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S2 : ℝ, S2 =
      ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (Real.pi * m * j / m) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) := ⟨_, rfl⟩
  have hGv : 2 * G = g * ((g:ℝ) - 1) := by rw [hG]; exact gauss g
  have hW : 2 * S1 + S2 = -G := by
    have hS1' : S1 = ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) *
        ∑ i ∈ Finset.Ico 1 m, Real.cos (Real.pi * i * j / m) := by
      rw [hS1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
    rw [hS1', hS2, hG, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj := Finset.mem_Ico.mp hj
    have hc := cos_sum m j hm1 hj.1 (by omega)
    linear_combination ((g:ℝ) - j) * hc
  have hsumIco : ∑ i ∈ Finset.Ico 1 m, coeffA g n i
      = 1 / ((n:ℝ) - g) * (2 * ((m:ℝ) - 1) + 4 / (g:ℝ) * S1) := by
    rw [Finset.sum_congr rfl hA_lt, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_sub hm1, Nat.cast_one, hS1]
    ring
  have hsplitA : ∑ i ∈ Finset.Ico 1 m, coeffA g n i + coeffA g n m = 1 := by
    rw [hsumIco, hA_m, ← hS2]
    have e1 : (2 / (g:ℝ)) * G = (g:ℝ) - 1 := by
      rw [show (2 / (g:ℝ)) * G = (2 * G) / g by ring, hGv, mul_div_cancel_left₀ _ hg0.ne']
    calc 1 / ((n:ℝ) - g) * (2 * ((m:ℝ) - 1) + 4 / (g:ℝ) * S1)
          + 1 / ((n:ℝ) - g) * (1 + 2 / (g:ℝ) * S2)
        = 1 / ((n:ℝ) - g) * (2 * (m:ℝ) - 1 + (2 / (g:ℝ)) * (2 * S1 + S2)) := by ring
      _ = 1 / ((n:ℝ) - g) * ((n:ℝ) - g) := by
          rw [hW, mul_neg, e1]
          congr 1
          linarith
      _ = 1 := one_div_mul_cancel hng.ne'
  have hsumA : ∑ i ∈ Finset.Icc 1 (n / 2), coeffA g n i = 1 := by
    rw [← hm, hIcc, Finset.sum_Ico_succ_top hm1]
    exact hsplitA
  have hB_lt : ∀ i ∈ Finset.Ico 1 m, coeffB g n i
      = (2 * (g:ℝ) - ((n:ℝ) - g) * coeffA g n i) / ((n:ℝ) * ((g:ℝ) - 1)) := by
    intro i hi
    unfold coeffB
    rw [← hm, if_pos (Finset.mem_Ico.mp hi).2]
  have hB_m : coeffB g n m = ((g:ℝ) - ((n:ℝ) - g) * coeffA g n m) / ((n:ℝ) * ((g:ℝ) - 1)) := by
    unfold coeffB
    rw [← hm, if_neg (lt_irrefl m)]
  have hD : (n:ℝ) * ((g:ℝ) - 1) ≠ 0 := (mul_pos hn0 hg1).ne'
  have hsumB : ∑ i ∈ Finset.Icc 1 (n / 2), coeffB g n i = 1 := by
    rw [← hm, hIcc, Finset.sum_Ico_succ_top hm1, Finset.sum_congr rfl hB_lt, hB_m,
      ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      ← Finset.mul_sum, Nat.cast_sub hm1, Nat.cast_one, ← add_div,
      div_eq_one_iff_eq hD]
    linear_combination (-((n:ℝ) - g)) * hsplitA + (g:ℝ) * hm2R
  refine ⟨?_, ?_, ?_⟩
  · unfold aHat
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one]
    exact hsumA
  · unfold bH
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one]
    exact hsumB
  · intro k hk1 hkn
    have hcc : ∀ i : ℕ, Real.cos (2 * Real.pi * i * k / n) = Real.cos (Real.pi * i * k / m) := by
      intro i
      congr 1
      rw [← hm2R, div_eq_div_iff (mul_ne_zero two_ne_zero hmR.ne') hmR.ne']
      ring
    obtain ⟨Sc, hSc⟩ : ∃ Sc : ℝ, Sc = ∑ i ∈ Finset.Ico 1 m, Real.cos (2 * Real.pi * i * k / n) :=
      ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ i ∈ Finset.Ico 1 m,
        coeffA g n i * Real.cos (2 * Real.pi * i * k / n) := ⟨_, rfl⟩
    have hS : 2 * Sc + Real.cos (2 * Real.pi * m * k / n) = -1 := by
      rw [hSc, hcc m]
      simp only [hcc]
      exact cos_sum m k hm1 hk1 (by omega)
    have haH : aHat g n k = T + coeffA g n m * Real.cos (2 * Real.pi * m * k / n) := by
      unfold aHat
      rw [← hm, hIcc, Finset.sum_Ico_succ_top hm1, hT]
    have hbH : bH g n k = (2 * (g:ℝ) * Sc - ((n:ℝ) - g) * T) / ((n:ℝ) * ((g:ℝ) - 1))
        + ((g:ℝ) - ((n:ℝ) - g) * coeffA g n m) / ((n:ℝ) * ((g:ℝ) - 1))
          * Real.cos (2 * Real.pi * m * k / n) := by
      unfold bH
      rw [← hm, hIcc, Finset.sum_Ico_succ_top hm1, hB_m]
      congr 1
      rw [hSc, hT, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hB_lt i hi]
      ring
    rw [hbH, haH, div_mul_eq_mul_div, ← add_div, div_left_inj' hD]
    linear_combination (g:ℝ) * hS

/-- block entries of `2n·Y`. -/
noncomputable def Kb (g n : ℕ) (a b s t : Fin n) : ℝ :=
  if a = b then (if s = t then 2 else 0)
  else if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then Amat g n s t else Bmat g n s t

/-- Fourier symbol of the blocks. -/
noncomputable def Lam (g n k : ℕ) (a b : Fin n) : ℝ :=
  if a = b then 2
  else if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then 2 * aHat g n k else 2 * bH g n k

lemma M_apply (g n : ℕ) (hn : 0 < n) (a s b t : Fin n) :
    ((2 * (n : ℝ)) • Ymat g n) (a, s) (b, t) = Kb g n a b s t := by
  have h2n : (2 * (n : ℝ)) ≠ 0 := by positivity
  rw [Matrix.smul_apply, smul_eq_mul]
  unfold Ymat Kb
  simp only [Matrix.of_apply]
  rw [← mul_assoc, mul_one_div_cancel h2n, one_mul]

lemma Kb_symm (g n : ℕ) (a b s t : Fin n) : Kb g n a b s t = Kb g n a b t s := by
  unfold Kb
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl]
    by_cases hst : s = t
    · subst hst
      rfl
    · rw [if_neg hst, if_neg (Ne.symm hst)]
  · rw [if_neg hab, if_neg hab]
    by_cases hg : (a : ℕ) / (n / g) = (b : ℕ) / (n / g)
    · rw [if_pos hg, if_pos hg]
      unfold Amat
      exact comb_symm n (coeffA g n) s t
    · rw [if_neg hg, if_neg hg]
      unfold Bmat
      exact comb_symm n (coeffB g n) s t

lemma Kb_row (g n : ℕ) (hn2 : 2 ≤ n) (k : ℕ) (a b s : Fin n) :
    ∑ t : Fin n, ((Kb g n a b s t : ℝ) : ℂ) * V n k t = ((Lam g n k a b : ℝ) : ℂ) * V n k s := by
  unfold Kb Lam
  by_cases hab : a = b
  · subst hab
    simp only [eq_self_iff_true, if_true]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ hts
      rw [if_neg (Ne.symm hts)]
      simp
    · intro h
      exact absurd (Finset.mem_univ s) h
  · simp only [if_neg hab]
    by_cases hg : (a : ℕ) / (n / g) = (b : ℕ) / (n / g)
    · simp only [if_pos hg]
      unfold Amat aHat
      exact comb_eig n k hn2 (coeffA g n) s
    · simp only [if_neg hg]
      unfold Bmat bH
      exact comb_eig n k hn2 (coeffB g n) s

lemma Kb_col (g n : ℕ) (hn2 : 2 ≤ n) (k : ℕ) (a b t : Fin n) :
    ∑ s : Fin n, ((Kb g n a b s t : ℝ) : ℂ) * V n k s = ((Lam g n k a b : ℝ) : ℂ) * V n k t := by
  rw [← Kb_row g n hn2 k a b t]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Kb_symm]

lemma Kb_row_re (g n : ℕ) (hn2 : 2 ≤ n) (k : ℕ) (a b s : Fin n) :
    ∑ t : Fin n, Kb g n a b s t * (V n k t).re = Lam g n k a b * (V n k s).re := by
  have := congrArg Complex.re (Kb_row g n hn2 k a b s)
  rw [Complex.re_sum] at this
  simp only [Complex.re_ofReal_mul] at this
  exact this

lemma ite_sum {R : Type*} [CommRing R] (n q : ℕ) (x y z : R) (Z : Fin n → R) (a : Fin n) :
    ∑ b : Fin n, (if a = b then x else if (a : ℕ) / q = (b : ℕ) / q then y else z) * Z b
      = (x - y) * Z a + (y - z) * ∑ b : Fin n, (if (a : ℕ) / q = (b : ℕ) / q then Z b else 0)
        + z * ∑ b : Fin n, Z b := by
  have e : ∀ b : Fin n, (if a = b then x else if (a : ℕ) / q = (b : ℕ) / q then y else z) * Z b
      = (if a = b then (x - y) * Z b else 0)
        + (y - z) * (if (a : ℕ) / q = (b : ℕ) / q then Z b else 0) + z * Z b := by
    intro b
    by_cases h1 : a = b
    · have h2 : (a : ℕ) / q = (b : ℕ) / q := by rw [h1]
      simp only [if_pos h1, if_pos h2]
      ring
    · simp only [if_neg h1]
      by_cases h2 : (a : ℕ) / q = (b : ℕ) / q
      · simp only [if_pos h2]
        ring
      · simp only [if_neg h2]
        ring
  rw [Finset.sum_congr rfl (fun b _ => e b), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]

lemma Lam_C (g n k : ℕ) (a b : Fin n) :
    ((Lam g n k a b : ℝ) : ℂ) = if a = b then (2 : ℂ) else
      if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then ((2 * aHat g n k : ℝ) : ℂ)
      else ((2 * bH g n k : ℝ) : ℂ) := by
  unfold Lam
  split_ifs <;> norm_num

lemma grp_card (n q g : ℕ) (hq : 0 < q) (hn : n = g * q) (a : Fin n) :
    (Finset.univ.filter (fun b : Fin n => (a : ℕ) / q = (b : ℕ) / q)).card = q := by
  have ha := a.isLt
  have hc : (a : ℕ) / q < g := by
    rw [Nat.div_lt_iff_lt_mul hq]
    omega
  obtain ⟨c, hcdef⟩ : ∃ c, c = (a : ℕ) / q := ⟨_, rfl⟩
  rw [← hcdef] at hc
  rw [← Finset.card_map Fin.valEmbedding]
  have hset : (Finset.univ.filter (fun b : Fin n => (a : ℕ) / q = (b : ℕ) / q)).map
      Fin.valEmbedding = Finset.Ico (c * q) (c * q + q) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [← hcdef] at hb
      have h1 := Nat.div_mul_le_self (b : ℕ) q
      have h2 : (b : ℕ) < ((b : ℕ) / q + 1) * q := (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
      rw [← hb] at h1 h2
      rw [add_mul, one_mul] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have h3 : (c + 1) * q ≤ g * q := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hc)
      rw [add_mul, one_mul] at h3
      have hxn : x < n := by omega
      refine ⟨⟨x, hxn⟩, ?_, rfl⟩
      rw [← hcdef]
      have e1 : c ≤ x / q := (Nat.le_div_iff_mul_le hq).mpr h1
      have e2 : x / q < c + 1 := (Nat.div_lt_iff_lt_mul hq).mpr (by rw [add_mul, one_mul]; exact h2)
      show c = x / q
      omega
  rw [hset, Nat.card_Ico]
  omega

lemma grp_sum {R : Type*} [CommRing R] (n q g : ℕ) (hq : 0 < q) (hn : n = g * q) (a : Fin n)
    (w : R) : ∑ b : Fin n, (if (a : ℕ) / q = (b : ℕ) / q then w else 0) = (q : R) * w := by
  rw [← Finset.sum_filter, Finset.sum_const, grp_card n q g hq hn a, nsmul_eq_mul]

lemma grp_sum' {R : Type*} [CommRing R] (n q g : ℕ) (hq : 0 < q) (hn : n = g * q) (b : Fin n)
    (w : R) : ∑ a : Fin n, (if (a : ℕ) / q = (b : ℕ) / q then w else 0) = (q : R) * w := by
  rw [← grp_sum n q g hq hn b w]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : (a : ℕ) / q = (b : ℕ) / q
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma grp_sum_c {R : Type*} [CommRing R] (n q g : ℕ) (hq : 0 < q) (hn : n = g * q) (c : ℕ)
    (hc : c < g) (w : R) : ∑ b : Fin n, (if (b : ℕ) / q = c then w else 0) = (q : R) * w := by
  have hcn : c * q < n := by
    rw [hn]
    exact Nat.mul_lt_mul_of_pos_right hc hq
  have hdiv : (c * q) / q = c := Nat.mul_div_cancel c hq
  rw [← grp_sum n q g hq hn ⟨c * q, hcn⟩ w]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Fin.val_mk, hdiv]
  by_cases h : (b : ℕ) / q = c
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma sig_grp {R : Type*} [CommRing R] (n q g : ℕ) (hq : 0 < q) (hn : n = g * q) (f : ℕ → R)
    (a : Fin n) :
    ∑ b : Fin n, (if (a : ℕ) / q = (b : ℕ) / q then f ((b : ℕ) / q) else 0)
      = (q : R) * f ((a : ℕ) / q) := by
  rw [← grp_sum n q g hq hn a (f ((a : ℕ) / q))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases h : (a : ℕ) / q = (b : ℕ) / q
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h]

/-- Fourier coefficients of a vector on `Fin n × Fin n` in the second coordinate. -/
noncomputable def ZZ (n : ℕ) (X : Fin n × Fin n → ℝ) (k a : Fin n) : ℂ :=
  ∑ s : Fin n, ((X (a, s) : ℝ) : ℂ) * V n k s

/-- every eigenvalue of `2nY` is one of three explicit values for some frequency `k`. -/
lemma spec_sub (g n : ℕ) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) (r : ℝ)
    (hr : r ∈ spectrum ℝ ((2 * (n : ℝ)) • Ymat g n)) :
    ∃ k : Fin n, r = 2 - 2 * aHat g n k ∨
      r = (2 - 2 * aHat g n k) + (2 * aHat g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ) ∨
      r = (2 - 2 * aHat g n k) + (2 * aHat g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ)
        + 2 * bH g n k * (n : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hn : 0 < n := by omega
  obtain ⟨q0, hq0⟩ := hgn
  have hqpos : 0 < n / g := by
    rw [hq0, Nat.mul_div_cancel_left q0 (by omega)]
    rcases Nat.eq_zero_or_pos q0 with h | h
    · subst h; omega
    · exact h
  have hnq : n = g * (n / g) := by
    rw [hq0, Nat.mul_div_cancel_left q0 (by omega)]
  obtain ⟨X, hX0, hX⟩ := (mem_spec _ r).mp hr
  have hZ : ∃ k a : Fin n, ZZ n X k a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hX0
    funext p
    obtain ⟨a, s⟩ := p
    have := inv_zeroR n hn (fun s => X (a, s)) (fun k => hcon k a)
    exact congrFun this s
  obtain ⟨k, a0, hZ0⟩ := hZ
  refine ⟨k, ?_⟩
  -- the eigen-equation in Fourier space
  have heq : ∀ a : Fin n, ((r : ℝ) : ℂ) * ZZ n X k a
      = ∑ b : Fin n, ((Lam g n k a b : ℝ) : ℂ) * ZZ n X k b := by
    intro a
    have hXa : ∀ s : Fin n, ((r : ℝ) : ℂ) * ((X (a, s) : ℝ) : ℂ)
        = ∑ b : Fin n, ∑ t : Fin n, ((Kb g n a b s t : ℝ) : ℂ) * ((X (b, t) : ℝ) : ℂ) := by
      intro s
      have := congrFun hX (a, s)
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, M_apply g n hn] at this
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [← Complex.ofReal_mul, ← this]
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    calc ((r : ℝ) : ℂ) * ZZ n X k a
        = ∑ s : Fin n, (∑ b : Fin n, ∑ t : Fin n,
            ((Kb g n a b s t : ℝ) : ℂ) * ((X (b, t) : ℝ) : ℂ)) * V n k s := by
          unfold ZZ
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [← hXa s]
          ring
      _ = ∑ b : Fin n, ∑ t : Fin n, ((X (b, t) : ℝ) : ℂ)
            * ∑ s : Fin n, ((Kb g n a b s t : ℝ) : ℂ) * V n k s := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun s _ => by ring)
      _ = ∑ b : Fin n, ∑ t : Fin n, ((X (b, t) : ℝ) : ℂ)
            * (((Lam g n k a b : ℝ) : ℂ) * V n k t) := by
          refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun t _ => ?_))
          rw [Kb_col g n hn2 k a b t]
      _ = ∑ b : Fin n, ((Lam g n k a b : ℝ) : ℂ) * ZZ n X k b := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          unfold ZZ
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t _ => by ring)
  -- abbreviations
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = 2 - ((2 * aHat g n k : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = ((2 * aHat g n k : ℝ) : ℂ) - ((2 * bH g n k : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ, γ = ((2 * bH g n k : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℂ, S = ∑ b : Fin n, ZZ n X k b := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin n → ℂ, σ = fun a : Fin n => ∑ b : Fin n,
      (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then ZZ n X k b else 0) := ⟨_, rfl⟩
  have heq' : ∀ a : Fin n, ((r : ℝ) : ℂ) * ZZ n X k a = α * ZZ n X k a + β * σ a + γ * S := by
    intro a
    rw [heq a]
    simp only [Lam_C]
    rw [ite_sum, hα, hβ, hγ, hS, hσ]
  have hσc : ∀ a b : Fin n, (a : ℕ) / (n / g) = (b : ℕ) / (n / g) → σ a = σ b := by
    intro a b h
    rw [hσ]
    simp only [h]
  have hgrp : ∀ a : Fin n, ((r : ℝ) : ℂ) * σ a
      = (α + β * ((n / g : ℕ) : ℂ)) * σ a + γ * ((n / g : ℕ) : ℂ) * S := by
    intro a
    have e : ∀ b : Fin n, ((r : ℝ) : ℂ) *
        (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then ZZ n X k b else 0)
        = α * (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then ZZ n X k b else 0)
          + (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then β * σ a else 0)
          + (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then γ * S else 0) := by
      intro b
      by_cases h : (a : ℕ) / (n / g) = (b : ℕ) / (n / g)
      · simp only [if_pos h]
        rw [heq' b, hσc a b h]
      · simp only [if_neg h]
        ring
    have hσa : σ a = ∑ b : Fin n,
        (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then ZZ n X k b else 0) := by
      rw [hσ]
    calc ((r : ℝ) : ℂ) * σ a
        = ∑ b : Fin n, (α * (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then ZZ n X k b else 0)
          + (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then β * σ a else 0)
          + (if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then γ * S else 0)) := by
          conv_lhs => rw [hσa]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun b _ => e b)
      _ = α * σ a + ((n / g : ℕ) : ℂ) * (β * σ a) + ((n / g : ℕ) : ℂ) * (γ * S) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hσa,
            grp_sum n (n / g) g hqpos hnq a, grp_sum n (n / g) g hqpos hnq a]
      _ = (α + β * ((n / g : ℕ) : ℂ)) * σ a + γ * ((n / g : ℕ) : ℂ) * S := by ring
  have hsumσ : ∑ a : Fin n, σ a = ((n / g : ℕ) : ℂ) * S := by
    rw [hS]
    simp only [hσ]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact grp_sum' n (n / g) g hqpos hnq b (ZZ n X k b)
  have htot : ((r : ℝ) : ℂ) * S
      = (α + β * ((n / g : ℕ) : ℂ) + γ * (n : ℂ)) * S := by
    have e0 : ((r : ℝ) : ℂ) * S = ∑ a : Fin n, ((r : ℝ) : ℂ) * ZZ n X k a := by
      rw [hS, Finset.mul_sum]
    have e1 : ((r : ℝ) : ℂ) * S = ∑ a : Fin n, (α * ZZ n X k a + β * σ a + γ * S) := by
      rw [e0]
      exact Finset.sum_congr rfl (fun a _ => heq' a)
    rw [e1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
      ← Finset.mul_sum, hsumσ, ← hS, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- case analysis
  by_cases hS0 : S = 0
  · by_cases hσ0 : ∃ a, σ a ≠ 0
    · obtain ⟨a1, ha1⟩ := hσ0
      have h1 := hgrp a1
      rw [hS0, mul_zero, add_zero] at h1
      have h2 : (((r : ℝ) : ℂ) - (α + β * ((n / g : ℕ) : ℂ))) * σ a1 = 0 := by
        rw [sub_mul, h1, sub_self]
      have h3 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ha1)
      right; left
      rw [hα, hβ] at h3
      exact_mod_cast h3
    · push_neg at hσ0
      have h1 := heq' a0
      rw [hS0, hσ0 a0, mul_zero, mul_zero, add_zero, add_zero] at h1
      have h2 : (((r : ℝ) : ℂ) - α) * ZZ n X k a0 = 0 := by
        rw [sub_mul, h1, sub_self]
      have h3 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hZ0)
      left
      rw [hα] at h3
      exact_mod_cast h3
  · have h2 : (((r : ℝ) : ℂ) - (α + β * ((n / g : ℕ) : ℂ) + γ * (n : ℂ))) * S = 0 := by
      rw [sub_mul, htot, sub_self]
    have h3 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hS0)
    right; right
    rw [hα, hβ, hγ] at h3
    exact_mod_cast h3

/-- eigenvectors of the form `u(a) · Re v_k(s)`. -/
lemma mem_of_u (g n : ℕ) (hn2 : 2 ≤ n) (k : ℕ) (u : Fin n → ℝ) (μ : ℝ) (hu : u ≠ 0)
    (h : ∀ a : Fin n, ∑ b : Fin n, Lam g n k a b * u b = μ * u a) :
    μ ∈ spectrum ℝ ((2 * (n : ℝ)) • Ymat g n) := by
  have hn : 0 < n := by omega
  rw [mem_spec]
  refine ⟨fun p => u p.1 * (V n k p.2).re, ?_, ?_⟩
  · intro h0
    apply hu
    funext a
    have := congrFun h0 (a, ⟨0, hn⟩)
    simp only [Fin.val_mk, V_zero, Complex.one_re, mul_one, Pi.zero_apply] at this
    exact this
  · funext p
    obtain ⟨a, s⟩ := p
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, M_apply g n hn]
    rw [Pi.smul_apply, smul_eq_mul]
    calc ∑ b : Fin n, ∑ t : Fin n, Kb g n a b s t * (u b * (V n k t).re)
        = ∑ b : Fin n, u b * ∑ t : Fin n, Kb g n a b s t * (V n k t).re := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t _ => by ring)
      _ = ∑ b : Fin n, u b * (Lam g n k a b * (V n k s).re) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Kb_row_re g n hn2 k a b s]
      _ = (∑ b : Fin n, Lam g n k a b * u b) * (V n k s).re := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun b _ => by ring)
      _ = μ * (u a * (V n k s).re) := by
          rw [h a]
          ring

lemma u1_eig (g n k : ℕ) (hq2 : 2 ≤ n / g) (a0 a1 : Fin n) (h0 : (a0 : ℕ) = 0)
    (h1 : (a1 : ℕ) = 1) (a : Fin n) :
    ∑ b : Fin n, Lam g n k a b * ((if b = a0 then (1 : ℝ) else 0) - (if b = a1 then 1 else 0))
      = (2 - 2 * aHat g n k) * ((if a = a0 then (1 : ℝ) else 0) - (if a = a1 then 1 else 0)) := by
  have hne : a0 ≠ a1 := by
    intro h
    rw [h] at h0
    omega
  have hq01 : (a1 : ℕ) / (n / g) = (a0 : ℕ) / (n / g) := by
    rw [h0, h1, Nat.zero_div, Nat.div_eq_of_lt (show 1 < n / g by omega)]
  have e : ∑ b : Fin n, Lam g n k a b * ((if b = a0 then (1 : ℝ) else 0) - (if b = a1 then 1 else 0))
      = Lam g n k a a0 - Lam g n k a a1 := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  rw [e]
  unfold Lam
  rw [hq01]
  by_cases ha0 : a = a0
  · have ha1 : a ≠ a1 := by rw [ha0]; exact hne
    have hg' : (a : ℕ) / (n / g) = (a0 : ℕ) / (n / g) := by rw [ha0]
    simp only [if_pos ha0, if_neg ha1, if_pos hg']
    ring
  · by_cases ha1 : a = a1
    · have hg' : (a : ℕ) / (n / g) = (a0 : ℕ) / (n / g) := by rw [ha1, hq01]
      simp only [if_neg ha0, if_pos ha1, if_pos hg']
      ring
    · simp only [if_neg ha0, if_neg ha1]
      by_cases hg' : (a : ℕ) / (n / g) = (a0 : ℕ) / (n / g)
      · simp only [if_pos hg']
        ring
      · simp only [if_neg hg']
        ring

/-- indicator of group `0` minus indicator of group `1`. -/
noncomputable def f2 (c : ℕ) : ℝ := (if c = 0 then (1 : ℝ) else 0) - (if c = 1 then 1 else 0)

lemma u2_eig (g n k : ℕ) (hg2 : 2 ≤ g) (hqpos : 0 < n / g) (hnq : n = g * (n / g)) (a : Fin n) :
    ∑ b : Fin n, Lam g n k a b * f2 ((b : ℕ) / (n / g))
      = ((2 - 2 * aHat g n k) + (2 * aHat g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ))
        * f2 ((a : ℕ) / (n / g)) := by
  have hS : ∑ b : Fin n, f2 ((b : ℕ) / (n / g)) = 0 := by
    simp only [f2, Finset.sum_sub_distrib]
    rw [grp_sum_c n (n / g) g hqpos hnq 0 (by omega), grp_sum_c n (n / g) g hqpos hnq 1 (by omega)]
    ring
  unfold Lam
  rw [ite_sum n (n / g) (2 : ℝ) (2 * aHat g n k) (2 * bH g n k)
    (fun b : Fin n => f2 ((b : ℕ) / (n / g))) a]
  simp only [sig_grp n (n / g) g hqpos hnq f2 a, hS] <;> ring

lemma u3_eig (g n k : ℕ) (hqpos : 0 < n / g) (hnq : n = g * (n / g)) (a : Fin n) :
    ∑ b : Fin n, Lam g n k a b * (fun _ : Fin n => (1 : ℝ)) b
      = ((2 - 2 * aHat g n k) + (2 * aHat g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ)
          + 2 * bH g n k * (n : ℝ)) * (fun _ : Fin n => (1 : ℝ)) a := by
  unfold Lam
  rw [ite_sum n (n / g) (2 : ℝ) (2 * aHat g n k) (2 * bH g n k) (fun _ : Fin n => (1 : ℝ)) a]
  simp only [grp_sum n (n / g) g hqpos hnq a, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] <;> ring

lemma alg1 (G Q a : ℝ) (hG : G ≠ 0) (hG1 : G - 1 ≠ 0) (hQ : Q ≠ 0) :
    (2 - 2 * a) + (2 * a - 2 * ((-G - (G * Q - G) * a) / (G * Q * (G - 1)))) * Q
      = 2 * (G / (G - 1)) + 2 * ((G * Q - G) / (G - 1)) * a := by
  field_simp <;> ring

lemma alg2 (G Q a : ℝ) (hG : G ≠ 0) (hG1 : G - 1 ≠ 0) (hQ : Q ≠ 0) :
    (2 - 2 * a) + (2 * a - 2 * ((-G - (G * Q - G) * a) / (G * Q * (G - 1)))) * Q
      + 2 * ((-G - (G * Q - G) * a) / (G * Q * (G - 1))) * (G * Q) = 0 := by
  field_simp <;> ring

end Aux_R6

end TSPSDPGap

open TSPSDPGap TSPSDPGap.Aux_R6 in
set_option maxHeartbeats 1600000 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    spectrum ℝ ((2 * (n : ℝ)) • Ymat g n) =
      ({0, 2 * (n : ℝ)} : Set ℝ) ∪
      {x | ∃ k : ℕ, 1 ≤ k ∧ k < n ∧
        x = 2 * ((g : ℝ) / ((g : ℝ) - 1)) + 2 * (((n : ℝ) - g) / ((g : ℝ) - 1)) * aHat g n k} ∪
      {x | ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ x = 2 - 2 * aHat g n k} := by
  have hn2 : 2 ≤ n := by omega
  have hn : 0 < n := by omega
  obtain ⟨ha0, hb0, hrel⟩ := coeff_facts g n hg hg2 hgn hlt
  obtain ⟨q0, hq0⟩ := hgn
  have hq0' : n / g = q0 := by rw [hq0, Nat.mul_div_cancel_left q0 (by omega)]
  have hq2 : 2 ≤ q0 := by
    rcases Nat.lt_or_ge q0 2 with h | h
    · interval_cases q0 <;> omega
    · exact h
  have hqpos : 0 < n / g := by omega
  have hq2' : 2 ≤ n / g := by omega
  have hnq : n = g * (n / g) := by rw [hq0']; exact hq0
  have hnR : (n : ℝ) = (g : ℝ) * ((n / g : ℕ) : ℝ) := by
    rw [hq0']
    exact_mod_cast hq0
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hg0 : (g : ℝ) ≠ 0 := by positivity
  have hg1 : (g : ℝ) - 1 ≠ 0 := (show (0 : ℝ) < (g : ℝ) - 1 by linarith).ne'
  have hQ0 : ((n / g : ℕ) : ℝ) ≠ 0 := by
    rw [hq0']
    exact_mod_cast (show q0 ≠ 0 by omega)
  obtain ⟨a0, h0⟩ : ∃ a : Fin n, (a : ℕ) = 0 := ⟨⟨0, hn⟩, rfl⟩
  obtain ⟨a1, h1⟩ : ∃ a : Fin n, (a : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hne : a0 ≠ a1 := by
    intro h
    rw [h] at h0
    omega
  have hu1 : (fun a : Fin n => (if a = a0 then (1 : ℝ) else 0) - (if a = a1 then 1 else 0)) ≠ 0 := by
    intro h
    have := congrFun h a0
    simp [hne] at this
  have hu2 : (fun a : Fin n => f2 ((a : ℕ) / (n / g))) ≠ 0 := by
    intro h
    have := congrFun h a0
    simp [f2, h0] at this
  have hu3 : (fun _ : Fin n => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congrFun h a0
    simp at this
  ext r
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro hr
    obtain ⟨k, hk⟩ := spec_sub g n hg2 ⟨q0, hq0⟩ hlt r hr
    by_cases hk0 : (k : ℕ) = 0
    · rw [hk0, ha0, hb0] at hk
      rcases hk with h | h | h
      · left; left; left
        rw [h]; ring
      · left; left; left
        rw [h]; ring
      · left; left; right
        rw [h]; ring
    · have hk1 : 1 ≤ (k : ℕ) := by omega
      have hkn : (k : ℕ) < n := k.isLt
      rcases hk with h | h | h
      · right
        exact ⟨k, hk1, hkn, h⟩
      · left; right
        refine ⟨k, hk1, hkn, ?_⟩
        rw [h, hrel k hk1 hkn, hnR]
        exact alg1 _ _ _ hg0 hg1 hQ0
      · left; left; left
        rw [h, hrel k hk1 hkn, hnR]
        exact alg2 _ _ _ hg0 hg1 hQ0
  · rintro (((h | h) | ⟨k, hk1, hkn, h⟩) | ⟨k, hk1, hkn, h⟩)
    · have hm := mem_of_u g n hn2 0 _ _ hu1 (u1_eig g n 0 hq2' a0 a1 h0 h1)
      have e : (2 : ℝ) - 2 * aHat g n 0 = 0 := by rw [ha0]; norm_num
      rw [e] at hm
      rw [h]
      exact hm
    · have hm := mem_of_u g n hn2 0 _ _ hu3 (u3_eig g n 0 hqpos hnq)
      have e : ((2 : ℝ) - 2 * aHat g n 0) + (2 * aHat g n 0 - 2 * bH g n 0) * ((n / g : ℕ) : ℝ)
          + 2 * bH g n 0 * (n : ℝ) = 2 * (n : ℝ) := by
        rw [ha0, hb0]; ring
      rw [e] at hm
      rw [h]
      exact hm
    · have hm := mem_of_u g n hn2 k _ _ hu2 (u2_eig g n k hg2 hqpos hnq)
      have e : ((2 : ℝ) - 2 * aHat g n k) + (2 * aHat g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ)
          = 2 * ((g : ℝ) / ((g : ℝ) - 1)) + 2 * (((n : ℝ) - g) / ((g : ℝ) - 1)) * aHat g n k := by
        rw [hrel k hk1 hkn, hnR]
        exact alg1 _ _ _ hg0 hg1 hQ0
      rw [e] at hm
      rw [h]
      exact hm
    · have hm := mem_of_u g n hn2 k _ _ hu1 (u1_eig g n k hq2' a0 a1 h0 h1)
      rw [h]
      exact hm
