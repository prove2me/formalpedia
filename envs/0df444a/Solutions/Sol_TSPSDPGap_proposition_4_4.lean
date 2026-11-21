-- Prove2me | solution 1 for TSPSDPGap.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:00:07.746967+00:00
-- url     : https://prove2.me/submissions/7e2b8e4f-beba-4a0c-a8bf-dd433423c916

import Mathlib
import Definitions.Def_TSPSDPGap_IsSDP1Feasible
import Definitions.Def_TSPSDPGap_Ymat

open scoped Kronecker

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

/-- `âₖ` (same formula as `aHat`). -/
noncomputable def aH (g n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2), coeffA g n i * Real.cos (2 * Real.pi * i * k / n)

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
    aH g n 0 = 1 ∧ bH g n 0 = 1 ∧
    ∀ k : ℕ, 1 ≤ k → k < n →
      bH g n k = (-(g:ℝ) - ((n:ℝ) - g) * aH g n k) / ((n:ℝ) * ((g:ℝ) - 1)) := by
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
  · unfold aH
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
    have haH : aH g n k = T + coeffA g n m * Real.cos (2 * Real.pi * m * k / n) := by
      unfold aH
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
  else if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then 2 * aH g n k else 2 * bH g n k

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
      unfold Amat aH
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
      if (a : ℕ) / (n / g) = (b : ℕ) / (n / g) then ((2 * aH g n k : ℝ) : ℂ)
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
    ∃ k : Fin n, r = 2 - 2 * aH g n k ∨
      r = (2 - 2 * aH g n k) + (2 * aH g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ) ∨
      r = (2 - 2 * aH g n k) + (2 * aH g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ)
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
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = 2 - ((2 * aH g n k : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = ((2 * aH g n k : ℝ) : ℂ) - ((2 * bH g n k : ℝ) : ℂ) :=
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
      = (2 - 2 * aH g n k) * ((if a = a0 then (1 : ℝ) else 0) - (if a = a1 then 1 else 0)) := by
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
      = ((2 - 2 * aH g n k) + (2 * aH g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ))
        * f2 ((a : ℕ) / (n / g)) := by
  have hS : ∑ b : Fin n, f2 ((b : ℕ) / (n / g)) = 0 := by
    simp only [f2, Finset.sum_sub_distrib]
    rw [grp_sum_c n (n / g) g hqpos hnq 0 (by omega), grp_sum_c n (n / g) g hqpos hnq 1 (by omega)]
    ring
  unfold Lam
  rw [ite_sum n (n / g) (2 : ℝ) (2 * aH g n k) (2 * bH g n k)
    (fun b : Fin n => f2 ((b : ℕ) / (n / g))) a]
  simp only [sig_grp n (n / g) g hqpos hnq f2 a, hS] <;> ring

lemma u3_eig (g n k : ℕ) (hqpos : 0 < n / g) (hnq : n = g * (n / g)) (a : Fin n) :
    ∑ b : Fin n, Lam g n k a b * (fun _ : Fin n => (1 : ℝ)) b
      = ((2 - 2 * aH g n k) + (2 * aH g n k - 2 * bH g n k) * ((n / g : ℕ) : ℝ)
          + 2 * bH g n k * (n : ℝ)) * (fun _ : Fin n => (1 : ℝ)) a := by
  unfold Lam
  rw [ite_sum n (n / g) (2 : ℝ) (2 * aH g n k) (2 * bH g n k) (fun _ : Fin n => (1 : ℝ)) a]
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


namespace TSPSDPGap

namespace Aux_C412

open Finset

lemma reflect_sum (g : ℕ) (θ : ℝ) :
    ∑ j ∈ range g, Real.cos (((g:ℝ) - j) * θ) = ∑ d ∈ Finset.Ico 1 (g + 1), Real.cos ((d:ℝ) * θ) := by
  rw [Finset.sum_Ico_eq_sum_range, show g + 1 - 1 = g by omega]
  rw [← Finset.sum_range_reflect (fun k => Real.cos (((1 + k : ℕ) : ℝ) * θ)) g]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  have e : ((1 + (g - 1 - j) : ℕ) : ℝ) = (g:ℝ) - j := by
    rw [show 1 + (g - 1 - j) = g - j by omega, Nat.cast_sub hj'.le]
  rw [e]

lemma fejer (g : ℕ) (θ : ℝ) :
    (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
      = (∑ j ∈ range g, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range g, Real.sin (j * θ)) ^ 2 := by
  induction g with
  | zero => simp
  | succ g ih =>
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · subst h0
      simp
    have h1 : 1 ≤ g := hpos
    have hsplit : ∑ j ∈ Finset.Ico 1 (g + 1), (((g + 1 : ℕ) : ℝ) - j) * Real.cos (j * θ)
        = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
          + ∑ j ∈ Finset.Ico 1 (g + 1), Real.cos (j * θ) := by
      rw [Finset.sum_Ico_succ_top h1, Finset.sum_Ico_succ_top h1]
      have e : ∑ j ∈ Finset.Ico 1 g, (((g + 1 : ℕ) : ℝ) - j) * Real.cos (j * θ)
          = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
            + ∑ j ∈ Finset.Ico 1 g, Real.cos (j * θ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        push_cast
        ring
      rw [e]
      push_cast
      ring
    have hcross : ∑ j ∈ range g, Real.cos (((g:ℝ) - j) * θ)
        = (∑ j ∈ range g, Real.cos (j * θ)) * Real.cos (g * θ)
          + (∑ j ∈ range g, Real.sin (j * θ)) * Real.sin (g * θ) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show ((g:ℝ) - j) * θ = g * θ - j * θ by ring, Real.cos_sub]
      ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsplit, ← reflect_sum, hcross]
    push_cast
    linear_combination ih - Real.sin_sq_add_cos_sq ((g:ℝ) * θ)

lemma fejer_le (g : ℕ) (θ : ℝ) :
    (∑ j ∈ range g, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range g, Real.sin (j * θ)) ^ 2
      ≤ (g:ℝ) ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := range g) (f := fun j : ℕ => Real.cos (j * θ))
  have h2 := sq_sum_le_card_mul_sum_sq (s := range g) (f := fun j : ℕ => Real.sin (j * θ))
  have h3 : ∑ j ∈ range g, Real.cos (j * θ) ^ 2 + ∑ j ∈ range g, Real.sin (j * θ) ^ 2 = g := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j ∈ range g, Real.cos (j * θ) ^ 2 + Real.sin (j * θ) ^ 2 = 1 := fun j _ => by
      rw [add_comm]; exact Real.sin_sq_add_cos_sq _
    rw [Finset.sum_congr rfl this]
    simp
  simp only [Finset.card_range] at h1 h2
  have h4 : (g:ℝ) * (∑ j ∈ range g, Real.cos (j * θ) ^ 2 + ∑ j ∈ range g, Real.sin (j * θ) ^ 2)
      = (g:ℝ) * g := by rw [h3]
  nlinarith [h1, h2, h4]

/-- Bounds `0 ≤ g + 2P ≤ g²` for the Fejér-type sum appearing in `coeffA`. -/
lemma key (g n i : ℕ) :
    0 ≤ (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
    ∧ (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
      ≤ (g : ℝ) ^ 2 := by
  have e : ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
      = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * (Real.pi * i / (n / 2 : ℕ))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show Real.pi * (i:ℝ) * (j:ℝ) / ((n / 2 : ℕ) : ℝ)
      = (j:ℝ) * (Real.pi * i / ((n / 2 : ℕ) : ℝ)) by ring]
  rw [e, fejer]
  exact ⟨by positivity, fejer_le g _⟩

lemma circ_nonneg (m i : ℕ) (s t : Fin m) : 0 ≤ circBasis m i s t := by
  unfold circBasis
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num

end Aux_C412

end TSPSDPGap

open TSPSDPGap TSPSDPGap.Aux_C412 in
theorem TSPSDPGap.c412_sol (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    (∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffA g n i) ∧
    (∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffB g n i) ∧
    ∀ a b, 0 ≤ Ymat g n a b := by
  have hg0 : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hg1 : (0:ℝ) < (g:ℝ) - 1 := by
    have : (2:ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hng : (0:ℝ) < (n:ℝ) - g := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hn0 : (0:ℝ) < n := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hgg : (g:ℝ) / g = 1 := div_self hg0.ne'
  have hA : ∀ i, 0 ≤ coeffA g n i := by
    intro i
    obtain ⟨k0, k1⟩ := key g n i
    unfold coeffA
    split_ifs
    · have e : (2:ℝ) + 4 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
          = 2 / g * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))) := by
        have e2 : 2 / (g:ℝ) * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)))
            = 2 * ((g:ℝ) / g) + 4 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := by ring
        rw [e2, hgg, mul_one]
      rw [e]
      exact mul_nonneg (one_div_nonneg.2 hng.le) (mul_nonneg (by positivity) k0)
    · have e : (1:ℝ) + 2 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
          = 1 / g * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))) := by
        have e2 : 1 / (g:ℝ) * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)))
            = (g:ℝ) / g + 2 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := by ring
        rw [e2, hgg]
      rw [e]
      exact mul_nonneg (one_div_nonneg.2 hng.le) (mul_nonneg (by positivity) k0)
  have hB : ∀ i, 0 ≤ coeffB g n i := by
    intro i
    obtain ⟨k0, k1⟩ := key g n i
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
        * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := ⟨_, rfl⟩
    rw [← hP] at k0 k1
    have hden : 0 < (n:ℝ) * ((g:ℝ) - 1) := mul_pos hn0 hg1
    have hcancel : ∀ X : ℝ, ((n:ℝ) - g) * (1 / ((n:ℝ) - g) * X) = X := by
      intro X
      rw [← mul_assoc, mul_one_div_cancel hng.ne', one_mul]
    unfold coeffB coeffA
    split_ifs with h
    · rw [← hP, hcancel]
      refine div_nonneg ?_ hden.le
      have e : (2:ℝ) + 4 / g * P = 2 / g * ((g : ℝ) + 2 * P) := by
        have e2 : 2 / (g:ℝ) * ((g : ℝ) + 2 * P) = 2 * ((g:ℝ) / g) + 4 / g * P := by ring
        rw [e2, hgg, mul_one]
      rw [e]
      have : 2 / (g:ℝ) * ((g : ℝ) + 2 * P) ≤ 2 / g * (g:ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left k1 (by positivity)
      have e3 : 2 / (g:ℝ) * (g:ℝ) ^ 2 = 2 * g * ((g:ℝ) / g) := by ring
      rw [e3, hgg, mul_one] at this
      linarith
    · rw [← hP, hcancel]
      refine div_nonneg ?_ hden.le
      have e : (1:ℝ) + 2 / g * P = 1 / g * ((g : ℝ) + 2 * P) := by
        have e2 : 1 / (g:ℝ) * ((g : ℝ) + 2 * P) = (g:ℝ) / g + 2 / g * P := by ring
        rw [e2, hgg]
      rw [e]
      have : 1 / (g:ℝ) * ((g : ℝ) + 2 * P) ≤ 1 / g * (g:ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left k1 (by positivity)
      have e3 : 1 / (g:ℝ) * (g:ℝ) ^ 2 = g * ((g:ℝ) / g) := by ring
      rw [e3, hgg, mul_one] at this
      linarith
  refine ⟨fun i _ => hA i, fun i _ => hB i, ?_⟩
  intro a b
  have hAm : ∀ s t, 0 ≤ Amat g n s t := by
    intro s t
    unfold Amat
    rw [Matrix.sum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (hA i) (circ_nonneg n i s t))
  have hBm : ∀ s t, 0 ≤ Bmat g n s t := by
    intro s t
    unfold Bmat
    rw [Matrix.sum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (hB i) (circ_nonneg n i s t))
  unfold Ymat
  simp only [Matrix.of_apply]
  apply mul_nonneg (by positivity)
  split_ifs
  · norm_num
  · norm_num
  · exact hAm _ _
  · exact hBm _ _


namespace TSPSDPGap

namespace Aux_C47

open Finset

lemma mod2 (a n : ℕ) (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma circ_row (n i : ℕ) (hi1 : 1 ≤ i) (hin : i < n) (s : Fin n) :
    ∑ t, circBasis n i s t = 2 := by
  have hn : 0 < n := by omega
  unfold circBasis
  simp only [Matrix.of_apply]
  rw [Finset.sum_add_distrib, Nat.mod_eq_of_lt hin]
  have h1 : ∀ t : Fin n, (((t : ℕ) + n - s) % n = i ↔ t = ⟨((s : ℕ) + i) % n, Nat.mod_lt _ hn⟩) := by
    intro t
    have := s.isLt
    have := t.isLt
    rw [Fin.ext_iff]
    simp only
    rw [mod2 _ _ (by omega), mod2 ((s : ℕ) + i) n (by omega)]
    split_ifs <;> omega
  have h2 : ∀ t : Fin n, (((s : ℕ) + n - t) % n = i ↔ t = ⟨((s : ℕ) + n - i) % n, Nat.mod_lt _ hn⟩) := by
    intro t
    have := s.isLt
    have := t.isLt
    rw [Fin.ext_iff]
    simp only
    rw [mod2 _ _ (by omega), mod2 ((s : ℕ) + n - i) n (by omega)]
    split_ifs <;> omega
  simp only [h1, h2]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  norm_num

lemma circ_comb_total (n : ℕ) (c : ℕ → ℝ) :
    ∑ s : Fin n, ∑ t : Fin n, (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t
      = 2 * (n : ℝ) * ∑ i ∈ Finset.Icc 1 (n / 2), c i := by
  have hA : ∀ s t : Fin n, (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t
      = ∑ i ∈ Finset.Icc 1 (n / 2), c i * circBasis n i s t := by
    intro s t
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
  calc ∑ s : Fin n, ∑ t : Fin n, (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t
      = ∑ s : Fin n, ∑ t : Fin n, ∑ i ∈ Finset.Icc 1 (n / 2), c i * circBasis n i s t := by
        simp only [hA]
    _ = ∑ s : Fin n, ∑ i ∈ Finset.Icc 1 (n / 2), ∑ t : Fin n, c i * circBasis n i s t :=
        Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
    _ = ∑ i ∈ Finset.Icc 1 (n / 2), ∑ s : Fin n, ∑ t : Fin n, c i * circBasis n i s t :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.Icc 1 (n / 2), c i * (2 * n) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_Icc.mp hi
        have hin : i < n := by omega
        have : ∑ s : Fin n, ∑ t : Fin n, c i * circBasis n i s t
            = ∑ s : Fin n, c i * ∑ t : Fin n, circBasis n i s t :=
          Finset.sum_congr rfl (fun s _ => (Finset.mul_sum _ _ _).symm)
        rw [this]
        simp only [circ_row n i hi'.1 hin]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = 2 * (n : ℝ) * ∑ i ∈ Finset.Icc 1 (n / 2), c i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring

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

end Aux_C47

end TSPSDPGap

open TSPSDPGap TSPSDPGap.Aux_C47 in
theorem TSPSDPGap.c47_sol (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    Matrix.trace (Matrix.of (fun _ _ => (1 : ℝ)) * Ymat g n) = (n : ℝ) ^ 2 := by
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
  have hg0 : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hng : (0:ℝ) < (n:ℝ) - g := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hg1 : (0:ℝ) < (g:ℝ) - 1 := by
    have : (2:ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hn0 : (0:ℝ) < n := by linarith
  have hn0' : (n:ℝ) ≠ 0 := hn0.ne'
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  -- the coefficient sums
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
  -- total entry sums of the two blocks
  have hAtot : ∑ s : Fin n, ∑ t : Fin n, Amat g n s t = 2 * n := by
    unfold Amat
    rw [circ_comb_total, hsumA, mul_one]
  have hBtot : ∑ s : Fin n, ∑ t : Fin n, Bmat g n s t = 2 * n := by
    unfold Bmat
    rw [circ_comb_total, hsumB, mul_one]
  -- each block of `Y` sums to one
  have hinner : ∀ x1 y1 : Fin n, ∑ x2 : Fin n, ∑ y2 : Fin n, Ymat g n (x1, x2) (y1, y2) = 1 := by
    intro x1 y1
    unfold Ymat
    simp only [Matrix.of_apply]
    by_cases h1 : x1 = y1
    · simp only [h1, eq_self_iff_true, if_true, ↓reduceIte]
      have e : ∀ x2 : Fin n, ∑ y2 : Fin n, 1 / (2 * (n:ℝ)) * (if x2 = y2 then (2:ℝ) else 0)
          = 1 / (2 * (n:ℝ)) * 2 := by
        intro x2
        rw [← Finset.mul_sum, Finset.sum_ite_eq]
        simp
      rw [Finset.sum_congr rfl (fun x2 _ => e x2), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (x1 : ℕ) / (n / g) = (y1 : ℕ) / (n / g)
      · simp only [h2, ↓reduceIte]
        have e : ∑ x2 : Fin n, ∑ y2 : Fin n, 1 / (2 * (n:ℝ)) * Amat g n x2 y2
            = 1 / (2 * (n:ℝ)) * ∑ x2 : Fin n, ∑ y2 : Fin n, Amat g n x2 y2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x2 _ => (Finset.mul_sum _ _ _).symm)
        rw [e, hAtot]
        field_simp
      · simp only [h2, ↓reduceIte]
        have e : ∑ x2 : Fin n, ∑ y2 : Fin n, 1 / (2 * (n:ℝ)) * Bmat g n x2 y2
            = 1 / (2 * (n:ℝ)) * ∑ x2 : Fin n, ∑ y2 : Fin n, Bmat g n x2 y2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x2 _ => (Finset.mul_sum _ _ _).symm)
        rw [e, hBtot]
        field_simp
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, one_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun b1 _ => Finset.sum_comm)]
  simp only [hinner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

namespace TSPSDPGap

namespace Aux_R6

open Finset

lemma eps_split (m : ℕ) (hm : 1 ≤ m) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1) * f i
      = 2 * ∑ i ∈ Finset.Ico 1 m, f i + f m := by
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_succ_top hm, if_neg (lt_irrefl m), one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [if_pos (Finset.mem_Ico.mp hi).2]

lemma Cf_ge (m : ℕ) (hm : 1 ≤ m) (d : ℤ) :
    -1 ≤ ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
      * Real.cos (Real.pi * i * ((d : ℤ) : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm2 : (0 : ℤ) < 2 * (m : ℤ) := by omega
  have hr0 : 0 ≤ d % (2 * (m : ℤ)) := Int.emod_nonneg d hm2.ne'
  have hr1 : d % (2 * (m : ℤ)) < 2 * (m : ℤ) := Int.emod_lt_of_pos d hm2
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = d % (2 * (m : ℤ)) := ⟨(d % (2 * (m : ℤ))).toNat,
    Int.toNat_of_nonneg hr0⟩
  obtain ⟨qq, hqq⟩ : ∃ qq : ℤ, qq = d / (2 * (m : ℤ)) := ⟨_, rfl⟩
  have hdz : d = (r : ℤ) + qq * (2 * (m : ℤ)) := by
    rw [hr, hqq]
    exact (Int.emod_add_ediv_mul d (2 * (m : ℤ))).symm
  have hrlt : r < 2 * m := by
    have h := hr1
    rw [← hr] at h
    exact_mod_cast h
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  have hterm : ∀ i : ℕ, Real.cos (Real.pi * i * ((d : ℤ) : ℝ) / m)
      = Real.cos (Real.pi * i * (r : ℝ) / m) := by
    intro i
    have e : Real.pi * (i : ℝ) * ((d : ℤ) : ℝ) / m
        = Real.pi * i * (r : ℝ) / m + (((i : ℤ) * qq : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hdz]
      push_cast
      field_simp <;> ring
    rw [e, Real.cos_add_int_mul_two_pi]
  simp only [hterm]
  by_cases hr0' : r = 0
  · refine le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Finset.sum_nonneg (fun i _ => ?_))
    rw [hr0']
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one]
    split_ifs <;> norm_num
  · have h2 : ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
          * Real.cos (Real.pi * i * (r : ℝ) / m)
        = 2 * ∑ i ∈ Finset.Ico 1 m, Real.cos (Real.pi * i * (r : ℝ) / m)
          + Real.cos (Real.pi * m * (r : ℝ) / m) :=
      eps_split m hm (fun i => Real.cos (Real.pi * i * (r : ℝ) / m))
    rw [h2]
    have := cos_sum m r hm (by omega) hrlt
    linarith

lemma ahat_lower (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) (k : ℕ) :
    -(g : ℝ) ≤ ((n : ℝ) - g) * aH g n k := by
  obtain ⟨q, hq⟩ := hgn
  have hneven : Even n := by rw [hq]; exact hg.mul_right q
  obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
  have hm2 : 2 * m = n := by rw [hm]; exact Nat.two_mul_div_two_of_even hneven
  have hm1 : 1 ≤ m := by omega
  have hm2R : 2 * (m : ℝ) = n := by exact_mod_cast hm2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hng : (0 : ℝ) < (n : ℝ) - g := by
    have : (g : ℝ) < n := by exact_mod_cast hlt
    linarith
  have hcc : ∀ i : ℕ, Real.cos (2 * Real.pi * i * k / n) = Real.cos (Real.pi * i * k / m) := by
    intro i
    congr 1
    rw [← hm2R, div_eq_div_iff (mul_ne_zero two_ne_zero hmR.ne') hmR.ne']
    ring
  have hcoef : ∀ i ∈ Finset.Icc 1 m, ((n : ℝ) - g) * coeffA g n i
      = (if i < m then (2 : ℝ) else 1) * (1 + 2 / (g : ℝ) *
        ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / m)) := by
    intro i _
    unfold coeffA
    rw [← hm]
    split_ifs
    · rw [← mul_assoc, mul_one_div_cancel hng.ne', one_mul] <;> ring
    · rw [← mul_assoc, mul_one_div_cancel hng.ne', one_mul] <;> ring
  have hW : ∀ j : ℕ, -1 ≤ ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
      * (Real.cos (Real.pi * i * j / m) * Real.cos (Real.pi * i * k / m)) := by
    intro j
    have h1 := Cf_ge m hm1 ((j : ℤ) + (k : ℤ))
    have h2 := Cf_ge m hm1 ((j : ℤ) - (k : ℤ))
    have e : ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
        * (Real.cos (Real.pi * i * j / m) * Real.cos (Real.pi * i * k / m))
        = (∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
            * Real.cos (Real.pi * i * ((((j : ℤ) + (k : ℤ)) : ℤ) : ℝ) / m)
          + ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
            * Real.cos (Real.pi * i * ((((j : ℤ) - (k : ℤ)) : ℤ) : ℝ) / m)) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have ha : Real.pi * (i : ℝ) * ((((j : ℤ) + (k : ℤ)) : ℤ) : ℝ) / m
          = Real.pi * i * j / m + Real.pi * i * k / m := by
        push_cast
        ring
      have hb : Real.pi * (i : ℝ) * ((((j : ℤ) - (k : ℤ)) : ℤ) : ℝ) / m
          = Real.pi * i * j / m - Real.pi * i * k / m := by
        push_cast
        ring
      rw [ha, hb, Real.cos_add, Real.cos_sub]
      ring
    rw [e]
    linarith
  have hexp : ((n : ℝ) - g) * aH g n k
      = ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1) * Real.cos (Real.pi * i * k / m)
        + 2 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) *
          ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
            * (Real.cos (Real.pi * i * j / m) * Real.cos (Real.pi * i * k / m)) := by
    have step : ∀ i ∈ Finset.Icc 1 m, ((n : ℝ) - g) * (coeffA g n i * Real.cos (2 * Real.pi * i * k / n))
        = (if i < m then (2 : ℝ) else 1) * Real.cos (Real.pi * i * k / m)
          + 2 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) *
            ((if i < m then (2 : ℝ) else 1)
              * (Real.cos (Real.pi * i * j / m) * Real.cos (Real.pi * i * k / m))) := by
      intro i hi
      rw [← mul_assoc, hcoef i hi, hcc i]
      have e2 : ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) *
            ((if i < m then (2 : ℝ) else 1)
              * (Real.cos (Real.pi * i * j / m) * Real.cos (Real.pi * i * k / m)))
          = (if i < m then (2 : ℝ) else 1) * (∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
              * Real.cos (Real.pi * i * j / m)) * Real.cos (Real.pi * i * k / m) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => by ring)
      rw [e2]
      ring
    have L : ((n : ℝ) - g) * aH g n k = ∑ i ∈ Finset.Icc 1 m,
        ((n : ℝ) - g) * (coeffA g n i * Real.cos (2 * Real.pi * i * k / n)) := by
      unfold aH
      rw [← hm, Finset.mul_sum]
    rw [L, Finset.sum_congr rfl step, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  rw [hexp]
  have hfirst := Cf_ge m hm1 (k : ℤ)
  have hfirst' : -1 ≤ ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
      * Real.cos (Real.pi * i * k / m) := by
    simp only [Int.cast_natCast] at hfirst
    exact hfirst
  have hsecond : -∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) ≤ ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) *
      ∑ i ∈ Finset.Icc 1 m, (if i < m then (2 : ℝ) else 1)
        * (Real.cos (Real.pi * i * j / m) * Real.cos (Real.pi * i * k / m)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hj := Finset.mem_Ico.mp hj
    have hgj : (0 : ℝ) ≤ (g : ℝ) - j := by
      have : (j : ℝ) < g := by exact_mod_cast hj.2
      linarith
    have := mul_le_mul_of_nonneg_left (hW j) hgj
    linarith
  have hG := gauss g
  have h2g : (0 : ℝ) ≤ 2 / (g : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hsecond h2g
  have h4 : 2 / (g : ℝ) * -∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) = -((g : ℝ) - 1) := by
    rw [mul_neg, show 2 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
      = (2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)) / g by ring, hG,
      mul_div_cancel_left₀ _ hg0.ne']
  linarith

lemma ahat_upper (g n : ℕ) (hc : ∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffA g n i)
    (ha0 : aH g n 0 = 1) (k : ℕ) : aH g n k ≤ 1 := by
  rw [← ha0]
  unfold aH
  refine Finset.sum_le_sum (fun i hi => ?_)
  apply mul_le_mul_of_nonneg_left _ (hc i hi)
  simp only [Nat.cast_zero, mul_zero, zero_div, Real.cos_zero]
  exact Real.cos_le_one _

lemma Kb_swap (g n : ℕ) (a b s t : Fin n) : Kb g n b a t s = Kb g n a b s t := by
  unfold Kb
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl]
    by_cases hst : s = t
    · subst hst
      rfl
    · rw [if_neg hst, if_neg (Ne.symm hst)]
  · rw [if_neg (Ne.symm hab), if_neg hab]
    by_cases hg : (a : ℕ) / (n / g) = (b : ℕ) / (n / g)
    · rw [if_pos hg.symm, if_pos hg]
      unfold Amat
      exact comb_symm n (coeffA g n) t s
    · rw [if_neg (Ne.symm hg), if_neg hg]
      unfold Bmat
      exact comb_symm n (coeffB g n) t s

lemma Y_psd (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n)
    (hc : ∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffA g n i) :
    (Ymat g n).PosSemidef := by
  have hn2 : 2 ≤ n := by omega
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : (2 * (n : ℝ)) ≠ 0 := by positivity
  obtain ⟨ha0, hb0, hrel⟩ := coeff_facts g n hg hg2 hgn hlt
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hngR : (0 : ℝ) < (n : ℝ) - g := by
    have : (g : ℝ) < n := by exact_mod_cast hlt
    linarith
  obtain ⟨q0, hq0⟩ := hgn
  have hq0' : n / g = q0 := by rw [hq0, Nat.mul_div_cancel_left q0 (by omega)]
  have hnRq : (n : ℝ) = (g : ℝ) * ((n / g : ℕ) : ℝ) := by
    rw [hq0']
    exact_mod_cast hq0
  have hg0 : (g : ℝ) ≠ 0 := by positivity
  have hQ0 : ((n / g : ℕ) : ℝ) ≠ 0 := by
    rw [hq0']
    have : q0 ≠ 0 := by
      rintro rfl
      omega
    exact_mod_cast this
  have hM : ((2 * (n : ℝ)) • Ymat g n).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨?_, ?_⟩
    · apply Matrix.IsHermitian.ext
      rintro ⟨a, s⟩ ⟨b, t⟩
      rw [star_trivial, M_apply g n hn, M_apply g n hn, Kb_swap]
    · intro r hr
      obtain ⟨k, hk⟩ := spec_sub g n hg2 ⟨q0, hq0⟩ hlt r hr
      show 0 ≤ r
      have hup := ahat_upper g n hc ha0 k
      by_cases hk0 : (k : ℕ) = 0
      · rw [hk0, ha0, hb0] at hk
        rcases hk with h | h | h
        · rw [h]; norm_num
        · rw [h]; norm_num
        · rw [h]; linarith
      · have hk1 : 1 ≤ (k : ℕ) := by omega
        have hkn : (k : ℕ) < n := k.isLt
        have hlow := ahat_lower g n hg hg2 ⟨q0, hq0⟩ hlt k
        rcases hk with h | h | h
        · rw [h]; linarith
        · rw [h, hrel k hk1 hkn, hnRq, alg1 _ _ _ hg0 hg1.ne' hQ0]
          rw [hnRq] at hlow
          have e : 2 * ((g : ℝ) / ((g : ℝ) - 1))
              + 2 * (((g : ℝ) * ((n / g : ℕ) : ℝ) - g) / ((g : ℝ) - 1)) * aH g n k
              = 2 * ((g : ℝ) + ((g : ℝ) * ((n / g : ℕ) : ℝ) - g) * aH g n k) / ((g : ℝ) - 1) := by
            ring
          rw [e]
          apply div_nonneg _ hg1.le
          linarith
        · rw [h, hrel k hk1 hkn, hnRq]
          linarith [alg2 (g : ℝ) ((n / g : ℕ) : ℝ) (aH g n k) hg0 hg1.ne' hQ0]
  have hY : Ymat g n = (1 / (2 * (n : ℝ))) • ((2 * (n : ℝ)) • Ymat g n) := by
    rw [smul_smul, one_div_mul_cancel h2n, one_smul]
  rw [hY]
  exact hM.smul (by positivity)

end Aux_R6

end TSPSDPGap

namespace TSPSDPGap

namespace Aux_R6

open Finset

lemma tr_kron1 (n : ℕ) (E : Matrix (Fin n) (Fin n) ℝ)
    (Y : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) :
    Matrix.trace (((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ E) * Y)
      = ∑ a : Fin n, ∑ s : Fin n, ∑ t : Fin n, E s t * Y (a, t) (a, s) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun s _ => ?_))
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [if_pos rfl]
    ring
  · intro b _ hba
    apply Finset.sum_eq_zero
    intro t _
    rw [if_neg (Ne.symm hba)]
    ring
  · intro h
    exact absurd (Finset.mem_univ a) h

lemma tr_kron2 (n : ℕ) (E : Matrix (Fin n) (Fin n) ℝ)
    (Y : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) :
    Matrix.trace ((E ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) * Y)
      = ∑ a : Fin n, ∑ s : Fin n, ∑ b : Fin n, E a b * Y (b, s) (a, s) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun s _ =>
    Finset.sum_congr rfl (fun b _ => ?_)))
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl]
    ring
  · intro t _ hts
    rw [if_neg (Ne.symm hts)]
    ring
  · intro h
    exact absurd (Finset.mem_univ s) h

end Aux_R6

end TSPSDPGap

open TSPSDPGap TSPSDPGap.Aux_R6 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    IsSDP1Feasible n (Ymat g n) := by
  have hn : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have h2n : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hYd : ∀ a s : Fin n, Ymat g n (a, s) (a, s) = 1 / n := by
    intro a s
    unfold Ymat
    simp only [Matrix.of_apply, eq_self_iff_true, if_true]
    ring
  have hYoff1 : ∀ a s t : Fin n, s ≠ t → Ymat g n (a, t) (a, s) = 0 := by
    intro a s t hst
    unfold Ymat
    simp only [Matrix.of_apply, eq_self_iff_true, if_true, if_neg (Ne.symm hst), mul_zero]
  have hcirc0 : ∀ i ∈ Finset.Icc 1 (n / 2), ∀ s : Fin n, circBasis n i s s = 0 := by
    intro i hi s
    have hi' := Finset.mem_Icc.mp hi
    have hin : i < n := by omega
    have hs := s.isLt
    have hc : ¬ (((s : ℕ) + n - s) % n = i % n) := by
      rw [show (s : ℕ) + n - s = n by omega, Nat.mod_self, Nat.mod_eq_of_lt hin]
      omega
    unfold circBasis
    simp only [Matrix.of_apply, if_neg hc, add_zero]
  have hAd : ∀ s : Fin n, Amat g n s s = 0 := by
    intro s
    unfold Amat
    rw [comb_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hcirc0 i hi s, mul_zero]
  have hBd : ∀ s : Fin n, Bmat g n s s = 0 := by
    intro s
    unfold Bmat
    rw [comb_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hcirc0 i hi s, mul_zero]
  have hYoff2 : ∀ a b s : Fin n, a ≠ b → Ymat g n (b, s) (a, s) = 0 := by
    intro a b s hab
    unfold Ymat
    simp only [Matrix.of_apply, if_neg (Ne.symm hab)]
    split_ifs
    · rw [hAd, mul_zero]
    · rw [hBd, mul_zero]
  have hJ : ∀ s t : Fin n, (Matrix.of (fun _ _ => (1 : ℝ)) - 1 : Matrix (Fin n) (Fin n) ℝ) s t
      = if s = t then 0 else 1 := by
    intro s t
    rw [Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  have hc412 := TSPSDPGap.c412_sol g n hg hg2 hgn hlt
  unfold IsSDP1Feasible
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [tr_kron1]
    have e : ∀ a : Fin n, ∑ s : Fin n, ∑ t : Fin n,
        Matrix.single j j (1 : ℝ) s t * Ymat g n (a, t) (a, s) = Ymat g n (a, j) (a, j) := by
      intro a
      rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single j]
        · rw [Matrix.single_apply_same, one_mul]
        · intro t _ htj
          rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => htj h.2.symm), zero_mul]
        · intro h
          exact absurd (Finset.mem_univ j) h
      · intro s _ hsj
        apply Finset.sum_eq_zero
        intro t _
        rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hsj h.1.symm), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [Finset.sum_congr rfl (fun a _ => e a)]
    simp only [hYd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hnR
  · intro j
    rw [tr_kron2]
    have e : ∑ a : Fin n, ∑ s : Fin n, ∑ b : Fin n,
        Matrix.single j j (1 : ℝ) a b * Ymat g n (b, s) (a, s)
          = ∑ s : Fin n, Ymat g n (j, s) (j, s) := by
      rw [Finset.sum_eq_single j]
      · refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.sum_eq_single j]
        · rw [Matrix.single_apply_same, one_mul]
        · intro b _ hbj
          rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hbj h.2.symm), zero_mul]
        · intro h
          exact absurd (Finset.mem_univ j) h
      · intro a _ haj
        apply Finset.sum_eq_zero
        intro s _
        apply Finset.sum_eq_zero
        intro b _
        rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => haj h.1.symm), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [e]
    simp only [hYd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hnR
  · rw [Matrix.add_mul, Matrix.trace_add, tr_kron1, tr_kron2]
    have z1 : ∑ a : Fin n, ∑ s : Fin n, ∑ t : Fin n,
        (Matrix.of (fun _ _ => (1 : ℝ)) - 1 : Matrix (Fin n) (Fin n) ℝ) s t
          * Ymat g n (a, t) (a, s) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro t _
      rw [hJ]
      by_cases hst : s = t
      · rw [if_pos hst, zero_mul]
      · rw [if_neg hst, hYoff1 a s t hst, mul_zero]
    have z2 : ∑ a : Fin n, ∑ s : Fin n, ∑ b : Fin n,
        (Matrix.of (fun _ _ => (1 : ℝ)) - 1 : Matrix (Fin n) (Fin n) ℝ) a b
          * Ymat g n (b, s) (a, s) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro b _
      rw [hJ]
      by_cases hab : a = b
      · rw [if_pos hab, zero_mul]
      · rw [if_neg hab, hYoff2 a b s hab, mul_zero]
    rw [z1, z2, add_zero]
  · exact TSPSDPGap.c47_sol g n hg hg2 hgn hlt
  · exact hc412.2.2
  · have key : ∀ x y, Ymat g n x y = (1 / (2 * (n : ℝ))) * ((2 * (n : ℝ)) • Ymat g n) x y := by
      intro x y
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, one_div_mul_cancel h2n, one_mul]
    ext ⟨a, s⟩ ⟨b, t⟩
    rw [Matrix.transpose_apply, key, key, M_apply g n hn, M_apply g n hn, Kb_swap]
  · exact Y_psd g n hg hg2 hgn hlt hc412.1
