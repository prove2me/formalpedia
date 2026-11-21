-- Prove2me | solution 1 for TSPSDPGap.claim_4_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:23:49.064921+00:00
-- url     : https://prove2.me/submissions/732cd6a2-859e-4221-ad28-9f291667e828

import Mathlib
import Definitions.Def_TSPSDPGap_Amat
import Definitions.Def_TSPSDPGap_Bmat
import Definitions.Def_TSPSDPGap_aHat
import Definitions.Def_TSPSDPGap_bHat

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

open TSPSDPGap TSPSDPGap.Aux_R6 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    let w : Fin n → ℂ := fun k =>
      Complex.exp (-2 * (Real.pi : ℂ) * ((k : ℕ) : ℂ) * Complex.I / (n : ℂ))
    let v : Fin n → Fin n → ℂ := fun k u => w k ^ (u : ℕ)
    (∀ k : Fin n,
      ((Amat g n).map (fun x : ℝ => (x : ℂ))).mulVec (v k) = ((2 * aHat g n k : ℝ) : ℂ) • v k ∧
      ((Bmat g n).map (fun x : ℝ => (x : ℂ))).mulVec (v k) = ((2 * bHat g n k : ℝ) : ℂ) • v k) ∧
    LinearIndependent ℂ v ∧
    spectrum ℝ (Amat g n) = Set.range (fun k : Fin n => 2 * aHat g n k) ∧
    spectrum ℝ (Bmat g n) = Set.range (fun k : Fin n => 2 * bHat g n k) := by
  intro w v
  have hn2 : 2 ≤ n := by omega
  have hn : 0 < n := by omega
  have hvV : v = fun (k u : Fin n) => V n k u := by
    funext k u
    show (Complex.exp (-2 * (Real.pi : ℂ) * ((k : ℕ) : ℂ) * Complex.I / (n : ℂ))) ^ (u : ℕ)
      = V n k u
    unfold V E
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  clear_value w v
  subst hvV
  refine ⟨fun k => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · ext s
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    unfold Amat aHat
    exact comb_eig n k hn2 (coeffA g n) s
  · ext s
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    unfold Bmat bHat
    exact comb_eig n k hn2 (coeffB g n) s
  · rw [Fintype.linearIndependent_iff]
    intro c hc l
    have hcu : ∀ u : Fin n, ∑ k : Fin n, c k * V n k u = 0 := by
      intro u
      have := congrFun hc u
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have e1 : ∀ u : Fin n, (∑ k : Fin n, c k * V n k u) * E n (((l : ℕ) : ℤ) * ((u : ℕ) : ℤ))
        = ∑ k : Fin n, c k * E n (((u : ℕ) : ℤ) * (((l : ℕ) : ℤ) - ((k : ℕ) : ℤ))) := by
      intro u
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      unfold V
      rw [mul_assoc, ← E_add]
      congr 2
      ring
    have key : ∑ u : Fin n, (∑ k : Fin n, c k * V n k u) * E n (((l : ℕ) : ℤ) * ((u : ℕ) : ℤ))
        = (n : ℂ) * c l := by
      rw [Finset.sum_congr rfl (fun u _ => e1 u), Finset.sum_comm]
      rw [Finset.sum_eq_single l]
      · rw [← Finset.mul_sum, orth n hn, if_pos (by simp)]
        ring
      · intro k _ hkl
        rw [← Finset.mul_sum, orth n hn, if_neg, mul_zero]
        rw [dvd_iff_eq]
        exact hkl
      · intro h
        exact absurd (Finset.mem_univ l) h
    have h0 : (n : ℂ) * c l = 0 := by
      rw [← key]
      simp [hcu]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    exact (mul_eq_zero.mp h0).resolve_left hnC
  · apply spec_circ n hn (Amat g n) (fun k : Fin n => 2 * aHat g n k)
    · intro s t
      unfold Amat
      exact comb_symm n (coeffA g n) s t
    · intro k s
      unfold Amat aHat
      exact comb_eig n k hn2 (coeffA g n) s
  · apply spec_circ n hn (Bmat g n) (fun k : Fin n => 2 * bHat g n k)
    · intro s t
      unfold Bmat
      exact comb_symm n (coeffB g n) s t
    · intro k s
      unfold Bmat bHat
      exact comb_eig n k hn2 (coeffB g n) s
