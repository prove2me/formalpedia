-- Prove2me | solution 1 for ZudilinZeta.zudilin_partial_fraction_constant_shift
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T14:10:10.445068+00:00
-- url     : https://prove2.me/submissions/e6ba371a-f8f5-47ad-93f5-48a404172eed

import Definitions.Def_ZudilinZetaCoefficientArithmetic

set_option autoImplicit false


-- VariablePartialFractions.lean

set_option autoImplicit false

open Polynomial Finset

/-- A simultaneous real evaluation of Mathlib's partial fractions, with rational residues. -/
lemma rational_partial_fraction_variable_expansion (K : Finset ℕ) (μ : ℕ → ℕ) (A : ℚ[X]) :
    ∃ (Q : ℚ[X]) (c : (k : ℕ) → Fin (μ k) → ℚ),
      ∀ t : ℝ, (∀ k ∈ K, t + (k : ℝ) ≠ 0) →
        A.eval₂ (algebraMap ℚ ℝ) t / (∏ k ∈ K, (t + (k : ℝ)) ^ (μ k)) =
          Q.eval₂ (algebraMap ℚ ℝ) t +
            ∑ k ∈ K, ∑ j : Fin (μ k), (c k j : ℝ) / (t + (k : ℝ)) ^ (j.val + 1) := by
  classical
  let U := {t : ℝ // ∀ k ∈ K, t + (k : ℝ) ≠ 0}
  let ev : ℚ[X] →+* (U → ℝ) :=
    RingHom.pi (fun t => Polynomial.eval₂RingHom (algebraMap ℚ ℝ) t.val)
  let : Algebra ℚ[X] (U → ℝ) := ev.toAlgebra
  let g : ℕ → ℚ[X] := fun k => X + C (k : ℚ)
  have hg (k : ℕ) (hk : k ∈ K) : (g k).Monic := monic_X_add_C _
  have hcop : Set.Pairwise (↑K : Set ℕ) (fun k l => IsCoprime (g k) (g l)) := by
    intro k hk l hl hkl
    have h : Function.Injective (fun k : ℕ => -(k : ℚ)) := by
      intro a b hab
      exact_mod_cast neg_injective hab
    simpa only [g, map_neg, sub_neg_eq_add] using pairwise_coprime_X_sub_C h hkl
  let gi : ℕ → U → ℝ := fun k t => (t.val + (k : ℝ))⁻¹
  have hgi (k : ℕ) (hk : k ∈ K) : gi k * algebraMap ℚ[X] (U → ℝ) (g k) = 1 := by
    funext t
    change (t.val + (k : ℝ))⁻¹ * (g k).eval₂ (algebraMap ℚ ℝ) t.val = 1
    simpa [g] using inv_mul_cancel₀ (t.property k hk)
  obtain ⟨Q, c, hc, he⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse A hg hcop μ hgi
  refine ⟨Q, fun k j => (c k j).coeff 0, ?_⟩
  intro t ht
  have he' := congrFun he (⟨t, ht⟩ : U)
  simp only [Pi.mul_apply, Pi.add_apply, Finset.prod_apply, Finset.sum_apply,
    Pi.pow_apply] at he'
  change A.eval₂ (algebraMap ℚ ℝ) t * (∏ k ∈ K, ((t + (k : ℝ))⁻¹)^(μ k)) =
    Q.eval₂ (algebraMap ℚ ℝ) t +
      ∑ k ∈ K, ∑ j : Fin (μ k), (c k j).eval₂ (algebraMap ℚ ℝ) t *
        ((t + (k : ℝ))⁻¹)^(j.val+1) at he'
  have hconst (k : ℕ) (hk : k ∈ K) (j : Fin (μ k)) :
      (c k j).eval₂ (algebraMap ℚ ℝ) t = ((c k j).coeff 0 : ℝ) := by
    have hd := hc k hk j
    simp only [g, degree_X_add_C] at hd
    have hd' : (c k j).degree ≤ 0 := by exact (Order.lt_succ_iff).mp hd
    conv_lhs => rw [eq_C_of_degree_le_zero hd', eval₂_C]
    rfl
  simp only [inv_pow, prod_inv_distrib, ← div_eq_mul_inv] at he'
  rw [he']
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro j hj
  rw [hconst k hk j]

open Filter
open scoped Topology

/-- Decay at infinity eliminates the polynomial part of a rational partial fraction expansion. -/
lemma proper_rational_partial_fraction_variable_expansion (K : Finset ℕ) (μ : ℕ → ℕ) (A : ℚ[X])
    (hlim : Tendsto (fun t : ℝ => A.eval₂ (algebraMap ℚ ℝ) t /
      (∏ k ∈ K, (t + (k : ℝ)) ^ (μ k))) atTop (𝓝 0)) :
    ∃ c : (k : ℕ) → Fin (μ k) → ℚ,
      ∀ t : ℝ, (∀ k ∈ K, t + (k : ℝ) ≠ 0) →
        A.eval₂ (algebraMap ℚ ℝ) t / (∏ k ∈ K, (t + (k : ℝ)) ^ (μ k)) =
          ∑ k ∈ K, ∑ j : Fin (μ k), (c k j : ℝ) / (t + (k : ℝ)) ^ (j.val + 1) := by
  obtain ⟨Q, c, he⟩ := rational_partial_fraction_variable_expansion K μ A
  have hc : Tendsto (fun t : ℝ => ∑ k ∈ K, ∑ j : Fin (μ k),
      (c k j : ℝ) / (t + (k : ℝ)) ^ (j.val+1)) atTop (𝓝 0) := by
    have h (k : ℕ) (j : Fin (μ k)) : Tendsto
        (fun t : ℝ => (c k j : ℝ) / (t + (k : ℝ)) ^ (j.val+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega : j.val+1 ≠ 0)).comp
        (tendsto_id.atTop_add tendsto_const_nhds))
    simpa only [sum_const_zero] using tendsto_finsetSum K (fun k hk =>
      tendsto_finsetSum univ (fun j hj => h k j))
  have hq : Tendsto (fun t : ℝ => Q.eval₂ (algebraMap ℚ ℝ) t) atTop (𝓝 0) := by
    have h := hlim.sub hc
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [he t (fun k hk => (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg k)).ne')]
    simp
  have hq0 : Q.map (algebraMap ℚ ℝ) = 0 := by
    apply leadingCoeff_eq_zero.mp
    apply ((Q.map (algebraMap ℚ ℝ)).tendsto_nhds_iff.mp ?_).1
    simpa only [eval_map] using hq
  refine ⟨c, fun t ht => ?_⟩
  have hQeval : Q.eval₂ (algebraMap ℚ ℝ) t = 0 := by
    rw [eval₂_eq_eval_map, hq0, eval_zero]
  simpa only [hQeval, zero_add] using he t ht


-- PartialFractionUniqueness.lean

set_option autoImplicit false

open Polynomial Finset

lemma partial_fraction_coeffs_unique (K : Finset ℕ) (S : ℕ)
    (hK : ∀ k ∈ K, 0 < k) (c d : ℕ → Fin S → ℚ)
    (he : ∀ t : ℝ, -1 < t →
      (∑ k ∈ K, ∑ j : Fin S, (c k j : ℝ)/(t+(k : ℝ))^(j.val+1)) =
        ∑ k ∈ K, ∑ j : Fin S, (d k j : ℝ)/(t+(k : ℝ))^(j.val+1)) :
    ∀ k ∈ K, c k = d k := by
  classical
  let U := {t : ℝ // -1 < t}
  let ev : ℚ[X] →+* (U → ℝ) :=
    RingHom.pi (fun t => Polynomial.eval₂RingHom (algebraMap ℚ ℝ) t.val)
  let : Algebra ℚ[X] (U → ℝ) := ev.toAlgebra
  have hev : Function.Injective ev := by
    intro A B hAB
    have hreal : A.map (algebraMap ℚ ℝ) = B.map (algebraMap ℚ ℝ) := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.Ioi_infinite (-1 : ℝ)).mono
      intro t ht
      have h := congrFun hAB (⟨t, ht⟩ : U)
      change A.eval₂ (algebraMap ℚ ℝ) t = B.eval₂ (algebraMap ℚ ℝ) t at h
      simpa only [Set.mem_ofPred_eq, eval_map] using h
    exact Polynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective hreal
  let : FaithfulSMul ℚ[X] (U → ℝ) :=
    (faithfulSMul_iff_algebraMap_injective ℚ[X] (U → ℝ)).mpr hev
  let g : ℕ → ℚ[X] := fun k => X + C (k : ℚ)
  have hg (k : ℕ) (hk : k ∈ K) : (g k).Monic := monic_X_add_C _
  have hcop : Set.Pairwise (↑K : Set ℕ) (fun k l => IsCoprime (g k) (g l)) := by
    intro k hk l hl hkl
    have h : Function.Injective (fun k : ℕ => -(k : ℚ)) := by
      intro a b hab
      exact_mod_cast neg_injective hab
    simpa only [g, map_neg, sub_neg_eq_add] using pairwise_coprime_X_sub_C h hkl
  let gi : ℕ → U → ℝ := fun k t => (t.val+(k : ℝ))⁻¹
  have hgi (k : ℕ) (hk : k ∈ K) : gi k * algebraMap ℚ[X] (U → ℝ) (g k) = 1 := by
    funext t
    change (t.val+(k : ℝ))⁻¹ * (g k).eval₂ (algebraMap ℚ ℝ) t.val = 1
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hK k hk
    have hne : t.val+(k : ℝ) ≠ 0 := by have := t.property; linarith
    simpa [g] using inv_mul_cancel₀ hne
  have hdeg (a : ℚ) (k : ℕ) : (C a).degree < (g k).degree := by
    apply degree_C_le.trans_lt
    simp only [g, degree_X_add_C]
    norm_num
  have hevC (a : ℚ) : algebraMap ℚ[X] (U → ℝ) (C a) = fun _ => (a : ℝ) := by
    funext t
    change (C a).eval₂ (algebraMap ℚ ℝ) t.val = (a : ℝ)
    rw [eval₂_C]
    rfl
  have hf : algebraMap ℚ[X] (U → ℝ) (0 : ℚ[X]) +
      (∑ k ∈ K, ∑ j : Fin S, algebraMap ℚ[X] (U → ℝ) (C (c k j)) * gi k^(j.val+1)) =
      algebraMap ℚ[X] (U → ℝ) (0 : ℚ[X]) +
      (∑ k ∈ K, ∑ j : Fin S, algebraMap ℚ[X] (U → ℝ) (C (d k j)) * gi k^(j.val+1)) := by
    simp only [map_zero, zero_add]
    funext t
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hevC]
    change (∑ k ∈ K, ∑ j : Fin S, (c k j : ℝ) * ((t.val+(k : ℝ))⁻¹)^(j.val+1)) =
      ∑ k ∈ K, ∑ j : Fin S, (d k j : ℝ) * ((t.val+(k : ℝ))⁻¹)^(j.val+1)
    simpa only [inv_pow, div_eq_mul_inv] using he t.val t.property
  have h := quo_add_sum_rem_mul_pow_inverse_unique hg hcop hgi
    (n := fun _ => S) (fun k hk j => hdeg (c k j) k) (fun k hk j => hdeg (d k j) k) hf
  intro k hk
  funext j
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) (congrFun (h.2 k hk) j)
  simpa only [coeff_C_zero] using hc

-- DecayFromConvergence.lean
/-
The rational-function degree bookkeeping below is reused from mrfancypants,
accepted Prove2Me submission 85b357a0-c802-42df-a9b9-9d6ed8493709,
for the mission series-convergence theorem. The final decay consequence is new.
-/

set_option autoImplicit false

namespace ZudilinZeta

open Polynomial Filter Asymptotics Topology

/-- `f` agrees on `(-1, ∞)` with a ratio `A / B` of real polynomials, `B` nonvanishing there,
and `deg A - deg B ≤ d`. -/
def aux_zz_RD (f : ℝ → ℝ) (d : ℤ) : Prop :=
  ∃ A B : ℝ[X], (∀ t : ℝ, -1 < t → B.eval t ≠ 0) ∧
    (∀ t : ℝ, -1 < t → f t = A.eval t / B.eval t) ∧ (A.natDegree : ℤ) - B.natDegree ≤ d

theorem aux_zz_RD_mono {f : ℝ → ℝ} {d d' : ℤ} (h : aux_zz_RD f d) (hd : d ≤ d') :
    aux_zz_RD f d' := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨A, B, h1, h2, h3.trans hd⟩

theorem aux_zz_RD_congr {f g : ℝ → ℝ} {d : ℤ} (h : aux_zz_RD f d)
    (hfg : ∀ t : ℝ, -1 < t → f t = g t) : aux_zz_RD g d := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨A, B, h1, fun t ht => (hfg t ht).symm.trans (h2 t ht), h3⟩

theorem aux_zz_RD_mul {f g : ℝ → ℝ} {d₁ d₂ : ℤ} (hf : aux_zz_RD f d₁) (hg : aux_zz_RD g d₂) :
    aux_zz_RD (fun t => f t * g t) (d₁ + d₂) := by
  obtain ⟨A₁, B₁, h1, h2, h3⟩ := hf
  obtain ⟨A₂, B₂, h1', h2', h3'⟩ := hg
  have hB₁ : B₁ ≠ 0 := by
    intro h; exact h1 0 (by norm_num) (by simp [h])
  have hB₂ : B₂ ≠ 0 := by
    intro h; exact h1' 0 (by norm_num) (by simp [h])
  refine ⟨A₁ * A₂, B₁ * B₂, ?_, ?_, ?_⟩
  · intro t ht
    rw [eval_mul]
    exact mul_ne_zero (h1 t ht) (h1' t ht)
  · intro t ht
    show f t * g t = _
    rw [eval_mul, eval_mul, h2 t ht, h2' t ht, div_mul_div_comm]
  · rw [natDegree_mul hB₁ hB₂]
    have : ((A₁ * A₂).natDegree : ℤ) ≤ A₁.natDegree + A₂.natDegree := by
      exact_mod_cast natDegree_mul_le
    push_cast
    linarith

theorem aux_zz_RD_const (c : ℝ) : aux_zz_RD (fun _ => c) 0 := by
  refine ⟨C c, 1, fun t _ => by simp, fun t _ => by simp, by simp⟩

theorem aux_zz_RD_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (d : ι → ℤ)
    (h : ∀ i ∈ s, aux_zz_RD (f i) (d i)) :
    aux_zz_RD (fun t => ∏ i ∈ s, f i t) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact aux_zz_RD_const 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine aux_zz_RD_congr (aux_zz_RD_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))) ?_
    intro t _
    rw [Finset.prod_insert ha]

theorem aux_zz_RD_lin (c : ℝ) : aux_zz_RD (fun t => c + 2 * t) 1 := by
  refine ⟨C 2 * X + C c, 1, fun t _ => by simp, fun t _ => by simp; ring, ?_⟩
  have := natDegree_linear_le (a := (2:ℝ)) (b := c)
  simp only [natDegree_one, Nat.cast_zero, sub_zero]
  exact_mod_cast this

theorem aux_zz_Gamma_add_nat (s : ℝ) (hs : 0 < s) (m : ℕ) :
    Real.Gamma (s + m) = Real.Gamma s * ∏ i ∈ Finset.range m, (s + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc,
      Real.Gamma_add_one (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg m)).ne', ih]
    ring

theorem aux_zz_natDegree_prod (a : ℝ) (m : ℕ) :
    (∏ i ∈ Finset.range m, (X + C (a + i))).natDegree = m := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem aux_zz_RD_up (a b : ℝ) (m : ℕ) (ha : 1 ≤ a) (hb : b = a + m) :
    aux_zz_RD (fun t => Real.Gamma (b + t) / Real.Gamma (a + t)) m := by
  refine ⟨∏ i ∈ Finset.range m, (X + C (a + i)), 1, fun t _ => by simp, ?_, ?_⟩
  · intro t ht
    have hpos : 0 < a + t := by linarith
    have hΓ : Real.Gamma (a + t) ≠ 0 := (Real.Gamma_pos_of_pos hpos).ne'
    have e : b + t = (a + t) + m := by rw [hb]; ring
    show Real.Gamma (b + t) / Real.Gamma (a + t) = _
    rw [e, aux_zz_Gamma_add_nat _ hpos, eval_one, div_one, eval_prod,
      mul_div_cancel_left₀ _ hΓ]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [eval_add, eval_X, eval_C]
    ring
  · rw [aux_zz_natDegree_prod]
    simp

theorem aux_zz_RD_down (a b : ℝ) (m : ℕ) (ha : 1 ≤ a) (hb : b = a + m) :
    aux_zz_RD (fun t => Real.Gamma (a + t) / Real.Gamma (b + t)) (-(m : ℤ)) := by
  refine ⟨1, ∏ i ∈ Finset.range m, (X + C (a + i)), ?_, ?_, ?_⟩
  · intro t ht
    rw [eval_prod]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    rw [eval_add, eval_X, eval_C]
    have : (0:ℝ) ≤ i := Nat.cast_nonneg i
    exact ne_of_gt (by linarith)
  · intro t ht
    have hpos : 0 < a + t := by linarith
    have hΓ : Real.Gamma (a + t) ≠ 0 := (Real.Gamma_pos_of_pos hpos).ne'
    have e : b + t = (a + t) + m := by rw [hb]; ring
    have hp : ∏ i ∈ Finset.range m, (a + t + (i : ℝ)) =
        ∏ i ∈ Finset.range m, eval t (X + C (a + i)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [eval_add, eval_X, eval_C]
      ring
    show Real.Gamma (a + t) / Real.Gamma (b + t) = _
    rw [e, aux_zz_Gamma_add_nat _ hpos, eval_one, eval_prod, ← hp,
      div_mul_cancel_left₀ hΓ, one_div]
  · rw [aux_zz_natDegree_prod]
    simp

theorem aux_zz_eta_mono (P : Params) (k : ℕ) :
    ∀ j, 1 ≤ j → j + k ≤ P.q → P.eta j ≤ P.eta (j + k) := by
  induction k with
  | zero => intro j _ _; simp
  | succ k ih =>
    intro j hj hjk
    have h1 := ih j hj (by omega)
    have h2 := P.eta_mono (j + k) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    rw [← add_assoc]; exact h1.trans h2

theorem aux_zz_eta_le (P : Params) (j : ℕ) (hj : j ∈ Finset.Icc 1 P.q) :
    2 * P.eta j ≤ P.eta 0 := by
  rw [Finset.mem_Icc] at hj
  have := aux_zz_eta_mono P (P.q - j) j hj.1 (by omega)
  rw [show j + (P.q - j) = P.q by omega] at this
  have := P.eta_lt
  omega

theorem aux_zz_RD_R (P : Params) (n : ℕ) : aux_zz_RD (R P n) (-2) := by
  have hq := P.q_ge
  have hh0 : hh P n 0 = P.eta 0 * n + 2 := by simp [hh]
  have hhj : ∀ j, 1 ≤ j → hh P n j = P.eta j * n + 1 := fun j hj => by
    simp [hh, show j ≠ 0 by omega]
  have hle : ∀ j ∈ Finset.Icc 1 P.q, 2 * (P.eta j * n) ≤ P.eta 0 * n := fun j hj => by
    have := Nat.mul_le_mul_right n (aux_zz_eta_le P j hj)
    rw [mul_assoc] at this
    exact this
  have e1 : aux_zz_RD (fun t => (hh P n 0 : ℝ) + 2 * t) 1 := aux_zz_RD_lin _
  have e2 : aux_zz_RD (fun t => ∏ j ∈ Finset.Icc 1 P.r,
        (1 / (Nat.factorial (hh P n j - 1) : ℝ)) * Real.Gamma ((hh P n j : ℝ) + t)
          / Real.Gamma (1 + t)) (∑ j ∈ Finset.Icc 1 P.r, ((P.eta j * n : ℕ) : ℤ)) := by
    apply aux_zz_RD_prod
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h := aux_zz_RD_mul (aux_zz_RD_const (1 / (Nat.factorial (hh P n j - 1) : ℝ)))
      (aux_zz_RD_up 1 (hh P n j : ℝ) (P.eta j * n) le_rfl
        (by rw [hhj j hj1]; push_cast; ring))
    exact aux_zz_RD_mono (aux_zz_RD_congr h (fun t _ => by simp only [mul_div_assoc]))
      (by simp)
  have e3 : aux_zz_RD (fun t => ∏ j ∈ Finset.Icc 1 P.r,
        (1 / (Nat.factorial (hh P n j - 1) : ℝ)) * Real.Gamma ((hh P n 0 : ℝ) + t)
          / Real.Gamma (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ) + t))
        (∑ j ∈ Finset.Icc 1 P.r, ((P.eta j * n : ℕ) : ℤ)) := by
    apply aux_zz_RD_prod
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjq : j ∈ Finset.Icc 1 P.q :=
      Finset.mem_Icc.mpr ⟨hj1, by have := (Finset.mem_Icc.mp hj).2; omega⟩
    have hl := hle j hjq
    have hcast : (hh P n j : ℝ) ≤ (hh P n 0 : ℝ) := by
      rw [hh0, hhj j hj1]; exact_mod_cast (by omega)
    have h := aux_zz_RD_mul (aux_zz_RD_const (1 / (Nat.factorial (hh P n j - 1) : ℝ)))
      (aux_zz_RD_up (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ)) (hh P n 0 : ℝ) (P.eta j * n)
        (by linarith) (by rw [hhj j hj1]; push_cast; ring))
    exact aux_zz_RD_mono (aux_zz_RD_congr h (fun t _ => by simp only [mul_div_assoc]))
      (by simp)
  have e4 : aux_zz_RD (fun t => ∏ j ∈ Finset.Icc (P.r + 1) P.q,
        (Nat.factorial (hh P n 0 - 2 * hh P n j) : ℝ) * Real.Gamma ((hh P n j : ℝ) + t)
          / Real.Gamma (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ) + t))
        (∑ j ∈ Finset.Icc (P.r + 1) P.q,
          -(((1 + P.eta 0 * n - 2 * (P.eta j * n)) : ℕ) : ℤ)) := by
    apply aux_zz_RD_prod
    intro j hj
    have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hjq : j ∈ Finset.Icc 1 P.q := Finset.mem_Icc.mpr ⟨hj1, (Finset.mem_Icc.mp hj).2⟩
    have hl := hle j hjq
    have hm : (((1 + P.eta 0 * n - 2 * (P.eta j * n)) : ℕ) : ℝ) =
        1 + ((P.eta 0 * n : ℕ) : ℝ) - 2 * ((P.eta j * n : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h := aux_zz_RD_mul (aux_zz_RD_const (Nat.factorial (hh P n 0 - 2 * hh P n j) : ℝ))
      (aux_zz_RD_down (hh P n j : ℝ) (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ))
        (1 + P.eta 0 * n - 2 * (P.eta j * n))
        (by rw [hhj j hj1]; push_cast; have : (0:ℝ) ≤ (P.eta j : ℝ) * n := by positivity
            linarith)
        (by rw [hm, hh0, hhj j hj1]; push_cast; ring))
    exact aux_zz_RD_mono (aux_zz_RD_congr h (fun t _ => by simp only [mul_div_assoc]))
      (by simp)
  have e := aux_zz_RD_mul (aux_zz_RD_mul (aux_zz_RD_mul e1 e2) e3) e4
  refine aux_zz_RD_mono (aux_zz_RD_congr e (fun t _ => rfl)) ?_
  -- arithmetic
  have hT : (∑ j ∈ Finset.Icc (P.r + 1) P.q,
          -(((1 + P.eta 0 * n - 2 * (P.eta j * n)) : ℕ) : ℤ)) =
      ∑ j ∈ Finset.Icc (P.r + 1) P.q, (-(1 + (P.eta 0 : ℤ) * n) + 2 * n * (P.eta j : ℤ)) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hjq : j ∈ Finset.Icc 1 P.q := Finset.mem_Icc.mpr ⟨hj1, (Finset.mem_Icc.mp hj).2⟩
    have hl := hle j hjq
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hS : (∑ j ∈ Finset.Icc 1 P.r, ((P.eta j * n : ℕ) : ℤ)) =
      (n : ℤ) * ∑ j ∈ Finset.Icc 1 P.r, (P.eta j : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast; ring
  rw [hT, hS, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, ← Finset.mul_sum]
  have hsplit : ∑ j ∈ Finset.Icc 1 P.r, P.eta j + ∑ j ∈ Finset.Icc (P.r + 1) P.q, P.eta j =
      ∑ j ∈ Finset.Icc 1 P.q, P.eta j := by
    rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
      ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_consecutive _ (by omega) (by omega)]
  have hsum := P.sum_le
  rw [← hsplit] at hsum
  have hsum' := Nat.mul_le_mul_right n hsum
  have hsumZ : ((2 * (∑ j ∈ Finset.Icc 1 P.r, P.eta j +
      ∑ j ∈ Finset.Icc (P.r + 1) P.q, P.eta j) * n : ℕ) : ℤ) ≤
      ((P.eta 0 * (P.q - P.r) * n : ℕ) : ℤ) := by exact_mod_cast hsum'
  have hcard : P.q + 1 - (P.r + 1) = P.q - P.r := by omega
  rw [hcard]
  push_cast [nsmul_eq_mul, Nat.cast_sub (show P.r ≤ P.q by omega)] at hsumZ ⊢
  have hqr : (4 : ℤ) ≤ (P.q : ℤ) - P.r := by
    have : P.r + 4 ≤ P.q := hq
    omega
  linarith


theorem rational_function_decay (P : Params) (n : ℕ) :
    Tendsto (R P n) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => t * R P n t) atTop (𝓝 0) := by
  obtain ⟨A, B, hB, hR, hd⟩ := aux_zz_RD_R P n
  have hB0 : B ≠ 0 := by
    intro hz
    exact hB 0 (by norm_num) (by simp [hz])
  have hnat : A.natDegree + 2 ≤ B.natDegree := by omega
  have hdeg : A.degree < B.degree := by
    rw [degree_eq_natDegree hB0]
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show A.natDegree < B.natDegree by omega)
  have hdegX : ((X : ℝ[X]) * A).degree < B.degree := by
    rw [degree_eq_natDegree hB0]
    apply degree_le_natDegree.trans_lt
    have h := natDegree_mul_le (p := (X : ℝ[X])) (q := A)
    rw [natDegree_X] at h
    exact_mod_cast (show ((X : ℝ[X]) * A).natDegree < B.natDegree by omega)
  constructor
  · apply (div_tendsto_atTop_zero_of_degree_lt A B hdeg).congr'
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with t ht
    exact (hR t ht).symm
  · have h := div_tendsto_atTop_zero_of_degree_lt ((X : ℝ[X]) * A) B hdegX
    apply h.congr'
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with t ht
    rw [eval_mul, eval_X, hR t ht]
    ring

end ZudilinZeta

-- RationalModel.lean
namespace ZudilinZeta

open Polynomial Finset Filter
open scoped Topology

noncomputable def pfInterval (a b : ℕ) : ℚ[X] := ∏ k ∈ Ico a b, (X + C (k : ℚ))

noncomputable def pfNumerator (P : Params) (n : ℕ) : ℚ[X] :=
  (C (hh P n 0 : ℚ) + C 2 * X) *
    (∏ j ∈ Icc 1 P.r, C (1 / ((hh P n j - 1).factorial : ℚ)) *
      pfInterval 1 (hh P n j)) *
    (∏ j ∈ Icc 1 P.r, C (1 / ((hh P n j - 1).factorial : ℚ)) *
      pfInterval (hh P n 0 + 1 - hh P n j) (hh P n 0)) *
    (∏ j ∈ Icc (P.r+1) P.q, C ((hh P n 0 - 2 * hh P n j).factorial : ℚ))

noncomputable def pfDenominator (P : Params) (n : ℕ) : ℚ[X] :=
  ∏ j ∈ Icc (P.r+1) P.q, pfInterval (hh P n j) (hh P n 0 + 1 - hh P n j)

lemma pfInterval_eval (a b : ℕ) (t : ℝ) :
    (pfInterval a b).eval₂ (algebraMap ℚ ℝ) t = ∏ k ∈ Ico a b, (t + (k : ℝ)) := by
  simp [pfInterval, eval₂_finsetProd]

lemma pfInterval_reflect (a b H : ℕ) (hb : b ≤ H+1) (t : ℝ) :
    (pfInterval a b).eval₂ (algebraMap ℚ ℝ) (-(H : ℝ)-t) =
      (-1 : ℝ)^(b-a) * (pfInterval (H+1-b) (H+1-a)).eval₂ (algebraMap ℚ ℝ) t := by
  simp only [pfInterval_eval]
  have he : (∏ k ∈ Ico a b, (-(H : ℝ)-t+(k : ℝ))) =
      ∏ k ∈ Ico a b, -(t+(H-k : ℕ)) := by
    apply prod_congr rfl
    intro k hk
    have hkle : k ≤ H := by have := (mem_Ico.mp hk).2; omega
    rw [Nat.cast_sub hkle]
    ring
  rw [he, Finset.prod_neg, Nat.card_Ico]
  congr 1
  exact prod_Ico_reflect (fun k : ℕ => t+(k : ℝ)) a (n := H) hb

lemma pf_hh_bounds (P : Params) (n j : ℕ) (hj : j ∈ Icc 1 P.q) :
    0 < hh P n j ∧ 2 * hh P n j ≤ hh P n 0 := by
  have hle := Nat.mul_le_mul_right n (aux_zz_eta_le P j hj)
  have hj0 : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
  have he0 : hh P n 0 = P.eta 0*n+2 := by simp [hh]
  have hej : hh P n j = P.eta j*n+1 := by simp [hh, hj0]
  rw [he0, hej]
  rw [mul_assoc] at hle
  omega

lemma pf_gamma_quotient (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (t : ℝ) (ht : -1 < t) :
    Real.Gamma ((b : ℝ)+t) / Real.Gamma ((a : ℝ)+t) =
      (pfInterval a b).eval₂ (algebraMap ℚ ℝ) t := by
  have hapos : 0 < (a : ℝ)+t := by
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have hb : (b : ℝ)+t = ((a : ℝ)+t) + (b-a : ℕ) := by
    rw [Nat.cast_sub hab]
    ring
  rw [hb, aux_zz_Gamma_add_nat _ hapos,
    mul_div_cancel_left₀ _ (Real.Gamma_pos_of_pos hapos).ne']
  simp only [pfInterval, eval₂_finsetProd, eval₂_add, eval₂_X, eval₂_C, map_natCast, eval₂_natCast]
  rw [prod_Ico_eq_prod_range]
  apply prod_congr rfl
  intro i hi
  push_cast
  ring

lemma pf_gamma_inverse_quotient (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (t : ℝ) (ht : -1 < t) :
    Real.Gamma ((a : ℝ)+t) / Real.Gamma ((b : ℝ)+t) =
      1 / (pfInterval a b).eval₂ (algebraMap ℚ ℝ) t := by
  rw [← pf_gamma_quotient a b ha hab t ht, one_div, inv_div]

lemma pf_real_expansion (P : Params) (n : ℕ) (t : ℝ) (ht : -1 < t) :
    R P n t = (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t := by
  have hqr := P.q_ge
  have hreal (j : ℕ) (hj : j ∈ Icc 1 P.q) :
      ((hh P n 0 + 1 - hh P n j : ℕ) : ℝ) = 1 + (hh P n 0 : ℝ) - hh P n j := by
    have hb := pf_hh_bounds P n j hj
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have h1 (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      Real.Gamma ((hh P n j : ℝ)+t) / Real.Gamma (1+t) =
        (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    simpa only [Nat.cast_one] using pf_gamma_quotient 1 (hh P n j) (by omega)
      (pf_hh_bounds P n j hjq).1 t ht
  have h2 (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      Real.Gamma ((hh P n 0 : ℝ)+t) / Real.Gamma (1+(hh P n 0 : ℝ)-hh P n j+t) =
        (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    have hb := pf_hh_bounds P n j hjq
    simpa only [hreal j hjq] using pf_gamma_quotient (hh P n 0+1-hh P n j) (hh P n 0)
      (by omega) (by omega) t ht
  have h3 (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      Real.Gamma ((hh P n j : ℝ)+t) / Real.Gamma (1+(hh P n 0 : ℝ)-hh P n j+t) =
        1 / (pfInterval (hh P n j) (hh P n 0+1-hh P n j)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
    have hb := pf_hh_bounds P n j hjq
    simpa only [hreal j hjq] using pf_gamma_inverse_quotient (hh P n j) (hh P n 0+1-hh P n j)
      hb.1 (by omega) t ht
  simp only [R, pfNumerator, pfDenominator, eval₂_mul, eval₂_add, eval₂_X,
    eval₂_C, eval₂_finsetProd, map_div₀, map_one, map_natCast, map_ofNat, eval₂_natCast, eval₂_ofNat, mul_div_assoc]
  have e1 := prod_congr rfl (fun j hj => congrArg (fun x : ℝ =>
    (1 / ((hh P n j-1).factorial : ℝ))*x) (h1 j hj))
  have e2 := prod_congr rfl (fun j hj => congrArg (fun x : ℝ =>
    (1 / ((hh P n j-1).factorial : ℝ))*x) (h2 j hj))
  have e3 := prod_congr rfl (fun j hj => congrArg (fun x : ℝ =>
    ((hh P n 0-2*hh P n j).factorial : ℝ)*x) (h3 j hj))
  rw [e1, e2, e3]
  simp only [mul_one_div, prod_div_distrib]

lemma pfNumerator_eval (P : Params) (n : ℕ) (t : ℝ) :
    (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t =
      ((hh P n 0 : ℝ)+2*t) *
      (∏ j ∈ Icc 1 P.r, (1 / ((hh P n j-1).factorial : ℝ))^2 *
        (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t *
        (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t) *
      (∏ j ∈ Icc (P.r+1) P.q, ((hh P n 0-2*hh P n j).factorial : ℝ)) := by
  simp only [pfNumerator, eval₂_mul, eval₂_add, eval₂_X, eval₂_C, eval₂_finsetProd,
    map_div₀, map_one, map_natCast, eval₂_natCast, eval₂_ofNat, map_ofNat]
  rw [mul_assoc ((hh P n 0 : ℝ)+2*t), ← prod_mul_distrib]
  congr 2
  apply prod_congr rfl
  intro j hj
  ring

lemma pfNumerator_reflect (P : Params) (n : ℕ) (t : ℝ) :
    (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) =
      -(pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t := by
  have hqr := P.q_ge
  have hpair (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) *
      (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) =
      (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t *
      (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    have hb := pf_hh_bounds P n j hjq
    rw [pfInterval_reflect _ _ _ (by omega), pfInterval_reflect _ _ _ (by omega)]
    have e1 : hh P n 0+1-1 = hh P n 0 := by omega
    have e2 : hh P n 0+1-hh P n 0 = 1 := by omega
    have e3 : hh P n 0+1-(hh P n 0+1-hh P n j) = hh P n j := by omega
    have e4 : hh P n 0-(hh P n 0+1-hh P n j) = hh P n j-1 := by omega
    rw [e1, e2, e3, e4]
    have hs : ((-1 : ℝ)^(hh P n j-1))^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    linear_combination
      ((pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t *
       (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t) * hs
  simp only [pfNumerator_eval]
  have hp : (∏ j ∈ Icc 1 P.r, (1 / ((hh P n j-1).factorial : ℝ))^2 *
      (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) *
      (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t)) =
      ∏ j ∈ Icc 1 P.r, (1 / ((hh P n j-1).factorial : ℝ))^2 *
      (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t *
      (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t := by
    apply prod_congr rfl
    intro j hj
    rw [mul_assoc, hpair j hj, ← mul_assoc]
  rw [hp]
  ring

lemma pfDenominator_reflect (P : Params) (n : ℕ) (t : ℝ) :
    (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) =
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t := by
  have hj (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      (pfInterval (hh P n j) (hh P n 0+1-hh P n j)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) =
      (-1 : ℝ)^(hh P n 0+1) *
        (pfInterval (hh P n j) (hh P n 0+1-hh P n j)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
    have hb := pf_hh_bounds P n j hjq
    rw [pfInterval_reflect _ _ _ (by omega)]
    have he : hh P n 0+1-(hh P n 0+1-hh P n j) = hh P n j := by omega
    rw [he]
    congr 1
    have he : (hh P n 0+1-hh P n j)-hh P n j + 2*hh P n j = hh P n 0+1 := by omega
    have hpow := congrArg (fun e : ℕ => (-1 : ℝ)^e) he
    rw [pow_add, (even_two.mul_right (hh P n j)).neg_one_pow, mul_one] at hpow
    exact hpow
  simp only [pfDenominator, eval₂_finsetProd]
  rw [prod_congr rfl hj, prod_mul_distrib, prod_const, Nat.card_Icc]
  have hc : P.q+1-(P.r+1) = P.q-P.r := by omega
  rw [hc]
  have hp : ((-1 : ℝ)^(hh P n 0+1))^(P.q-P.r) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, (Nat.Odd.sub_odd P.q_odd P.r_odd).neg_one_pow, one_pow]
  rw [hp, one_mul]

lemma pfDenominator_dvd_uniform (P : Params) (n : ℕ) :
    pfDenominator P n ∣ ∏ k ∈ poleRange P n, (X + C (k : ℚ))^(P.q-P.r) := by
  have hqr := P.q_ge
  have hsub (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      Ico (hh P n j) (hh P n 0+1-hh P n j) ⊆ poleRange P n := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
    have hb := pf_hh_bounds P n j hjq
    have hmono := aux_zz_eta_mono P (j-(P.r+1)) (P.r+1) (by omega) (by have := (mem_Icc.mp hj).2; omega)
    have he : P.r+1+(j-(P.r+1)) = j := by have := (mem_Icc.mp hj).1; omega
    rw [he] at hmono
    have hm := Nat.mul_le_mul_right n hmono
    have hlow : hh P n (P.r+1) ≤ hh P n j := by
      simp only [hh, if_neg (show P.r+1 ≠ 0 by omega), if_neg (show j ≠ 0 by have := (mem_Icc.mp hj).1; omega)]
      omega
    intro k hk
    apply mem_Icc.mpr
    have hk' := mem_Ico.mp hk
    omega
  have hd (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      pfInterval (hh P n j) (hh P n 0+1-hh P n j) ∣
        ∏ k ∈ poleRange P n, (X + C (k : ℚ)) :=
    prod_dvd_prod_of_subset _ _ _ (hsub j hj)
  have h := prod_dvd_prod_of_dvd
    (fun j => pfInterval (hh P n j) (hh P n 0+1-hh P n j))
    (fun _ => ∏ k ∈ poleRange P n, (X + C (k : ℚ))) hd
  have hc : P.q+1-(P.r+1) = P.q-P.r := by omega
  simpa only [pfDenominator, prod_const, Nat.card_Icc, hc, prod_pow] using h

lemma pf_uniform_model (P : Params) (n : ℕ) :
    ∃ A : ℚ[X], ∀ t : ℝ, (∀ k ∈ poleRange P n, t+(k : ℝ) ≠ 0) →
      A.eval₂ (algebraMap ℚ ℝ) t / (∏ k ∈ poleRange P n, (t+(k : ℝ))^(P.q-P.r)) =
        (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
          (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t := by
  obtain ⟨B, hB⟩ := pfDenominator_dvd_uniform P n
  refine ⟨pfNumerator P n * B, ?_⟩
  intro t ht
  have hn : (∏ k ∈ poleRange P n, (t+(k : ℝ))^(P.q-P.r)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun k hk => pow_ne_zero _ (ht k hk))
  have he := congrArg (fun p : ℚ[X] => p.eval₂ (algebraMap ℚ ℝ) t) hB
  simp only [eval₂_finsetProd, eval₂_pow, eval₂_mul, eval₂_add, eval₂_X, eval₂_C,
    map_natCast, eval₂_natCast] at he
  have hB0 : B.eval₂ (algebraMap ℚ ℝ) t ≠ 0 := by
    intro hz
    apply hn
    rw [he, hz, mul_zero]
  rw [eval₂_mul, he, mul_div_mul_right _ _ hB0]

end ZudilinZeta

-- PartialFractionContinuation.lean

set_option autoImplicit false

open Polynomial Finset Filter
open scoped Topology

namespace ZudilinZeta

lemma cs_sum_orders (S : ℕ) (f : ℕ → ℝ) :
    (∑ j : Fin S, f (j.val+1)) = ∑ s ∈ Icc 1 S, f s := by
  have index_lt (s : ℕ) (hs : s ∈ Icc 1 S) : s-1 < S := by
    have := mem_Icc.mp hs
    omega
  refine sum_bij' (fun j hj => j.val+1)
    (fun s hs => (⟨s-1, index_lt s hs⟩ : Fin S)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    apply mem_Icc.mpr
    have := j.isLt
    omega
  · intro s hs
    exact mem_univ _
  · intro j hj
    apply Fin.ext
    simp
  · intro s hs
    change (s-1)+1=s
    have := mem_Icc.mp hs
    omega
  · intro j hj
    rfl

lemma cs_pole_pos (P : Params) (n k : ℕ) (hk : k ∈ poleRange P n) : 0 < k := by
  have hh1 : 1 ≤ hh P n (P.r+1) := by simp [hh]
  have := (mem_Icc.mp hk).1
  omega

lemma partial_fraction_continuation (P : Params) (n : ℕ) (d : PartialFractionData P n)
    (t : ℝ) (ht : ∀ k ∈ poleRange P n, t+(k : ℝ) ≠ 0) :
    (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t =
      ∑ s ∈ Icc 1 (P.q-P.r), ∑ k ∈ poleRange P n, (d.coeff s k : ℝ)/(t+(k : ℝ))^s := by
  have hpoles (t : ℝ) (ht : -1 < t) : ∀ k ∈ poleRange P n, t+(k : ℝ) ≠ 0 := by
    intro k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast cs_pole_pos P n k hk
    linarith
  obtain ⟨A, hA⟩ := pf_uniform_model P n
  have hlim : Tendsto (fun t : ℝ => A.eval₂ (algebraMap ℚ ℝ) t /
      (∏ k ∈ poleRange P n, (t+(k : ℝ))^(P.q-P.r))) atTop (𝓝 0) := by
    apply (rational_function_decay P n).1.congr'
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with t ht
    rw [hA t (hpoles t ht), ← pf_real_expansion P n t ht]
  obtain ⟨c, hc⟩ := proper_rational_partial_fraction_variable_expansion
    (poleRange P n) (fun _ => P.q-P.r) A hlim
  have he : ∀ t : ℝ, -1 < t →
      (∑ k ∈ poleRange P n, ∑ j : Fin (P.q-P.r),
        (d.coeff (j.val+1) k : ℝ)/(t+(k : ℝ))^(j.val+1)) =
      ∑ k ∈ poleRange P n, ∑ j : Fin (P.q-P.r), (c k j : ℝ)/(t+(k : ℝ))^(j.val+1) := by
    intro t ht
    rw [Finset.sum_comm,
      cs_sum_orders (P.q-P.r) (fun s => ∑ k ∈ poleRange P n, (d.coeff s k : ℝ)/(t+(k : ℝ))^s),
      ← d.expansion t ht,
      pf_real_expansion P n t ht, ← hA t (hpoles t ht), hc t (hpoles t ht)]
  have huniq := partial_fraction_coeffs_unique (poleRange P n) (P.q-P.r)
    (cs_pole_pos P n) (fun k j => d.coeff (j.val+1) k) c he
  rw [← hA t ht, hc t ht]
  conv_rhs => rw [← cs_sum_orders (P.q-P.r)
    (fun s => ∑ k ∈ poleRange P n, (d.coeff s k : ℝ)/(t+(k : ℝ))^s), Finset.sum_comm]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro j hj
  rw [← congrFun (huniq k hk) j]

lemma cs_hh_mono (P : Params) (n : ℕ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ P.q) : hh P n i ≤ hh P n j := by
  have he := aux_zz_eta_mono P (j-i) i hi (by omega)
  rw [show i+(j-i)=j by omega] at he
  simp only [hh, if_neg (show i ≠ 0 by omega), if_neg (show j ≠ 0 by omega)]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right n he) 1

lemma cs_numerator_zero_factor (P : Params) (n u : ℕ)
    (hu : u ∈ Ico 1 (hh P n 1)) : (X+C (u : ℚ))^P.r ∣ pfNumerator P n := by
  classical
  have hqr := P.q_ge
  have hd (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      X+C (u : ℚ) ∣ C (1/((hh P n j-1).factorial : ℚ))*pfInterval 1 (hh P n j) := by
    have hj' := mem_Icc.mp hj
    have hm := cs_hh_mono P n (i := 1) (j := j) le_rfl hj'.1 (by omega)
    have huj : u ∈ Ico 1 (hh P n j) := mem_Ico.mpr ⟨(mem_Ico.mp hu).1,
      (mem_Ico.mp hu).2.trans_le hm⟩
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun k : ℕ => X+C (k : ℚ)) huj) _
  have hprod := Finset.prod_dvd_prod_of_dvd (fun _j => X+C (u : ℚ))
    (fun j => C (1/((hh P n j-1).factorial : ℚ))*pfInterval 1 (hh P n j)) hd
  simp only [prod_const, Nat.card_Icc, Nat.add_sub_cancel] at hprod
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hprod _) _) _

lemma cs_denominator_nonzero (P : Params) (n u : ℕ)
    (hu : u < hh P n 1) : (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) (-(u : ℝ)) ≠ 0 := by
  classical
  simp only [pfDenominator, eval₂_finsetProd, pfInterval_eval]
  apply prod_ne_zero_iff.mpr
  intro j hj
  apply prod_ne_zero_iff.mpr
  intro k hk
  have hj' := mem_Icc.mp hj
  have hm := cs_hh_mono P n (i := 1) (j := j) le_rfl (by omega) hj'.2
  have huk : u < k := hu.trans_le (hm.trans (mem_Ico.mp hk).1)
  have huk' : (u : ℝ) < k := by exact_mod_cast huk
  linarith

lemma cs_rational_derivative_zero (P : Params) (n u : ℕ)
    (hu : u ∈ Ico 1 (hh P n 1)) :
    iteratedDeriv (P.r-1) (fun t : ℝ =>
      (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t) (-(u : ℝ)) = 0 := by
  have hp (A : ℚ[X]) (x : ℝ) : AnalyticAt ℝ (fun t => A.eval₂ (algebraMap ℚ ℝ) t) x := by
    exact analyticAt_id.aeval_polynomial A
  have hB := cs_denominator_nonzero P n u (mem_Ico.mp hu).2
  let f : ℝ → ℝ := fun t => (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
    (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t
  have hf : AnalyticAt ℝ f (-(u : ℝ)) := (hp _ _).div (hp _ _) hB
  obtain ⟨Q, hQ⟩ := cs_numerator_zero_factor P n u hu
  have horder : (P.r : ℕ∞) ≤ analyticOrderAt f (-(u : ℝ)) := by
    apply (natCast_le_analyticOrderAt hf).mpr
    refine ⟨fun t => Q.eval₂ (algebraMap ℚ ℝ) t /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t, (hp _ _).div (hp _ _) hB, ?_⟩
    apply Filter.Eventually.of_forall
    intro t
    simp only [f, hQ, eval₂_mul, eval₂_pow, eval₂_add, eval₂_X, eval₂_C,
      map_natCast, eval₂_natCast, sub_neg_eq_add, smul_eq_mul]
    ring
  have hr : 0 < P.r := P.r_odd.pos
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp horder (P.r-1) (by omega)

end ZudilinZeta

private lemma cs_hasDerivAt_const_div_pow (c : ℝ) (k s : ℕ) (hs : 0 < s)
    (x : ℝ) (hx : x+k ≠ 0) :
    HasDerivAt (fun t : ℝ => c/(t+(k : ℝ))^s) (-(c*s)/(x+k)^(s+1)) x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have h := (hasDerivAt_const x c).div
    (((hasDerivAt_id x).add_const (k : ℝ)).fun_pow (j+1)) (pow_ne_zero _ hx)
  convert h using 1 <;> try rfl
  simp only [Nat.add_sub_cancel, pow_succ, id_eq, zero_mul, mul_one, zero_sub]
  field_simp [hx]

private lemma cs_iteratedDeriv_const_div_pow (c : ℝ) (k s d : ℕ) (hs : 0 < s)
    {x : ℝ} (hx : x+k ≠ 0) :
    iteratedDeriv d (fun t : ℝ => c/(t+(k : ℝ))^s) x =
      (-1 : ℝ)^d*(s.ascFactorial d : ℝ)*c/(x+k)^(s+d) := by
  induction d generalizing x with
  | zero => simp
  | succ d ih =>
    have he : iteratedDeriv d (fun t : ℝ => c/(t+(k : ℝ))^s) =ᶠ[𝓝 x]
        fun t => (-1 : ℝ)^d*(s.ascFactorial d : ℝ)*c/(t+k)^(s+d) := by
      filter_upwards [(continuousAt_id.add continuousAt_const).tendsto.eventually
        (eventually_ne_nhds hx)] with y hy
      exact ih hy
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hd := cs_hasDerivAt_const_div_pow ((-1 : ℝ)^d*(s.ascFactorial d : ℝ)*c)
      k (s+d) (by omega) x hx
    rw [hd.deriv, Nat.ascFactorial_succ, pow_succ]
    push_cast
    rw [show s+(d+1)=s+d+1 by omega]
    ring

open ZudilinZeta

lemma cs_normalized_derivative (P : Params) (n : ℕ) (d : PartialFractionData P n)
    (x : ℝ) (hx : ∀ k ∈ poleRange P n, x+(k : ℝ) ≠ 0) :
    (1/((P.r-1).factorial : ℝ))*iteratedDeriv (P.r-1) (fun t : ℝ =>
      (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t) x =
      ∑ s ∈ Icc 1 (P.q-P.r), (derivativeWeight P.r s : ℝ)*
        ∑ k ∈ poleRange P n, (d.coeff s k : ℝ)/(x+k)^(s+(P.r-1)) := by
  have he : (fun t : ℝ => (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t) =ᶠ[𝓝 x]
      fun t => ∑ s ∈ Icc 1 (P.q-P.r), ∑ k ∈ poleRange P n, (d.coeff s k : ℝ)/(t+k)^s := by
    filter_upwards [(eventually_all_finset (poleRange P n)).mpr (fun k hk =>
      (continuousAt_id.add continuousAt_const).tendsto.eventually (eventually_ne_nhds (hx k hk)))] with t ht
    exact partial_fraction_continuation P n d t ht
  rw [he.iteratedDeriv_eq]
  have hcd (s k : ℕ) (hk : k ∈ poleRange P n) :
      ContDiffAt ℝ (P.r-1) (fun t : ℝ => (d.coeff s k : ℝ)/(t+k)^s) x :=
    contDiffAt_const.fun_div ((contDiffAt_id.add contDiffAt_const).pow s) (pow_ne_zero _ (hx k hk))
  rw [iteratedDeriv_fun_sum (fun s hs => ContDiffAt.sum (fun k hk => hcd s k hk)), mul_sum]
  apply sum_congr rfl
  intro s hs
  rw [iteratedDeriv_fun_sum (fun k hk => hcd s k hk), mul_sum, mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [cs_iteratedDeriv_const_div_pow _ _ _ _ (mem_Icc.mp hs).1 (hx k hk)]
  rw [(Nat.Odd.sub_odd P.r_odd odd_one).neg_one_pow]
  simp only [derivativeWeight, Rat.cast_div, Rat.cast_natCast, one_mul]
  ring

lemma cs_negative_integer_row_zero (P : Params) (n : ℕ) (d : PartialFractionData P n)
    (u : ℕ) (hu : u ∈ Ico 1 (hh P n 1)) :
    (∑ s ∈ Icc 1 (P.q-P.r), derivativeWeight P.r s *
      ∑ k ∈ poleRange P n, d.coeff s k/((k : ℚ)-u)^(s+(P.r-1))) = 0 := by
  have hqr := P.q_ge
  have hx (k : ℕ) (hk : k ∈ poleRange P n) : -(u : ℝ)+(k : ℝ) ≠ 0 := by
    have hm := cs_hh_mono P n (i := 1) (j := P.r+1) le_rfl (by omega) (by omega)
    have huk : u < k := (mem_Ico.mp hu).2.trans_le (hm.trans (mem_Icc.mp hk).1)
    have huk' : (u : ℝ) < k := by exact_mod_cast huk
    linarith
  have he := cs_normalized_derivative P n d (-(u : ℝ)) hx
  rw [cs_rational_derivative_zero P n u hu, mul_zero] at he
  have hh : ((∑ s ∈ Icc 1 (P.q-P.r), derivativeWeight P.r s *
      ∑ k ∈ poleRange P n, d.coeff s k/((k : ℚ)-u)^(s+(P.r-1)) : ℚ) : ℝ) = 0 := by
    push_cast
    simpa only [sub_eq_add_neg, add_comm] using he.symm
  exact_mod_cast hh

private lemma cs_finite_tail {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    (h k : ℕ) (hh : 1 ≤ h) (hk : h ≤ k) :
    (∑ l ∈ range (k-1), f (l+1)) =
      (∑ l ∈ range (k-h), f (l+1)) + ∑ u ∈ range (h-1), f (k-1-u) := by
  have he : k-1=(k-h)+(h-1) := by omega
  rw [he, sum_range_add]
  congr 1
  rw [← sum_range_reflect (fun i => f (k-h+i+1)) (h-1)]
  apply sum_congr rfl
  intro u hu
  have := mem_range.mp hu
  congr 1
  omega

theorem solution (P : Params) (n : ℕ) (hn : 0 < n) (d : PartialFractionData P n) :
    d.constantCoefficient = d.shiftedConstantCoefficient := by
  have hqr := P.q_ge
  have h1pos : 1 ≤ hh P n 1 := by simp [hh]
  have hk (k : ℕ) (hk : k ∈ poleRange P n) : hh P n 1 ≤ k :=
    (cs_hh_mono P n (i := 1) (j := P.r+1) le_rfl (by omega) (by omega)).trans (mem_Icc.mp hk).1
  have ht (s k : ℕ) (hkm : k ∈ poleRange P n) :
      (∑ l ∈ range (k-1), (1 : ℚ)/((l : ℚ)+1)^(s+(P.r-1))) =
        (∑ l ∈ range (k-hh P n 1), (1 : ℚ)/((l : ℚ)+1)^(s+(P.r-1))) +
        ∑ u ∈ range (hh P n 1-1), (1 : ℚ)/((k : ℚ)-(u+1))^(s+(P.r-1)) := by
    have he := cs_finite_tail (fun l => (1 : ℚ)/(l : ℚ)^(s+(P.r-1))) (hh P n 1) k h1pos (hk k hkm)
    push_cast at he
    rw [he]
    congr 1
    apply sum_congr rfl
    intro u hu
    have hu' := mem_range.mp hu
    have hku : u+1 ≤ k := by have := hk k hkm; omega
    have heq : k-1-u=k-(u+1) := by omega
    rw [heq, Nat.cast_sub hku]
    push_cast
    rfl
  have hz : (∑ s ∈ Icc 1 (P.q-P.r), derivativeWeight P.r s *
      ∑ k ∈ poleRange P n, d.coeff s k *
        ∑ u ∈ range (hh P n 1-1), (1 : ℚ)/((k : ℚ)-(u+1))^(s+(P.r-1))) = 0 := by
    simp_rw [mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := poleRange P n)]
    rw [Finset.sum_comm]
    apply sum_eq_zero
    intro u hu
    have hu' := mem_range.mp hu
    have he := cs_negative_integer_row_zero P n d (u+1) (mem_Ico.mpr ⟨by omega, by omega⟩)
    push_cast at he
    simpa only [mul_one_div, mul_sum] using he
  unfold PartialFractionData.constantCoefficient PartialFractionData.shiftedConstantCoefficient
  congr 1
  calc
    _ = (∑ s ∈ Icc 1 (P.q-P.r), derivativeWeight P.r s *
          ∑ k ∈ poleRange P n, d.coeff s k *
            ∑ l ∈ range (k-hh P n 1), (1 : ℚ)/((l : ℚ)+1)^(s+(P.r-1))) +
        (∑ s ∈ Icc 1 (P.q-P.r), derivativeWeight P.r s *
          ∑ k ∈ poleRange P n, d.coeff s k *
            ∑ u ∈ range (hh P n 1-1), (1 : ℚ)/((k : ℚ)-(u+1))^(s+(P.r-1))) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro s hs
      rw [← mul_add, ← sum_add_distrib]
      apply congrArg (derivativeWeight P.r s * ·)
      apply sum_congr rfl
      intro k hkm
      rw [ht s k hkm, mul_add]
    _ = _ := by rw [hz, add_zero]
