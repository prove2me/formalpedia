-- Prove2me | solution 1 for ZudilinZeta.zudilin_partial_fraction_rough_denominators
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T15:26:54.444364+00:00
-- url     : https://prove2.me/submissions/9656492d-7f23-41f3-923f-c666d08cfa1d

import Definitions.Def_ZudilinZetaPartialFractions

set_option autoImplicit false


/- Source component: VariablePartialFractions -/
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


/- Source component: PartialFractionUniqueness -/
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


/- Source component: DecayFromConvergence -/
/-
The rational-function degree bookkeeping below is reused from mrfancypants,
accepted Prove2Me submission 85b357a0-c802-42df-a9b9-9d6ed8493709,
for the mission series-convergence theorem. The final decay consequence is new.
-/


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


/- Source component: RationalModel -/
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


/- Source component: RationalContinuation -/
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


end ZudilinZeta


/- Source component: ScaledBinomialArithmetic -/
open Polynomial Finset

private lemma bc_factorial_choose (z : ℚ[X]) (m : ℕ) :
    (m.factorial : ℚ[X])*Ring.choose z m = ∏ j ∈ range m, (z-(j : ℚ[X])) := by
  rw [← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose,
    descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer, descPochhammer_eval_eq_prod_range]

private lemma bc_D_dvd (N j : ℕ) (hj : j ∈ Icc 1 N) : j ∣ Nat.lcmUpto N :=
  Finset.dvd_lcm (f := id) hj

private lemma bc_scaled_choose_zero (N m : ℕ) (hm : m ≤ N) :
    ∃ A : ℤ[X], A.map (Int.castRingHom ℚ) = Ring.choose (C (Nat.lcmUpto N : ℚ)*X) m := by
  classical
  cases m with
  | zero => exact ⟨1, by simp⟩
  | succ m =>
    let A : ℤ[X] := C ((Nat.lcmUpto N/(m+1) : ℕ) : ℤ)*X *
      ∏ j ∈ Icc 1 m, (C ((Nat.lcmUpto N/j : ℕ) : ℤ)*X-1)
    refine ⟨A, ?_⟩
    have hdiv (j : ℕ) (hj : j ∈ Icc 1 (m+1)) :
        (j : ℚ)*(Nat.lcmUpto N/j : ℕ) = (Nat.lcmUpto N : ℚ) := by
      have hd := bc_D_dvd N j (mem_Icc.mpr ⟨(mem_Icc.mp hj).1, (mem_Icc.mp hj).2.trans hm⟩)
      exact_mod_cast Nat.mul_div_cancel' hd
    have hlin (j : ℕ) (hj : j ∈ Icc 1 m) :
        C (j : ℚ)*(C ((Nat.lcmUpto N/j : ℕ) : ℚ)*X-1) = C (Nat.lcmUpto N : ℚ)*X-C (j : ℚ) := by
      rw [mul_sub, ← mul_assoc, ← map_mul, hdiv j (mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩), mul_one]
    have hfact : (∏ j ∈ Icc 1 m, C (j : ℚ)) = C (m.factorial : ℚ) := by
      rw [← map_prod, ← Nat.cast_prod]
      congr 1
      exact_mod_cast (show (∏ j ∈ Icc 1 m, j) = m.factorial from by
        simpa only [Ico_add_one_right_eq_Icc] using prod_Ico_id_eq_factorial m)
    have hprod : C (m.factorial : ℚ) *
        (∏ j ∈ Icc 1 m, (C ((Nat.lcmUpto N/j : ℕ) : ℚ)*X-1)) =
        ∏ j ∈ Icc 1 m, (C (Nat.lcmUpto N : ℚ)*X-C (j : ℚ)) := by
      rw [← hfact, ← prod_mul_distrib]
      exact prod_congr rfl hlin
    have hhead : C ((m+1 : ℕ) : ℚ)*C ((Nat.lcmUpto N/(m+1) : ℕ) : ℚ) = C (Nat.lcmUpto N : ℚ) := by
      rw [← map_mul, hdiv (m+1) (mem_Icc.mpr ⟨by omega, le_rfl⟩)]
    have hsplit : (∏ j ∈ range (m+1), (C (Nat.lcmUpto N : ℚ)*X-(j : ℚ[X]))) =
        C (Nat.lcmUpto N : ℚ)*X * ∏ j ∈ Icc 1 m, (C (Nat.lcmUpto N : ℚ)*X-C (j : ℚ)) := by
      have he := prod_range_mul_prod_Ico (fun j => C (Nat.lcmUpto N : ℚ)*X-(j : ℚ[X]))
        (m := 1) (n := m+1) (by omega)
      simpa only [prod_range_one, Nat.cast_zero, sub_zero, Ico_add_one_right_eq_Icc,
        C_eq_natCast] using he.symm
    have hfacne : (m+1).factorial ≠ 0 := Nat.factorial_ne_zero _
    apply mul_left_cancel₀ (a := ((m+1).factorial : ℚ[X])) (by exact_mod_cast hfacne)
    rw [bc_factorial_choose, hsplit]
    simp only [A, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_one, Int.coe_castRingHom, Int.cast_natCast]
    rw [Nat.factorial_succ, Nat.cast_mul, ← C_eq_natCast (m+1), ← C_eq_natCast (m.factorial)]
    calc
      _ = (C ((m+1 : ℕ) : ℚ)*C ((Nat.lcmUpto N/(m+1) : ℕ) : ℚ)) * X *
          (C (m.factorial : ℚ)*(∏ j ∈ Icc 1 m, (C ((Nat.lcmUpto N/j : ℕ) : ℚ)*X-1))) := by ring
      _ = _ := by rw [hhead, hprod]

lemma scaled_binomial_has_integer_coefficients (N m : ℕ) (hm : m ≤ N) (a : ℤ) :
    ∃ A : ℤ[X], A.map (Int.castRingHom ℚ) = Ring.choose (C (Nat.lcmUpto N : ℚ)*X+C (a : ℚ)) m := by
  classical
  have hchoose (j : ℕ) :
      ∃ A : ℤ[X], j ≤ m → A.map (Int.castRingHom ℚ) = Ring.choose (C (Nat.lcmUpto N : ℚ)*X) j := by
    by_cases hj : j ≤ m
    · obtain ⟨A, hA⟩ := bc_scaled_choose_zero N j (hj.trans hm)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose A hA using hchoose
  let F : ℤ[X] := ∑ ij ∈ antidiagonal m, A ij.1 * C (Ring.choose a ij.2)
  have hc (j : ℕ) : C ((Ring.choose a j : ℤ) : ℚ) = Ring.choose (C (a : ℚ)) j := by
    simpa using Ring.map_choose ((C : ℚ →+* ℚ[X]).comp (Int.castRingHom ℚ)) a j
  refine ⟨F, ?_⟩
  rw [Ring.add_choose_eq m (Commute.all _ _)]
  simp only [F, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom]
  apply sum_congr rfl
  intro ij hij
  rw [hA ij.1 (HasAntidiagonal.antidiagonal.fst_le hij), hc]

lemma binomial_coefficient_lcm_integral (N m j : ℕ) (hm : m ≤ N) (a : ℤ) :
    ∃ z : ℤ, (Nat.lcmUpto N : ℚ)^j*(Ring.choose (X+C (a : ℚ) : ℚ[X]) m).coeff j = (z : ℚ) := by
  obtain ⟨A, hA⟩ := scaled_binomial_has_integer_coefficients N m hm a
  have he : (Ring.choose (X+C (a : ℚ) : ℚ[X]) m).comp (C (Nat.lcmUpto N : ℚ)*X) =
      Ring.choose (C (Nat.lcmUpto N : ℚ)*X+C (a : ℚ)) m := by
    have h :=
      Ring.map_choose (Polynomial.compRingHom (C (Nat.lcmUpto N : ℚ)*X : ℚ[X])) (X+C (a : ℚ) : ℚ[X]) m
    change (Ring.choose (X+C (a : ℚ) : ℚ[X]) m).comp (C (Nat.lcmUpto N : ℚ)*X) =
      Ring.choose ((X+C (a : ℚ) : ℚ[X]).comp (C (Nat.lcmUpto N : ℚ)*X)) m at h
    rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at h
    exact h
  refine ⟨A.coeff j, ?_⟩
  have h := congrArg (fun f : ℚ[X] => f.coeff j) hA
  rw [coeff_map, ← he, comp_C_mul_X_coeff] at h
  simpa only [Int.coe_castRingHom, mul_comm] using h.symm

private lemma bc_normalized_polynomial_derivative (A : ℚ[X]) (j : ℕ) :
    (1/(j.factorial : ℝ))*iteratedDeriv j (fun t => A.eval₂ (algebraMap ℚ ℝ) t) 0 =
      (A.coeff j : ℝ) := by
  have hi (j : ℕ) : ∀ B : ℝ[X], iteratedDeriv j (fun t => B.eval t) =
      fun t => (Polynomial.derivative^[j] B).eval t := by
    induction j with
    | zero => intro B; simp
    | succ j ih =>
      intro B
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [Polynomial.deriv, Function.iterate_succ_apply']
  have he : (fun t => A.eval₂ (algebraMap ℚ ℝ) t) =
      fun t => (A.map (algebraMap ℚ ℝ)).eval t := by
    funext t
    rw [eval_map]
  rw [he, hi]
  dsimp only
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  simp only [Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul, coeff_map]
  have hne : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  simp only [one_div, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rfl

lemma binomial_derivative_lcm_integral (N m j : ℕ) (hm : m ≤ N) (a k : ℤ) :
    ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^j/(j.factorial : ℝ) *
      iteratedDeriv j (fun t : ℝ => Ring.choose (t+(a : ℝ)) m) (k : ℝ) = (z : ℝ) := by
  have hzero (b : ℤ) : ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^j/(j.factorial : ℝ) *
      iteratedDeriv j (fun t : ℝ => Ring.choose (t+(b : ℝ)) m) 0 = (z : ℝ) := by
    let A : ℚ[X] := Ring.choose (X+C (b : ℚ) : ℚ[X]) m
    have he : (fun t => A.eval₂ (algebraMap ℚ ℝ) t) =
        fun t : ℝ => Ring.choose (t+(b : ℝ)) m := by
      funext t
      have h := Ring.map_choose (Polynomial.eval₂RingHom (algebraMap ℚ ℝ) t)
        (X+C (b : ℚ) : ℚ[X]) m
      change A.eval₂ (algebraMap ℚ ℝ) t =
        Ring.choose ((X+C (b : ℚ) : ℚ[X]).eval₂ (algebraMap ℚ ℝ) t) m at h
      rw [eval₂_add, eval₂_X, eval₂_C] at h
      simpa only [map_intCast] using h
    have hd := bc_normalized_polynomial_derivative A j
    rw [he] at hd
    obtain ⟨z, hz⟩ := binomial_coefficient_lcm_integral N m j hm b
    refine ⟨z, ?_⟩
    calc
      _ = (Nat.lcmUpto N : ℝ)^j*(A.coeff j : ℝ) := by rw [← hd]; ring
      _ = (z : ℝ) := by exact_mod_cast hz
  have he : (fun t : ℝ => Ring.choose (t+((a+k : ℤ) : ℝ)) m) =
      fun t : ℝ => (fun u : ℝ => Ring.choose (u+(a : ℝ)) m) (t+(k : ℝ)) := by
    funext t
    simp only [Int.cast_add]
    congr 1
    ring
  obtain ⟨z, hz⟩ := hzero (a+k)
  rw [he, iteratedDeriv_comp_add_const j (fun t : ℝ => Ring.choose (t+(a : ℝ)) m) (k : ℝ)] at hz
  dsimp only at hz
  rw [zero_add] at hz
  exact ⟨z, hz⟩


/- Source component: PolynomialBrickArithmetic -/
open Finset Polynomial

lemma polynomial_brick_eq_choose (m : ℕ) (z : ℝ) :
    (∏ i ∈ range m, (z+i))/(m.factorial : ℝ) = Ring.choose (z+m-1) m := by
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  apply (div_eq_iff hf).mpr
  rw [mul_comm, ← Ring.multichoose_eq, ← nsmul_eq_mul,
    Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval]
  clear hf
  induction m with
  | zero => simp
  | succ m ih => rw [prod_range_succ, ascPochhammer_succ_eval, ih]

lemma polynomial_brick_arithmetic (N a m : ℕ) (hm : m ≤ N) (k : ℤ) :
    AnalyticAt ℝ (fun t : ℝ => (∏ i ∈ range m, (t+(a+i : ℕ)))/(m.factorial : ℝ)) (k : ℝ) ∧
      ∀ j : ℕ, ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^j/(j.factorial : ℝ)*
        iteratedDeriv j (fun t : ℝ =>
          (∏ i ∈ range m, (t+(a+i : ℕ)))/(m.factorial : ℝ)) (k : ℝ) = (z : ℝ) := by
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  refine ⟨((range m).analyticAt_fun_prod (fun i hi =>
    analyticAt_id.add analyticAt_const)).div analyticAt_const hf, ?_⟩
  intro j
  have he : (fun t : ℝ => (∏ i ∈ range m, (t+(a+i : ℕ)))/(m.factorial : ℝ)) =
      fun t : ℝ => Ring.choose (t+((a : ℤ)+m-1 : ℤ)) m := by
    funext t
    simp only [Nat.cast_add, ← add_assoc]
    rw [polynomial_brick_eq_choose]
    congr 1
    push_cast
    ring
  rw [he]
  exact binomial_derivative_lcm_integral N m j hm ((a : ℤ)+m-1) k


/- Source component: IntegralDerivatives -/
open Finset

lemma integral_normalized_derivative_mul (L j : ℕ) (f g : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x)
    (hfi : ∀ i ≤ j, ∃ a : ℤ, (L : ℝ)^i/(i.factorial : ℝ)*iteratedDeriv i f x = (a : ℝ))
    (hgi : ∀ i ≤ j, ∃ a : ℤ, (L : ℝ)^i/(i.factorial : ℝ)*iteratedDeriv i g x = (a : ℝ)) :
    ∃ a : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*
      iteratedDeriv j (fun t => f t*g t) x = (a : ℝ) := by
  classical
  have hterm (i : ℕ) (hi : i ∈ range (j+1)) :
      ∃ a : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*
        ((j.choose i : ℝ)*iteratedDeriv i f x*iteratedDeriv (j-i) g x) = (a : ℝ) := by
    have hij : i ≤ j := by have := mem_range.mp hi; omega
    obtain ⟨a, ha⟩ := hfi i hij
    obtain ⟨b, hb⟩ := hgi (j-i) (Nat.sub_le _ _)
    refine ⟨a*b, ?_⟩
    have hc : (j.choose i : ℝ)*(i.factorial : ℝ)*((j-i).factorial : ℝ) = (j.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hij
    have hi0 : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hji0 : ((j-i).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-i)
    have he : (L : ℝ)^j = (L : ℝ)^i*(L : ℝ)^(j-i) := by
      rw [← pow_add, Nat.add_sub_of_le hij]
    rw [Int.cast_mul, ← ha, ← hb, he]
    field_simp
    linear_combination (L : ℝ)^i*(L : ℝ)^(j-i)*
      iteratedDeriv i f x*iteratedDeriv (j-i) g x*hc
  have hterm' (i : ℕ) : ∃ a : ℤ, i ∈ range (j+1) →
      (L : ℝ)^j/(j.factorial : ℝ)*
        ((j.choose i : ℝ)*iteratedDeriv i f x*iteratedDeriv (j-i) g x) = (a : ℝ) := by
    by_cases hi : i ∈ range (j+1)
    · obtain ⟨a, ha⟩ := hterm i hi
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose a ha using hterm'
  refine ⟨∑ i ∈ range (j+1), a i, ?_⟩
  rw [iteratedDeriv_fun_mul hf hg, mul_sum]
  push_cast
  exact sum_congr rfl (fun i hi => ha i hi)

lemma integral_normalized_derivative_const (L j : ℕ) (a : ℤ) (x : ℝ) :
    ∃ z : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*iteratedDeriv j (fun _ : ℝ => (a : ℝ)) x = (z : ℝ) := by
  cases j with
  | zero => exact ⟨a, by simp⟩
  | succ j => exact ⟨0, by simp [iteratedDeriv_const]⟩

lemma integral_normalized_derivative_const_mul (L j : ℕ) (a : ℤ) (f : ℝ → ℝ) (x : ℝ)
    (hf : ∃ z : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*iteratedDeriv j f x = (z : ℝ)) :
    ∃ z : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*
      iteratedDeriv j (fun t => (a : ℝ)*f t) x = (z : ℝ) := by
  obtain ⟨z, hz⟩ := hf
  refine ⟨a*z, ?_⟩
  rw [iteratedDeriv_const_mul_field, Int.cast_mul, ← hz]
  ring

lemma integral_normalized_derivative_sum {ι : Type*} (s : Finset ι)
    (L j : ℕ) (f : ι → ℝ → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ j (f i) x)
    (hfi : ∀ i ∈ s, ∃ a : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*iteratedDeriv j (f i) x = (a : ℝ)) :
    ∃ a : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*
      iteratedDeriv j (fun t => ∑ i ∈ s, f i t) x = (a : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integral_normalized_derivative_const L j 0 x
  | @insert i s hi ih =>
    obtain ⟨a, ha⟩ := hfi i (mem_insert_self _ _)
    obtain ⟨b, hb⟩ := ih (fun l hl => hf l (mem_insert_of_mem hl))
      (fun l hl => hfi l (mem_insert_of_mem hl))
    refine ⟨a+b, ?_⟩
    simp only [sum_insert hi]
    rw [iteratedDeriv_fun_add (hf i (mem_insert_self _ _))
      (ContDiffAt.sum (fun l hl => hf l (mem_insert_of_mem hl))), mul_add, ha, hb, Int.cast_add]

lemma integral_normalized_derivative_prod {ι : Type*} (s : Finset ι)
    (L : ℕ) (f : ι → ℝ → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) x)
    (hfi : ∀ i ∈ s, ∀ j : ℕ, ∃ a : ℤ,
      (L : ℝ)^j/(j.factorial : ℝ)*iteratedDeriv j (f i) x = (a : ℝ)) :
    ∀ j : ℕ, ∃ a : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*
      iteratedDeriv j (fun t => ∏ i ∈ s, f i t) x = (a : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro j; simpa using integral_normalized_derivative_const L j 1 x
  | @insert i s hi ih =>
    intro j
    simp only [prod_insert hi]
    have hfs (l : ι) (hl : l ∈ s) : AnalyticAt ℝ (f l) x := hf l (mem_insert_of_mem hl)
    apply integral_normalized_derivative_mul L j (f i) _ x
      (hf i (mem_insert_self _ _)).contDiffAt (s.analyticAt_fun_prod hfs).contDiffAt
    · intro l hl
      exact hfi i (mem_insert_self _ _) l
    · intro l hl
      exact ih hfs (fun a ha => hfi a (mem_insert_of_mem ha)) l

lemma integral_analytic_mul (L : ℕ) (f g : ℝ → ℝ) (x : ℝ)
    (hf : AnalyticAt ℝ f x ∧ ∀ j : ℕ, ∃ a : ℤ,
      (L : ℝ)^j/(j.factorial : ℝ)*iteratedDeriv j f x = (a : ℝ))
    (hg : AnalyticAt ℝ g x ∧ ∀ j : ℕ, ∃ a : ℤ,
      (L : ℝ)^j/(j.factorial : ℝ)*iteratedDeriv j g x = (a : ℝ)) :
    AnalyticAt ℝ (fun t => f t*g t) x ∧ ∀ j : ℕ, ∃ a : ℤ,
      (L : ℝ)^j/(j.factorial : ℝ)*iteratedDeriv j (fun t => f t*g t) x = (a : ℝ) :=
  ⟨hf.1.mul hg.1, fun j => integral_normalized_derivative_mul L j f g x
    hf.1.contDiffAt hg.1.contDiffAt (fun i hi => hf.2 i) (fun i hi => hg.2 i)⟩

lemma integer_affine_derivative (L j : ℕ) (a b k : ℤ) :
    ∃ z : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*
      iteratedDeriv j (fun t : ℝ => (a : ℝ)+(b : ℝ)*t) (k : ℝ) = (z : ℝ) := by
  cases j with
  | zero => exact ⟨a+b*k, by simp⟩
  | succ j =>
    have he : deriv (fun t : ℝ => (a : ℝ)+(b : ℝ)*t) = fun _ => (b : ℝ) := by
      funext t
      simp
    rw [iteratedDeriv_succ', he]
    cases j with
    | zero => exact ⟨(L : ℤ)*b, by simp⟩
    | succ j => exact ⟨0, by simp [iteratedDeriv_const]⟩


/- Source component: InverseBrickArithmetic -/
open Finset Polynomial

lemma ib_prod_differences (m i : ℕ) (hi : i ≤ m) :
    (∏ j ∈ (range (m+1)).erase i, ((j : ℚ)-i)) =
      (-1 : ℚ)^i*(i.factorial : ℚ)*((m-i).factorial : ℚ) := by
  classical
  let f : ℕ → ℚ := fun j => if j=i then 1 else (j : ℚ)-i
  have hleft : (∏ j ∈ range i, f j) = (-1 : ℚ)^i*(i.factorial : ℚ) := by
    rw [← prod_range_reflect f i]
    have he (j : ℕ) (hj : j ∈ range i) : f (i-1-j) = -(j+1 : ℚ) := by
      have hj' := mem_range.mp hj
      have hne : i-1-j ≠ i := by omega
      dsimp [f]
      rw [if_neg hne]
      have ht : i-1-j+(j+1)=i := by omega
      have ht' : ((i-1-j : ℕ) : ℚ)+(j+1)=i := by exact_mod_cast ht
      linarith
    rw [prod_congr rfl he]
    rw [Finset.prod_neg, card_range]
    congr 1
    exact_mod_cast prod_range_add_one_eq_factorial i
  have hright : (∏ j ∈ range (m-i+1), f (i+j)) = ((m-i).factorial : ℚ) := by
    rw [prod_range_succ']
    have he (j : ℕ) (hj : j ∈ range (m-i)) : f (i+(j+1)) = (j+1 : ℚ) := by
      have hne : i+(j+1) ≠ i := by omega
      simp only [f, if_neg hne, Nat.cast_add, Nat.cast_one]
      ring
    rw [prod_congr rfl he]
    simp only [f, Nat.add_zero, if_pos rfl, mul_one]
    exact_mod_cast prod_range_add_one_eq_factorial (m-i)
  have he : (∏ j ∈ (range (m+1)).erase i, ((j : ℚ)-i)) = ∏ j ∈ range (m+1), f j := by
    rw [← prod_erase (range (m+1)) (a := i) (show f i = 1 by simp [f])]
    apply prod_congr rfl
    intro j hj
    exact (if_neg (mem_erase.mp hj).1).symm
  rw [he, show m+1=i+(m-i+1) by omega, prod_range_add, hleft, hright]

lemma ib_integer_residues (m : ℕ) :
    ∃ b : ℕ → ℤ, ∀ t : ℝ, (∀ j ∈ range (m+1), t+j ≠ 0) →
      (m.factorial : ℝ)/(∏ j ∈ range (m+1), (t+j)) =
        ∑ j ∈ range (m+1), (b j : ℝ)/(t+j) := by
  classical
  let b : ℕ → ℤ := fun j => (-1)^j*(m.choose j : ℤ)
  have hweight (j : ℕ) (hj : j ∈ range (m+1)) :
      (m.factorial : ℝ)*Lagrange.nodalWeight (range (m+1)) (fun j : ℕ => -(j : ℝ)) j = (b j : ℝ) := by
    have hj' : j ≤ m := by have := mem_range.mp hj; omega
    have hp : (∏ l ∈ (range (m+1)).erase j, ((l : ℝ)-j)) =
        (-1 : ℝ)^j*(j.factorial : ℝ)*((m-j).factorial : ℝ) := by
      exact_mod_cast ib_prod_differences m j hj'
    have hc : (m.choose j : ℝ)*(j.factorial : ℝ)*((m-j).factorial : ℝ) = (m.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
    have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hmj0 : ((m-j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m-j)
    have hs : ((-1 : ℝ)^j)^2=1 := by rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
    simp only [Lagrange.nodalWeight, neg_sub_neg, prod_inv_distrib]
    rw [hp]
    simp only [b, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    field_simp
    linear_combination -hc - (m.choose j : ℝ)*(j.factorial : ℝ)*((m-j).factorial : ℝ)*hs
  refine ⟨b, fun t ht => ?_⟩
  have hinj : Set.InjOn (fun j : ℕ => -(j : ℝ)) (range (m+1)) := by
    intro j hj l hl h
    exact_mod_cast neg_injective h
  have hnon : (range (m+1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  have hn (j : ℕ) (hj : j ∈ range (m+1)) : t ≠ -(j : ℝ) := by
    exact fun h => ht j hj (by rw [h]; ring)
  have he := Lagrange.eval_interpolate_not_at_node (s := range (m+1))
    (v := fun j : ℕ => -(j : ℝ)) (1 : ℕ → ℝ) hn
  rw [Lagrange.interpolate_one hinj hnon, eval_one, Lagrange.eval_nodal] at he
  simp only [sub_neg_eq_add, Pi.one_apply, mul_one] at he
  have hp0 : (∏ j ∈ range (m+1), (t+j)) ≠ 0 := prod_ne_zero_iff.mpr ht
  have hs : (∑ j ∈ range (m+1), Lagrange.nodalWeight (range (m+1))
      (fun j : ℕ => -(j : ℝ)) j*(t+j)⁻¹) = (∏ j ∈ range (m+1), (t+j))⁻¹ := by
    apply (mul_left_cancel₀ hp0)
    rw [← he, mul_inv_cancel₀ hp0]
  calc
    _ = (m.factorial : ℝ)*(∑ j ∈ range (m+1), Lagrange.nodalWeight (range (m+1))
        (fun j : ℕ => -(j : ℝ)) j*(t+j)⁻¹) := by rw [hs, div_eq_mul_inv]
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro j hj; rw [← mul_assoc, hweight j hj, div_eq_mul_inv]


/- Source component: CanceledReciprocalArithmetic -/
open Finset Filter
open scoped Topology

lemma canceled_reciprocal_integral (L j : ℕ) (k l : ℤ) (hkl : l ≠ k)
    (hd : l-k ∣ (L : ℤ)) :
    ∃ z : ℤ, (L : ℝ)^j/(j.factorial : ℝ)*
      iteratedDeriv j (fun t : ℝ => (t+k)/(t+l)) (-(k : ℝ)) = (z : ℝ) := by
  have hlk : (l : ℝ)-k ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hkl
  have hx : -(k : ℝ)+l ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using hlk
  cases j with
  | zero => exact ⟨0, by simp⟩
  | succ j =>
    have he : (fun t : ℝ => (t+k)/(t+l)) =ᶠ[𝓝 (-(k : ℝ))]
        fun t => 1+((k : ℝ)-l)*(t+l)⁻¹ := by
      filter_upwards [(continuousAt_id.add continuousAt_const).tendsto.eventually
        (eventually_ne_nhds hx)] with t ht
      change t+(l : ℝ) ≠ 0 at ht
      field_simp [ht]
      ring
    rw [he.iteratedDeriv_eq, iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_add_const (j+1) (fun t : ℝ => t⁻¹) (l : ℝ),
      iteratedDeriv_eq_iterate]
    dsimp only
    rw [iter_deriv_inv]
    obtain ⟨q, hq⟩ := hd
    have hq' : (L : ℝ)=((l : ℝ)-k)*(q : ℝ) := by exact_mod_cast hq
    have hf : ((j+1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j+1)
    refine ⟨(-1)^(j+2)*q^(j+1), ?_⟩
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [hq', mul_pow]
    have heq : -(k : ℝ)+l=(l : ℝ)-k := by ring
    rw [heq]
    rw [show (-1-((j+1 : ℕ) : ℤ)) = -((j+2 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
    field_simp
    ring

lemma regularized_simple_fraction (N : ℕ) (k l : ℤ)
    (hbound : (l-k).natAbs ≤ N) :
    AnalyticAt ℝ (fun t : ℝ => if l=k then 1 else (t+k)/(t+l)) (-(k : ℝ)) ∧
      ∀ j : ℕ, ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^j/(j.factorial : ℝ)*
        iteratedDeriv j (fun t : ℝ => if l=k then 1 else (t+k)/(t+l)) (-(k : ℝ)) = (z : ℝ) := by
  by_cases hkl : l=k
  · simp only [if_pos hkl]
    refine ⟨analyticAt_const, fun j => ?_⟩
    simpa only [Int.cast_one] using integral_normalized_derivative_const (Nat.lcmUpto N) j 1 (-(k : ℝ))
  · simp only [if_neg hkl]
    have hx : -(k : ℝ)+(l : ℝ) ≠ 0 := by
      have h : (l : ℝ)-k ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hkl
      simpa only [sub_eq_add_neg, add_comm] using h
    have hd : l-k ∣ (Nat.lcmUpto N : ℤ) := by
      apply Int.dvd_natCast.mpr
      apply Finset.dvd_lcm (f := id)
      exact mem_Icc.mpr ⟨Int.natAbs_pos.mpr (sub_ne_zero.mpr hkl), hbound⟩
    exact ⟨(analyticAt_id.add analyticAt_const).div (analyticAt_id.add analyticAt_const) hx,
      fun j => canceled_reciprocal_integral (Nat.lcmUpto N) j k l hkl hd⟩


/- Source component: RegularizedInverseBrick -/
open Finset

lemma inverse_brick_regularized (N a m : ℕ) (k : ℤ)
    (hbound : ∀ i ∈ range (m+1), ((a+i : ℕ) - k : ℤ).natAbs ≤ N) :
    ∃ f : ℝ → ℝ, AnalyticAt ℝ f (-(k : ℝ)) ∧
      (∀ t : ℝ, (∀ i ∈ range (m+1), t+(a+i : ℕ) ≠ 0) →
        f t = (t+k)*(m.factorial : ℝ)/(∏ i ∈ range (m+1), (t+(a+i : ℕ)))) ∧
      ∀ j : ℕ, ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^j/(j.factorial : ℝ)*
        iteratedDeriv j f (-(k : ℝ)) = (z : ℝ) := by
  classical
  obtain ⟨b, hb⟩ := ib_integer_residues m
  let g : ℕ → ℝ → ℝ := fun i t =>
    if ((a+i : ℕ) : ℤ)=k then 1 else (t+k)/(t+(a+i : ℕ))
  let f : ℝ → ℝ := fun t => ∑ i ∈ range (m+1), (b i : ℝ)*g i t
  have hg (i : ℕ) (hi : i ∈ range (m+1)) :
      AnalyticAt ℝ (g i) (-(k : ℝ)) ∧
        ∀ j : ℕ, ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^j/(j.factorial : ℝ)*
          iteratedDeriv j (g i) (-(k : ℝ)) = (z : ℝ) := by
    simpa only [g, Int.cast_natCast] using
      regularized_simple_fraction N k ((a+i : ℕ) : ℤ) (hbound i hi)
  refine ⟨f, (range (m+1)).analyticAt_fun_sum (fun i hi => analyticAt_const.mul (hg i hi).1), ?_, ?_⟩
  · intro t ht
    have he := hb (t+a) (fun i hi => by simpa only [Nat.cast_add, add_assoc] using ht i hi)
    have he' : (m.factorial : ℝ)/(∏ i ∈ range (m+1), (t+(a+i : ℕ))) =
        ∑ i ∈ range (m+1), (b i : ℝ)/(t+(a+i : ℕ)) := by
      simpa only [Nat.cast_add, add_assoc] using he
    rw [mul_div_assoc, he', mul_sum]
    apply sum_congr rfl
    intro i hi
    dsimp only [g]
    by_cases h : ((a+i : ℕ) : ℤ)=k
    · rw [if_pos h]
      have h' : (a+i : ℕ) = (k : ℝ) := by exact_mod_cast h
      have ht' := ht i hi
      rw [h'] at ht' ⊢
      field_simp [ht']
    · rw [if_neg h]
      ring
  · intro j
    apply integral_normalized_derivative_sum (range (m+1)) (Nat.lcmUpto N) j
      (fun i t => (b i : ℝ)*g i t) (-(k : ℝ))
    · intro i hi
      exact (analyticAt_const.mul (hg i hi).1).contDiffAt
    · intro i hi
      exact integral_normalized_derivative_const_mul _ j (b i) (g i) _ ((hg i hi).2 j)


/- Source component: PartialFractionCoefficientDerivative -/
open Finset Filter
open scoped Topology

lemma partial_fraction_coefficient_derivative (K : Finset ℕ) (S : ℕ)
    (c : ℕ → ℕ → ℝ) (k : ℕ) (hk : k ∈ K) (F : ℝ → ℝ)
    (hF : AnalyticAt ℝ F (-(k : ℝ)))
    (hFe : ∀ t : ℝ, (∀ l ∈ K, t+(l : ℝ) ≠ 0) →
      F t = (t+k)^S*(∑ s ∈ Icc 1 S, ∑ l ∈ K, c s l/(t+l)^s))
    (s : ℕ) (hs : s ∈ Icc 1 S) :
    (1/((S-s).factorial : ℝ))*iteratedDeriv (S-s) F (-(k : ℝ)) = c s k := by
  classical
  let A : ℝ → ℝ := fun t => ∑ u ∈ Icc 1 S, c u k*(t+k)^(S-u)
  let B : ℝ → ℝ := fun t => ∑ u ∈ Icc 1 S, ∑ l ∈ K.erase k, c u l/(t+l)^u
  let G : ℝ → ℝ := fun t => A t+(t+k)^S*B t
  have hpole (l : ℕ) (hl : l ∈ K.erase k) : -(k : ℝ)+l ≠ 0 := by
    have hlk := (mem_erase.mp hl).1
    have h : (l : ℝ) ≠ k := by exact_mod_cast hlk
    exact fun he => h (by linarith)
  have hA : AnalyticAt ℝ A (-(k : ℝ)) :=
    (Icc 1 S).analyticAt_fun_sum (fun u hu => analyticAt_const.mul
      ((analyticAt_id.add analyticAt_const).pow (S-u)))
  have hB : AnalyticAt ℝ B (-(k : ℝ)) :=
    (Icc 1 S).analyticAt_fun_sum (fun u hu => (K.erase k).analyticAt_fun_sum
      (fun l hl => analyticAt_const.div ((analyticAt_id.add analyticAt_const).pow u)
        (pow_ne_zero _ (hpole l hl))))
  have hC : AnalyticAt ℝ (fun t : ℝ => (t+k)^S*B t) (-(k : ℝ)) :=
    ((analyticAt_id.add analyticAt_const).pow S).mul hB
  have hG : AnalyticAt ℝ G (-(k : ℝ)) := hA.add hC
  have he (t : ℝ) (ht : ∀ l ∈ K, t+(l : ℝ) ≠ 0) : F t = G t := by
    rw [hFe t ht]
    have hpow (u : ℕ) (hu : u ∈ Icc 1 S) :
        (t+k)^S*(c u k/(t+k)^u) = c u k*(t+k)^(S-u) := by
      have hle := (mem_Icc.mp hu).2
      conv_lhs => rw [show S=u+(S-u) by omega, pow_add]
      field_simp [ht k hk]
    simp only [G, A, B, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    rw [← add_sum_erase K (fun l => (t+k)^S*(c u l/(t+l)^u)) hk, hpow u hu]
  have hpunct : F =ᶠ[𝓝[≠] (-(k : ℝ))] G := by
    have hother : ∀ᶠ t in 𝓝 (-(k : ℝ)), ∀ l ∈ K.erase k, t+(l : ℝ) ≠ 0 :=
      (eventually_all_finset (K.erase k)).mpr (fun l hl =>
        (continuousAt_id.add continuousAt_const).tendsto.eventually (eventually_ne_nhds (hpole l hl)))
    filter_upwards [hother.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htk
    apply he t
    intro l hl
    by_cases hlk : l=k
    · subst l
      have htne : t ≠ -(k : ℝ) := htk
      exact fun hz => htne (by linarith)
    · exact ht l (mem_erase.mpr ⟨hlk, hl⟩)
  have hlocal : F =ᶠ[𝓝 (-(k : ℝ))] G :=
    (hF.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hG.continuousAt).mp hpunct
  have hz : iteratedDeriv (S-s) (fun t : ℝ => (t+k)^S*B t) (-(k : ℝ)) = 0 := by
    have hord : (S : ℕ∞) ≤ analyticOrderAt (fun t : ℝ => (t+k)^S*B t) (-(k : ℝ)) := by
      apply (natCast_le_analyticOrderAt hC).mpr
      refine ⟨B, hB, Filter.Eventually.of_forall (fun t => ?_)⟩
      simp only [sub_neg_eq_add, smul_eq_mul]
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hC).mp hord (S-s)
    have := mem_Icc.mp hs
    omega
  rw [hlocal.iteratedDeriv_eq]
  change (1/((S-s).factorial : ℝ))*iteratedDeriv (S-s)
    (fun t => A t+(t+k)^S*B t) (-(k : ℝ)) = _
  rw [iteratedDeriv_fun_add hA.contDiffAt hC.contDiffAt, hz, add_zero]
  have hmon' (u : ℕ) (hu : u ∈ Icc 1 S) :
      iteratedDeriv (S-s) (fun t : ℝ => c u k*(t+k)^(S-u)) (-(k : ℝ)) =
        if u=s then c s k*((S-s).factorial : ℝ) else 0 := by
    rw [iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_add_const (S-s) (fun t : ℝ => t^(S-u)) (k : ℝ)]
    simp only [neg_add_cancel, iteratedDeriv_fun_pow_zero]
    by_cases he : u=s
    · subst u; simp
    · have hne : S-s ≠ S-u := by have := mem_Icc.mp hu; have := mem_Icc.mp hs; omega
      simp only [if_neg he, if_neg hne, Nat.cast_zero, mul_zero]
  have hAe : iteratedDeriv (S-s) A (-(k : ℝ)) = c s k*((S-s).factorial : ℝ) := by
    rw [show A=(fun t => ∑ u ∈ Icc 1 S, c u k*(t+k)^(S-u)) from rfl,
      iteratedDeriv_fun_sum (fun u hu =>
        (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).pow (S-u))).contDiffAt)]
    rw [sum_congr rfl hmon']
    simp only [sum_ite_eq', if_pos hs]
  rw [hAe]
  have hf : ((S-s).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (S-s)
  field_simp


/- Source component: RoughCoefficientDenominators -/
open Polynomial Finset

namespace ZudilinZeta

lemma rough_factor_arithmetic (P : Params) (n : ℕ) (k : ℕ) (hk : k ∈ poleRange P n) :
    ∃ F : ℝ → ℝ, AnalyticAt ℝ F (-(k : ℝ)) ∧
      (∀ t : ℝ, (∀ l ∈ poleRange P n, t+(l : ℝ) ≠ 0) →
        F t = (t+k)^(P.q-P.r)*(pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
          (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t) ∧
      ∀ j : ℕ, ∃ z : ℤ,
        (Nat.lcmUpto (max (P.eta P.r) (P.eta 0-2*P.eta (P.r+1))*n) : ℝ)^j/
          (j.factorial : ℝ)*iteratedDeriv j F (-(k : ℝ)) = (z : ℝ) := by
  classical
  let N := max (P.eta P.r) (P.eta 0-2*P.eta (P.r+1))*n
  let J := Icc 1 P.r
  let T := Icc (P.r+1) P.q
  let A : ℕ → ℝ → ℝ := fun j t =>
    (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t / ((hh P n j-1).factorial : ℝ)
  let B : ℕ → ℝ → ℝ := fun j t =>
    (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t /
      ((hh P n j-1).factorial : ℝ)
  have hqr := P.q_ge
  have hjq (j : ℕ) (hj : j ∈ J) : j ∈ Icc 1 P.q :=
    mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
  have htq (j : ℕ) (hj : j ∈ T) : j ∈ Icc 1 P.q :=
    mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
  have hdeg (j : ℕ) (hj : j ∈ J) : hh P n j-1 ≤ N := by
    have hj' := mem_Icc.mp hj
    have hmono := aux_zz_eta_mono P (P.r-j) j (mem_Icc.mp hj).1 (by omega)
    rw [show j+(P.r-j)=P.r by have := (mem_Icc.mp hj).2; omega] at hmono
    have hhj : hh P n j-1=P.eta j*n := by simp [hh, show j ≠ 0 by have := (mem_Icc.mp hj).1; omega]
    rw [hhj]
    exact Nat.mul_le_mul_right n (hmono.trans (le_max_left _ _))
  have hAeq (j : ℕ) (hj : j ∈ J) : A j = fun t : ℝ =>
      (∏ i ∈ range (hh P n j-1), (t+(1+i : ℕ)))/((hh P n j-1).factorial : ℝ) := by
    funext t
    simp only [A, pfInterval_eval, prod_Ico_eq_prod_range]
  have hBeq (j : ℕ) (hj : j ∈ J) : B j = fun t : ℝ =>
      (∏ i ∈ range (hh P n j-1), (t+(hh P n 0+1-hh P n j+i : ℕ)))/
        ((hh P n j-1).factorial : ℝ) := by
    have hb := pf_hh_bounds P n j (hjq j hj)
    funext t
    simp only [B, pfInterval_eval, prod_Ico_eq_prod_range]
    rw [show hh P n 0-(hh P n 0+1-hh P n j)=hh P n j-1 by omega]
  have ha (j : ℕ) (hj : j ∈ J) : AnalyticAt ℝ (A j) (-(k : ℝ)) ∧
      ∀ u : ℕ, ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^u/(u.factorial : ℝ)*
        iteratedDeriv u (A j) (-(k : ℝ)) = (z : ℝ) := by
    rw [hAeq j hj]
    simpa only [Int.cast_neg, Int.cast_natCast] using
      polynomial_brick_arithmetic N 1 (hh P n j-1) (hdeg j hj) (-(k : ℤ))
  have hb (j : ℕ) (hj : j ∈ J) : AnalyticAt ℝ (B j) (-(k : ℝ)) ∧
      ∀ u : ℕ, ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^u/(u.factorial : ℝ)*
        iteratedDeriv u (B j) (-(k : ℝ)) = (z : ℝ) := by
    rw [hBeq j hj]
    simpa only [Int.cast_neg, Int.cast_natCast] using
      polynomial_brick_arithmetic N (hh P n 0+1-hh P n j) (hh P n j-1)
        (hdeg j hj) (-(k : ℤ))
  have hwidth : hh P n 0-2*hh P n (P.r+1) ≤ N := by
    have hm := Nat.mul_le_mul_right n
      (le_max_right (P.eta P.r) (P.eta 0-2*P.eta (P.r+1)))
    change (P.eta 0-2*P.eta (P.r+1))*n ≤ N at hm
    rw [Nat.sub_mul] at hm
    simp only [hh, if_neg (show P.r+1 ≠ 0 by omega), ↓reduceIte]
    rw [mul_assoc] at hm
    omega
  have hsub (j : ℕ) (hj : j ∈ T) :
      ∀ i ∈ range (hh P n 0-2*hh P n j+1), hh P n j+i ∈ poleRange P n := by
    have hb := pf_hh_bounds P n j (htq j hj)
    have hm := cs_hh_mono P n (i := P.r+1) (j := j) (by omega)
      (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
    intro i hi
    have hi' := mem_range.mp hi
    apply mem_Icc.mpr
    constructor <;> omega
  have hc (j : ℕ) : ∃ f : ℝ → ℝ, j ∈ T →
      AnalyticAt ℝ f (-(k : ℝ)) ∧
      (∀ t : ℝ, (∀ l ∈ poleRange P n, t+(l : ℝ) ≠ 0) →
        f t = (t+k)*((hh P n 0-2*hh P n j).factorial : ℝ)/
          (pfInterval (hh P n j) (hh P n 0+1-hh P n j)).eval₂ (algebraMap ℚ ℝ) t) ∧
      ∀ u : ℕ, ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^u/(u.factorial : ℝ)*
        iteratedDeriv u f (-(k : ℝ)) = (z : ℝ) := by
    by_cases hj : j ∈ T
    · have hbound : ∀ i ∈ range (hh P n 0-2*hh P n j+1),
          ((hh P n j+i : ℕ)-(k : ℤ)).natAbs ≤ N := by
        intro i hi
        have hl := mem_Icc.mp (hsub j hj i hi)
        have hk' := mem_Icc.mp hk
        have hb := pf_hh_bounds P n (P.r+1) (mem_Icc.mpr ⟨by omega, by omega⟩)
        apply Int.ofNat_le.mp
        rw [Int.natCast_natAbs]
        apply abs_le.mpr
        constructor <;> omega
      obtain ⟨f, hf, he, hi⟩ := inverse_brick_regularized N (hh P n j)
        (hh P n 0-2*hh P n j) (k : ℤ) hbound
      refine ⟨f, fun _ => ?_⟩
      simp only [Int.cast_natCast] at hf he hi
      refine ⟨hf, ?_, hi⟩
      intro t ht
      rw [he t (fun i hi => ht _ (hsub j hj i hi)), pfInterval_eval, prod_Ico_eq_prod_range]
      have hb := pf_hh_bounds P n j (htq j hj)
      rw [show hh P n 0+1-hh P n j-hh P n j=hh P n 0-2*hh P n j+1 by omega]
    · exact ⟨0, fun h => (hj h).elim⟩
  choose C hC using hc
  let F : ℝ → ℝ := fun t => ((hh P n 0 : ℝ)+2*t)*
    (∏ j ∈ J, A j t)*(∏ j ∈ J, B j t)*(∏ j ∈ T, C j t)
  have hpoly : AnalyticAt ℝ (fun t : ℝ => (hh P n 0 : ℝ)+2*t) (-(k : ℝ)) ∧
      ∀ u : ℕ, ∃ z : ℤ, (Nat.lcmUpto N : ℝ)^u/(u.factorial : ℝ)*
        iteratedDeriv u (fun t : ℝ => (hh P n 0 : ℝ)+2*t) (-(k : ℝ)) = (z : ℝ) := by
    refine ⟨analyticAt_const.add (analyticAt_const.mul analyticAt_id), fun u => ?_⟩
    simpa only [Int.cast_natCast, Int.cast_ofNat, Int.cast_neg] using
      integer_affine_derivative (Nat.lcmUpto N) u (hh P n 0) 2 (-(k : ℤ))
  have hpa := integral_analytic_mul (Nat.lcmUpto N) _ _ _ hpoly
    ⟨J.analyticAt_fun_prod (fun j hj => (ha j hj).1),
      integral_normalized_derivative_prod J _ A _ (fun j hj => (ha j hj).1) (fun j hj => (ha j hj).2)⟩
  have hpab := integral_analytic_mul (Nat.lcmUpto N) _ _ _ hpa
    ⟨J.analyticAt_fun_prod (fun j hj => (hb j hj).1),
      integral_normalized_derivative_prod J _ B _ (fun j hj => (hb j hj).1) (fun j hj => (hb j hj).2)⟩
  have hpabc := integral_analytic_mul (Nat.lcmUpto N) _ _ _ hpab
    ⟨T.analyticAt_fun_prod (fun j hj => (hC j hj).1),
      integral_normalized_derivative_prod T _ C _ (fun j hj => (hC j hj).1) (fun j hj => (hC j hj).2.2)⟩
  refine ⟨F, hpabc.1, ?_, hpabc.2⟩
  intro t ht
  have he := prod_congr rfl (fun j hj => (hC j hj).2.1 t ht)
  change (∏ j ∈ T, C j t) = _ at he
  dsimp only [F]
  rw [he]
  simp only [A, B, pfNumerator, pfDenominator, eval₂_mul, eval₂_add, eval₂_X,
    eval₂_C, eval₂_finsetProd, map_div₀, map_one, map_natCast, map_ofNat,
    eval₂_natCast, eval₂_ofNat, mul_one_div, prod_mul_distrib, prod_div_distrib,
    prod_const, J, T, Nat.card_Icc]
  rw [show P.q+1-(P.r+1)=P.q-P.r by omega]
  ring

end ZudilinZeta

open ZudilinZeta

theorem solution (P : Params) (n : ℕ) (hn : 0 < n) (d : PartialFractionData P n) :
    ∀ s ∈ Icc 1 (P.q-P.r), ∀ k ∈ poleRange P n,
      ∃ a : ℤ, (D (max (P.eta P.r) (P.eta 0-2*P.eta (P.r+1))*n) : ℚ)^(P.q-P.r-s)*
        d.coeff s k = (a : ℚ) := by
  intro s hs k hk
  obtain ⟨F, hF, hFe, hFi⟩ := rough_factor_arithmetic P n k hk
  have hc := partial_fraction_coefficient_derivative (poleRange P n) (P.q-P.r)
    (fun s k => (d.coeff s k : ℝ)) k hk F hF (fun t ht => by
      rw [hFe t ht, mul_div_assoc, partial_fraction_continuation P n d t ht]) s hs
  obtain ⟨a, ha⟩ := hFi (P.q-P.r-s)
  refine ⟨a, ?_⟩
  have he : (D (max (P.eta P.r) (P.eta 0-2*P.eta (P.r+1))*n) : ℝ)^(P.q-P.r-s)*
      (d.coeff s k : ℝ) = (a : ℝ) := by
    rw [← hc]
    convert ha using 1
    change (Nat.lcmUpto _ : ℝ)^_*(1/_*_) = _
    ring
  exact_mod_cast he
