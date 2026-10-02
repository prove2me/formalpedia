-- Prove2me | solution 1 for ZudilinZeta.zudilin_partial_fraction_prime_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T15:59:36.331057+00:00
-- url     : https://prove2.me/submissions/1e401f3e-7973-40f1-8395-9810d602b1c2

import Definitions.Def_ZudilinZetaPartialFractions

set_option autoImplicit false


/- Source component: VariablePartialFractions -/
section
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
end


/- Source component: PartialFractionUniqueness -/
section
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
end


/- Source component: DecayFromConvergence -/
section
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
end


/- Source component: RationalModel -/
section
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
end


/- Source component: RationalContinuation -/
section
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
end


/- Source component: SelectedPrimeArithmetic -/
section
open Finset

lemma factorial_padic_below_square (p m : ℕ) (hp : p.Prime) (hm : m < p*p) :
    padicValNat p m.factorial = m/p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow' (by norm_num) (by simpa [pow_two] using hm)
  rw [padicValNat_factorial hlog]
  norm_num

lemma integer_padic_below_square (p : ℕ) (hp : p.Prime) (d : ℤ)
    (hd : d ≠ 0) (hb : d.natAbs < p*p) : padicValInt p d ≤ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  by_contra hn
  have hle : 2 ≤ padicValNat p d.natAbs := by change ¬padicValNat p d.natAbs ≤ 1 at hn; omega
  have hdiv : p^2 ∣ d.natAbs := (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hd)).mpr hle
  have hlarge := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hdiv
  rw [pow_two] at hlarge
  omega

lemma prime_over_difference_integral (p : ℕ) (hp : p.Prime) (d : ℤ)
    (hd : d ≠ 0) (hb : d.natAbs < p*p) : 0 ≤ padicValRat p ((p : ℚ)/(d : ℚ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [padicValRat.div hp0 hd0, padicValRat.self hp.one_lt, padicValRat.of_int]
  have h := integer_padic_below_square p hp d hd hb
  omega
end


/- Source component: PadicTaylorArithmetic -/
section
open Finset

namespace ZudilinLocal

def PadicLower (p : ℕ) (a : ℤ) (q : ℚ) : Prop := q=0 ∨ a ≤ padicValRat p q

lemma padicLower_zero (p : ℕ) (a : ℤ) : PadicLower p a 0 := Or.inl rfl

lemma padicLower_int (p : ℕ) (a : ℤ) : PadicLower p 0 (a : ℚ) := by
  right
  rw [padicValRat.of_int]
  positivity

lemma PadicLower.mono {p : ℕ} {a b : ℤ} {q : ℚ} (h : PadicLower p a q) (hba : b ≤ a) :
    PadicLower p b q := h.imp id (hba.trans ·)

lemma PadicLower.mul {p : ℕ} (hp : p.Prime) {a b : ℤ} {q r : ℚ}
    (hq : PadicLower p a q) (hr : PadicLower p b r) : PadicLower p (a+b) (q*r) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hq0 : q=0
  · exact Or.inl (by simp [hq0])
  by_cases hr0 : r=0
  · exact Or.inl (by simp [hr0])
  right
  rw [padicValRat.mul hq0 hr0]
  exact add_le_add (hq.resolve_left hq0) (hr.resolve_left hr0)

lemma PadicLower.add {p : ℕ} (hp : p.Prime) {a : ℤ} {q r : ℚ}
    (hq : PadicLower p a q) (hr : PadicLower p a r) : PadicLower p a (q+r) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hqr : q+r=0
  · exact Or.inl hqr
  by_cases hq0 : q=0
  · simpa only [hq0, zero_add] using hr
  by_cases hr0 : r=0
  · simpa only [hr0, add_zero] using hq
  exact Or.inr ((le_min (hq.resolve_left hq0) (hr.resolve_left hr0)).trans
    (padicValRat.min_le_padicValRat_add hqr))

lemma padicLower_sum {ι : Type*} (p : ℕ) (hp : p.Prime) (a : ℤ) (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ i ∈ s, PadicLower p a (f i)) :
    PadicLower p a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using padicLower_zero p a
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact (hf i (mem_insert_self _ _)).add hp (ih (fun l hl => hf l (mem_insert_of_mem hl)))

def PadicTaylor (p : ℕ) (a : ℤ) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  AnalyticAt ℝ f x ∧ ∀ j : ℕ, ∃ q : ℚ,
    (p : ℝ)^j/(j.factorial : ℝ)*iteratedDeriv j f x = (q : ℝ) ∧ PadicLower p a q

lemma PadicTaylor.mono {p : ℕ} {a b : ℤ} {f : ℝ → ℝ} {x : ℝ}
    (hf : PadicTaylor p a f x) (hba : b ≤ a) : PadicTaylor p b f x := by
  refine ⟨hf.1, fun j => ?_⟩
  obtain ⟨q, hq, hval⟩ := hf.2 j
  exact ⟨q, hq, hval.mono hba⟩

lemma padicTaylor_const (p : ℕ) (a : ℤ) (q : ℚ) (x : ℝ) (hq : PadicLower p a q) :
    PadicTaylor p a (fun _ : ℝ => (q : ℝ)) x := by
  refine ⟨analyticAt_const, fun j => ?_⟩
  cases j with
  | zero => exact ⟨q, by simp, hq⟩
  | succ j => exact ⟨0, by simp [iteratedDeriv_const], padicLower_zero p a⟩

lemma PadicTaylor.mul {p : ℕ} (hp : p.Prime) {a b : ℤ} {f g : ℝ → ℝ} {x : ℝ}
    (hf : PadicTaylor p a f x) (hg : PadicTaylor p b g x) :
    PadicTaylor p (a+b) (fun t => f t*g t) x := by
  classical
  refine ⟨hf.1.mul hg.1, fun j => ?_⟩
  choose A hA hAv using hf.2
  choose B hB hBv using hg.2
  refine ⟨∑ i ∈ range (j+1), A i*B (j-i), ?_,
    padicLower_sum p hp (a+b) (range (j+1)) _ (fun i hi => (hAv i).mul hp (hBv (j-i)))⟩
  rw [iteratedDeriv_fun_mul hf.1.contDiffAt hg.1.contDiffAt, mul_sum]
  push_cast
  apply sum_congr rfl
  intro i hi
  have hij : i ≤ j := by have := mem_range.mp hi; omega
  have hc : (j.choose i : ℝ)*(i.factorial : ℝ)*((j-i).factorial : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hij
  have hi0 : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hji0 : ((j-i).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-i)
  have he : (p : ℝ)^j=(p : ℝ)^i*(p : ℝ)^(j-i) := by rw [← pow_add, Nat.add_sub_of_le hij]
  rw [← hA, ← hB, he]
  field_simp
  linear_combination (p : ℝ)^i*(p : ℝ)^(j-i)*iteratedDeriv i f x*iteratedDeriv (j-i) g x*hc

lemma padicTaylor_prod {ι : Type*} (p : ℕ) (hp : p.Prime) (s : Finset ι)
    (a : ι → ℤ) (f : ι → ℝ → ℝ) (x : ℝ) (hf : ∀ i ∈ s, PadicTaylor p (a i) (f i) x) :
    PadicTaylor p (∑ i ∈ s, a i) (fun t => ∏ i ∈ s, f i t) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, prod_empty]
    simpa only [Rat.cast_one] using padicTaylor_const p 0 1 x (by right; simp)
  | @insert i s hi ih =>
    simp only [sum_insert hi, prod_insert hi]
    exact (hf i (mem_insert_self _ _)).mul hp (ih (fun l hl => hf l (mem_insert_of_mem hl)))

lemma padicTaylor_affine (p : ℕ) (a : ℤ) (c d x : ℚ)
    (h0 : PadicLower p a (c+d*x)) (h1 : PadicLower p a ((p : ℚ)*d)) :
    PadicTaylor p a (fun t : ℝ => (c : ℝ)+(d : ℝ)*t) (x : ℝ) := by
  refine ⟨analyticAt_const.add (analyticAt_const.mul analyticAt_id), fun j => ?_⟩
  cases j with
  | zero => exact ⟨c+d*x, by simp, h0⟩
  | succ j =>
    have he : deriv (fun t : ℝ => (c : ℝ)+(d : ℝ)*t) = fun _ => (d : ℝ) := by funext t; simp
    rw [iteratedDeriv_succ', he]
    cases j with
    | zero => exact ⟨(p : ℚ)*d, by simp, h1⟩
    | succ j => exact ⟨0, by simp [iteratedDeriv_const], padicLower_zero p a⟩

lemma padicTaylor_reciprocal (p : ℕ) (hp : p.Prime) (l x : ℚ)
    (hx : x+l ≠ 0) (hv : padicValRat p (x+l) ≤ 1) :
    PadicTaylor p (-padicValRat p (x+l)) (fun t : ℝ => (t+(l : ℝ))⁻¹) (x : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hxr : (x : ℝ)+(l : ℝ) ≠ 0 := by exact_mod_cast hx
  refine ⟨(analyticAt_id.add analyticAt_const).inv hxr, fun j => ?_⟩
  let q : ℚ := (-1)^j*(p : ℚ)^j/(x+l)^(j+1)
  refine ⟨q, ?_, ?_⟩
  · rw [iteratedDeriv_comp_add_const j (fun t : ℝ => t⁻¹) (l : ℝ), iteratedDeriv_eq_iterate]
    dsimp only
    rw [iter_deriv_inv, show (-1-(j : ℤ)) = -((j+1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    simp only [q, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
      Rat.cast_natCast, Rat.cast_add]
    field_simp
  · right
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hneg : (-1 : ℚ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
    have hvq : padicValRat p q = (j : ℤ)-((j+1 : ℕ) : ℤ)*padicValRat p (x+l) := by
      dsimp only [q]
      rw [padicValRat.div (mul_ne_zero hneg (pow_ne_zero _ hp0)) (pow_ne_zero _ hx),
        padicValRat.mul hneg (pow_ne_zero _ hp0)]
      simp only [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero, zero_add,
        padicValRat.self hp.one_lt, mul_one]
    rw [hvq]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hv (show (0 : ℤ) ≤ j by positivity)]

end ZudilinLocal
end


/- Source component: IntervalPadicValuation -/
section
open Finset

namespace ZudilinLocal

lemma ediv_step (p d : ℤ) (hp : 0 < p) :
    d/p-(d-1)/p = if p ∣ d then 1 else 0 := by
  have hlo := Int.emod_nonneg d hp.ne'
  have hhi := Int.emod_lt_of_pos d hp
  have he := Int.emod_add_ediv_mul d p
  by_cases hd : p ∣ d
  · have hz : d%p=0 := Int.emod_eq_zero_of_dvd hd
    have hq : (d-1)/p=d/p-1 := (Int.ediv_eq_iff_of_pos hp).mpr ⟨by nlinarith, by nlinarith⟩
    rw [hq, if_pos hd]
    ring
  · have hn : d%p ≠ 0 := fun h => hd (Int.dvd_of_emod_eq_zero h)
    have hpos : 1 ≤ d%p := by omega
    have hq : (d-1)/p=d/p := (Int.ediv_eq_iff_of_pos hp).mpr ⟨by nlinarith, by nlinarith⟩
    rw [hq, if_neg hd, sub_self]

lemma integer_padic_floor_step (p : ℕ) (hp : p.Prime) (d : ℤ)
    (hb : d.natAbs < p*p) :
    (padicValInt p d : ℤ) = d/(p : ℤ)-(d-1)/(p : ℤ)-(if d=0 then 1 else 0) := by
  rw [ediv_step _ _ (by exact_mod_cast hp.pos)]
  by_cases hd0 : d=0
  · subst d
    simp
  · rw [if_neg hd0]
    by_cases hd : (p : ℤ) ∣ d
    · rw [if_pos hd]
      have hupper := integer_padic_below_square p hp d hd0 hb
      have hlower : 1 ≤ padicValInt p d := by
        have hdiv : (p : ℤ)^1 ∣ d := by simpa only [pow_one] using hd
        exact ((padicValInt_dvd_iff_of_ne_one hp.ne_one 1 d).mp hdiv).resolve_left hd0
      have hv : padicValInt p d=1 := by omega
      simp only [hv, Nat.cast_one, sub_zero]
    · rw [if_neg hd, padicValInt.eq_zero_of_not_dvd hd]
      simp

lemma sum_interval_padic (p a b k : ℕ) (hp : p.Prime) (hab : a ≤ b)
    (hbound : ∀ l ∈ Ico a b, ((l : ℤ)-k).natAbs < p*p) :
    (∑ l ∈ Ico a b, (padicValInt p ((l : ℤ)-k) : ℤ)) =
      ((b : ℤ)-1-k)/(p : ℤ)-((a : ℤ)-1-k)/(p : ℤ) -
        (if k ∈ Ico a b then 1 else 0) := by
  have he (l : ℕ) (hl : l ∈ Ico a b) := integer_padic_floor_step p hp ((l : ℤ)-k) (hbound l hl)
  rw [sum_congr rfl he, sum_sub_distrib]
  have hdelta : (∑ l ∈ Ico a b, (((l : ℤ)-k)/(p : ℤ)-((l : ℤ)-k-1)/(p : ℤ))) =
      ((b : ℤ)-1-k)/(p : ℤ)-((a : ℤ)-1-k)/(p : ℤ) := by
    clear hbound he
    induction b, hab using Nat.le_induction with
    | base => simp
    | @succ b hab ih =>
      rw [sum_Ico_succ_top hab, ih]
      push_cast
      have h1 : (b : ℤ)+1-1-k=(b : ℤ)-k := by ring
      have h2 : (b : ℤ)-k-1=(b : ℤ)-1-k := by ring
      rw [h1, h2]
      ring
  rw [hdelta]
  congr 1
  have hz (l : ℕ) : (if (l : ℤ)-k=0 then (1 : ℤ) else 0) = if l=k then 1 else 0 := by
    simp only [sub_eq_zero, Nat.cast_inj]
  rw [sum_congr rfl (fun l hl => hz l)]
  simp

lemma ediv_negative_complement (p : ℕ) (hp : 0 < p) (d : ℤ) :
    (-d-1)/(p : ℤ) = -(d/(p : ℤ))-1 := by
  have hp' : (0 : ℤ)<p := by exact_mod_cast hp
  have hlo := Int.emod_nonneg d hp'.ne'
  have hhi := Int.emod_lt_of_pos d hp'
  have he := Int.emod_add_ediv_mul d (p : ℤ)
  apply (Int.ediv_eq_iff_of_pos hp').mpr
  constructor <;> nlinarith

end ZudilinLocal
end


/- Source component: PrimeBrickArithmetic -/
section
open Finset

namespace ZudilinLocal

lemma padicTaylor_integer_linear (p l k : ℕ) (hp : p.Prime) (hlk : l ≠ k)
    (hb : ((l : ℤ)-k).natAbs < p*p) :
    PadicTaylor p (padicValInt p ((l : ℤ)-k) : ℤ) (fun t : ℝ => t+l) (-(k : ℝ)) := by
  have hd : (l : ℤ)-k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hlk)
  have hv := integer_padic_below_square p hp _ hd hb
  have h0 : PadicLower p (padicValInt p ((l : ℤ)-k) : ℤ) ((l : ℚ)+1*(-k)) := by
    right
    have he : (l : ℚ)+1*(-k)=((l : ℤ)-k : ℤ) := by push_cast; ring
    rw [he, padicValRat.of_int]
  have h1 : PadicLower p (padicValInt p ((l : ℤ)-k) : ℤ) ((p : ℚ)*1) := by
    right
    rw [mul_one, padicValRat.self hp.one_lt]
    exact_mod_cast hv
  simpa only [Rat.cast_natCast, Rat.cast_neg, Rat.cast_one, one_mul, add_comm] using
    padicTaylor_affine p _ (l : ℚ) 1 (-(k : ℚ)) h0 h1

lemma padicTaylor_centered_linear (p k : ℕ) (hp : p.Prime) :
    PadicTaylor p 1 (fun t : ℝ => t+k) (-(k : ℝ)) := by
  have h0 : PadicLower p 1 ((k : ℚ)+1*(-k)) := by left; ring
  have h1 : PadicLower p 1 ((p : ℚ)*1) := by right; simp only [mul_one, padicValRat.self hp.one_lt, le_refl]
  simpa only [Rat.cast_natCast, Rat.cast_neg, Rat.cast_one, one_mul, add_comm] using
    padicTaylor_affine p 1 (k : ℚ) 1 (-(k : ℚ)) h0 h1

lemma padicTaylor_integer_affine (p : ℕ) (a b k : ℤ) :
    PadicTaylor p 0 (fun t : ℝ => (a : ℝ)+(b : ℝ)*t) (k : ℝ) := by
  have h0 : PadicLower p 0 ((a : ℚ)+(b : ℚ)*(k : ℚ)) := by
    exact_mod_cast padicLower_int p (a+b*k)
  have h1 : PadicLower p 0 ((p : ℚ)*(b : ℚ)) := by
    exact_mod_cast padicLower_int p ((p : ℤ)*b)
  simpa only [Rat.cast_intCast] using padicTaylor_affine p 0 (a : ℚ) (b : ℚ) (k : ℚ) h0 h1

lemma padicTaylor_integer_reciprocal (p l k : ℕ) (hp : p.Prime) (hlk : l ≠ k)
    (hb : ((l : ℤ)-k).natAbs < p*p) :
    PadicTaylor p (-(padicValInt p ((l : ℤ)-k) : ℤ)) (fun t : ℝ => (t+l)⁻¹) (-(k : ℝ)) := by
  have hd : (l : ℤ)-k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hlk)
  have hq : -(k : ℚ)+l=((l : ℤ)-k : ℤ) := by push_cast; ring
  have hq0 : -(k : ℚ)+l ≠ 0 := by rw [hq]; exact_mod_cast hd
  have hval : padicValRat p (-(k : ℚ)+l)=(padicValInt p ((l : ℤ)-k) : ℤ) := by
    rw [hq, padicValRat.of_int]
  have hv : padicValRat p (-(k : ℚ)+l) ≤ 1 := by
    rw [hval]
    exact_mod_cast integer_padic_below_square p hp _ hd hb
  simpa only [hval, Rat.cast_natCast, Rat.cast_neg] using
    padicTaylor_reciprocal p hp (l : ℚ) (-(k : ℚ)) hq0 hv

lemma padicTaylor_factorial (p m : ℕ) (hp : p.Prime) (hm : m < p*p) (x : ℝ) :
    PadicTaylor p ((m : ℤ)/p) (fun _ : ℝ => (m.factorial : ℝ)) x := by
  have hv : padicValRat p (m.factorial : ℚ)=((m : ℤ)/p) := by
    rw [padicValRat.of_nat, factorial_padic_below_square p m hp hm, Int.natCast_ediv]
  simpa only [Rat.cast_natCast] using
    padicTaylor_const p ((m : ℤ)/p) (m.factorial : ℚ) x (Or.inr hv.ge)

lemma padicTaylor_inverse_factorial (p m : ℕ) (hp : p.Prime) (hm : m < p*p) (x : ℝ) :
    PadicTaylor p (-((m : ℤ)/p)) (fun _ : ℝ => (m.factorial : ℝ)⁻¹) x := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv : padicValRat p ((m.factorial : ℚ)⁻¹) = -((m : ℤ)/p) := by
    rw [padicValRat.inv, padicValRat.of_nat, factorial_padic_below_square p m hp hm,
      Int.natCast_ediv]
  simpa only [Rat.cast_inv, Rat.cast_natCast] using
    padicTaylor_const p (-((m : ℤ)/p)) ((m.factorial : ℚ)⁻¹) x (Or.inr hv.ge)

lemma padicTaylor_polynomial_interval (p a b k : ℕ) (hp : p.Prime) (hab : a ≤ b)
    (hk : k ∉ Ico a b) (hm : b-a < p*p)
    (hbound : ∀ l ∈ Ico a b, ((l : ℤ)-k).natAbs < p*p) :
    PadicTaylor p (((b : ℤ)-1-k)/p-((a : ℤ)-1-k)/p-((b-a : ℕ) : ℤ)/p)
      (fun t : ℝ => (∏ l ∈ Ico a b, (t+l))/((b-a).factorial : ℝ)) (-(k : ℝ)) := by
  have hprod := padicTaylor_prod p hp (Ico a b) (fun l => (padicValInt p ((l : ℤ)-k) : ℤ))
    (fun l t => t+(l : ℝ)) (-(k : ℝ)) (fun l hl =>
      padicTaylor_integer_linear p l k hp (fun he => hk (he ▸ hl)) (hbound l hl))
  have h := hprod.mul hp (padicTaylor_inverse_factorial p (b-a) hp hm (-(k : ℝ)))
  rw [sum_interval_padic p a b k hp hab hbound, if_neg hk, sub_zero] at h
  simpa only [sub_eq_add_neg, div_eq_mul_inv] using h

lemma padicTaylor_inverse_interval (p a b k : ℕ) (hp : p.Prime) (hab : a < b)
    (hm : b-a-1 < p*p) (hbound : ∀ l ∈ Ico a b, ((l : ℤ)-k).natAbs < p*p) :
    ∃ F : ℝ → ℝ,
      PadicTaylor p (((b-a-1 : ℕ) : ℤ)/p-((k : ℤ)-a)/p-((b : ℤ)-1-k)/p) F (-(k : ℝ)) ∧
      ∀ t : ℝ, (∀ l ∈ Ico a b, t+(l : ℝ) ≠ 0) →
        F t = (t+k)*((b-a-1).factorial : ℝ)/(∏ l ∈ Ico a b, (t+l)) := by
  classical
  let V : ℤ := ∑ l ∈ Ico a b, (padicValInt p ((l : ℤ)-k) : ℤ)
  have hc := padicTaylor_factorial p (b-a-1) hp hm (-(k : ℝ))
  have hcomp : ((a : ℤ)-1-k)/p = -(((k : ℤ)-a)/p)-1 := by
    rw [show (a : ℤ)-1-k= -((k : ℤ)-a)-1 by ring]
    exact ediv_negative_complement p hp.pos _
  by_cases hk : k ∈ Ico a b
  · let F : ℝ → ℝ := fun t => ((b-a-1).factorial : ℝ)*∏ l ∈ (Ico a b).erase k, (t+l)⁻¹
    have hprod := padicTaylor_prod p hp ((Ico a b).erase k)
      (fun l => -(padicValInt p ((l : ℤ)-k) : ℤ))
      (fun l t => (t+(l : ℝ))⁻¹) (-(k : ℝ)) (fun l hl =>
        padicTaylor_integer_reciprocal p l k hp (mem_erase.mp hl).1 (hbound l (mem_erase.mp hl).2))
    have hv : (∑ l ∈ (Ico a b).erase k, -(padicValInt p ((l : ℤ)-k) : ℤ)) = -V := by
      rw [sum_neg_distrib, Finset.sum_erase (Ico a b) (f := fun l => (padicValInt p ((l : ℤ)-k) : ℤ))
        (a := k) (by simp)]
    have h := hc.mul hp hprod
    rw [hv] at h
    have he : ((b-a-1 : ℕ) : ℤ)/p + -V =
        ((b-a-1 : ℕ) : ℤ)/p-((k : ℤ)-a)/p-((b : ℤ)-1-k)/p := by
      dsimp only [V]
      rw [sum_interval_padic p a b k hp hab.le hbound, if_pos hk, hcomp]
      ring
    rw [he] at h
    refine ⟨F, h, fun t ht => ?_⟩
    dsimp only [F]
    rw [prod_inv_distrib, ← mul_prod_erase (Ico a b) (fun l => t+(l : ℝ)) hk]
    field_simp [ht k hk]
  · let F : ℝ → ℝ := fun t => (t+k)*((b-a-1).factorial : ℝ)*∏ l ∈ Ico a b, (t+l)⁻¹
    have hprod := padicTaylor_prod p hp (Ico a b)
      (fun l => -(padicValInt p ((l : ℤ)-k) : ℤ))
      (fun l t => (t+(l : ℝ))⁻¹) (-(k : ℝ)) (fun l hl =>
        padicTaylor_integer_reciprocal p l k hp (fun he => hk (he ▸ hl)) (hbound l hl))
    have h := ((padicTaylor_centered_linear p k hp).mul hp hc).mul hp hprod
    rw [sum_neg_distrib] at h
    have he : 1+((b-a-1 : ℕ) : ℤ)/p + -V =
        ((b-a-1 : ℕ) : ℤ)/p-((k : ℤ)-a)/p-((b : ℤ)-1-k)/p := by
      dsimp only [V]
      rw [sum_interval_padic p a b k hp hab.le hbound, if_neg hk, hcomp]
      ring
    change PadicTaylor p (1+((b-a-1 : ℕ) : ℤ)/p + -V) F (-(k : ℝ)) at h
    rw [he] at h
    refine ⟨F, h, fun t ht => ?_⟩
    simp only [F, prod_inv_distrib, div_eq_mul_inv]

end ZudilinLocal
end


/- Source component: PhiMinimumComparison -/
section
open Set ZudilinZeta

-- The following floor-superadditivity proof reuses the argument in the accepted
-- Prove2Me submission c74c01b0-dbc0-4054-acf6-232df78455ed (cm_beta).
private lemma phiExpr_nonneg (P : Params) (x y : ℝ) : 0 ≤ phiExpr P x y := by
  have h1 (e0 ej : ℝ) :
      0 ≤ ⌊y⌋ + ⌊e0 * x - y⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ - 2 * ⌊ej * x⌋ := by
    have ha : ⌊(e0 - ej) * x - y⌋ + ⌊ej * x⌋ ≤ ⌊e0 * x - y⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le ((e0 - ej) * x - y), Int.floor_le (ej * x)]
    have hb : ⌊ej * x⌋ + ⌊y - ej * x⌋ ≤ ⌊y⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (y - ej * x), Int.floor_le (ej * x)]
    omega
  have h2 (e0 ej : ℝ) :
      0 ≤ ⌊(e0 - 2 * ej) * x⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ := by
    have h : ⌊y - ej * x⌋ + ⌊(e0 - ej) * x - y⌋ ≤ ⌊(e0 - 2 * ej) * x⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (y - ej * x), Int.floor_le ((e0 - ej) * x - y)]
    omega
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => h1 _ _))
    (Finset.sum_nonneg (fun _ _ => h2 _ _))

private lemma phiExpr_bddBelow (P : Params) (x : ℝ) :
    BddBelow (phiExpr P x '' Ico (0 : ℝ) 1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, _, rfl⟩
  exact phiExpr_nonneg P x y

lemma phiExpr_translate_integer_y (P : Params) (x y : ℝ) (z : ℤ) :
    phiExpr P x (y+z) = phiExpr P x y := by
  have h1 (e : ℝ) : ⌊e-(y+(z : ℝ))⌋ = ⌊e-y⌋-z := by
    rw [show e-(y+(z : ℝ))=(e-y)-(z : ℝ) by ring, Int.floor_sub_intCast]
  have h2 (e : ℝ) : ⌊y+(z : ℝ)-e⌋ = ⌊y-e⌋+z := by
    rw [show y+(z : ℝ)-e=(y-e)+(z : ℝ) by ring, Int.floor_add_intCast]
  unfold phiExpr
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Int.floor_add_intCast, h1, h2, h1]
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    rw [h2, h1]
    ring

lemma phi_le_phiExpr (P : Params) (x y : ℝ) : phi P x ≤ phiExpr P x y := by
  have he : phiExpr P x (Int.fract y)=phiExpr P x y := by
    have h := phiExpr_translate_integer_y P x (Int.fract y) ⌊y⌋
    rw [Int.fract_add_floor] at h
    exact h.symm
  apply csInf_le (phiExpr_bddBelow P x)
  exact ⟨Int.fract y, ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩, he⟩
end


/- Source component: PrimeFloorIdentity -/
section
open Finset ZudilinLocal

namespace ZudilinZeta

lemma prime_floor_identity (P : Params) (n p k : ℕ) :
    phiExpr P ((n : ℝ)/(p : ℝ)) (((k : ℝ)-1)/(p : ℝ)) =
      (∑ j ∈ Icc 1 P.r,
        (((k : ℤ)-1)/p-((k : ℤ)-hh P n j)/p-((hh P n j-1 : ℕ) : ℤ)/p)) +
      (∑ j ∈ Icc 1 P.r,
        (((hh P n 0 : ℤ)-1-k)/p-((hh P n 0 : ℤ)-hh P n j-k)/p-((hh P n j-1 : ℕ) : ℤ)/p)) +
      ∑ j ∈ Icc (P.r+1) P.q,
        (((hh P n 0-2*hh P n j : ℕ) : ℤ)/p-((k : ℤ)-hh P n j)/p-
          ((hh P n 0 : ℤ)-hh P n j-k)/p) := by
  have hqr := P.q_ge
  have hfloor (z : ℤ) : ⌊(z : ℝ)/(p : ℝ)⌋ = z/(p : ℤ) := by
    rw [Int.floor_div_natCast, Int.floor_intCast]
  have h0 : hh P n 0=P.eta 0*n+2 := by simp [hh]
  have hj (j : ℕ) (hj : j ∈ Icc 1 P.q) : hh P n j=P.eta j*n+1 := by
    simp only [hh, if_neg (show j ≠ 0 by have := (mem_Icc.mp hj).1; omega)]
  have hf1 : ⌊((k : ℝ)-1)/(p : ℝ)⌋ = ((k : ℤ)-1)/p := by
    simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_one] using hfloor ((k : ℤ)-1)
  have hf2 : ⌊(P.eta 0 : ℝ)*((n : ℝ)/(p : ℝ))-((k : ℝ)-1)/(p : ℝ)⌋ =
      ((hh P n 0 : ℤ)-1-k)/p := by
    rw [show (P.eta 0 : ℝ)*((n : ℝ)/(p : ℝ))-((k : ℝ)-1)/(p : ℝ) =
      (((hh P n 0 : ℤ)-1-k : ℤ) : ℝ)/(p : ℝ) by rw [h0]; push_cast; ring]
    exact hfloor _
  have hf3 (j : ℕ) (hjq : j ∈ Icc 1 P.q) :
      ⌊((k : ℝ)-1)/(p : ℝ)-(P.eta j : ℝ)*((n : ℝ)/(p : ℝ))⌋ =
        ((k : ℤ)-hh P n j)/p := by
    rw [show ((k : ℝ)-1)/(p : ℝ)-(P.eta j : ℝ)*((n : ℝ)/(p : ℝ)) =
      (((k : ℤ)-hh P n j : ℤ) : ℝ)/(p : ℝ) by rw [hj j hjq]; push_cast; ring]
    exact hfloor _
  have hf4 (j : ℕ) (hjq : j ∈ Icc 1 P.q) :
      ⌊((P.eta 0 : ℝ)-(P.eta j : ℝ))*((n : ℝ)/(p : ℝ))-((k : ℝ)-1)/(p : ℝ)⌋ =
        ((hh P n 0 : ℤ)-hh P n j-k)/p := by
    rw [show ((P.eta 0 : ℝ)-(P.eta j : ℝ))*((n : ℝ)/(p : ℝ))-((k : ℝ)-1)/(p : ℝ) =
      (((hh P n 0 : ℤ)-hh P n j-k : ℤ) : ℝ)/(p : ℝ) by rw [h0, hj j hjq]; push_cast; ring]
    exact hfloor _
  have hf5 (j : ℕ) (hjq : j ∈ Icc 1 P.q) :
      ⌊(P.eta j : ℝ)*((n : ℝ)/(p : ℝ))⌋ = ((hh P n j-1 : ℕ) : ℤ)/p := by
    have hm : hh P n j-1=P.eta j*n := by rw [hj j hjq]; omega
    rw [hm, show (P.eta j : ℝ)*((n : ℝ)/(p : ℝ)) =
      (((P.eta j*n : ℕ) : ℤ) : ℝ)/(p : ℝ) by push_cast; ring]
    exact hfloor _
  have hf6 (j : ℕ) (hjq : j ∈ Icc 1 P.q) :
      ⌊((P.eta 0 : ℝ)-2*(P.eta j : ℝ))*((n : ℝ)/(p : ℝ))⌋ =
        ((hh P n 0-2*hh P n j : ℕ) : ℤ)/p := by
    have hb := (pf_hh_bounds P n j hjq).2
    rw [show ((P.eta 0 : ℝ)-2*(P.eta j : ℝ))*((n : ℝ)/(p : ℝ)) =
      (((hh P n 0-2*hh P n j : ℕ) : ℤ) : ℝ)/(p : ℝ) by
        rw [Nat.cast_sub hb, h0, hj j hjq]; push_cast; ring]
    exact hfloor _
  unfold phiExpr
  rw [← sum_add_distrib]
  congr 1
  · apply sum_congr rfl
    intro j hjr
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hjr).1, by have := (mem_Icc.mp hjr).2; omega⟩
    rw [hf1, hf2, hf3 j hjq, hf4 j hjq, hf5 j hjq]
    ring
  · apply sum_congr rfl
    intro j hjt
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hjt).1; omega, (mem_Icc.mp hjt).2⟩
    rw [hf3 j hjq, hf4 j hjq, hf6 j hjq]

end ZudilinZeta
end


/- Source component: PartialFractionCoefficientDerivative -/
section
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
end


/- Source component: PrimeCoefficientBound -/
section
open Polynomial Finset ZudilinLocal

namespace ZudilinZeta

lemma prime_factor_arithmetic (P : Params) (n k p : ℕ) (hk : k ∈ poleRange P n)
    (hp : p.Prime) (hpp : P.eta 0*n < p*p) :
    ∃ F : ℝ → ℝ, PadicTaylor p (phiExpr P ((n : ℝ)/(p : ℝ)) (((k : ℝ)-1)/(p : ℝ))) F (-(k : ℝ)) ∧
      ∀ t : ℝ, (∀ l ∈ poleRange P n, t+(l : ℝ) ≠ 0) →
        F t = (t+k)^(P.q-P.r)*(pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
          (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t := by
  classical
  let H := hh P n 0
  let J := Icc 1 P.r
  let T := Icc (P.r+1) P.q
  let A : ℕ → ℝ → ℝ := fun j t =>
    (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t/((hh P n j-1).factorial : ℝ)
  let B : ℕ → ℝ → ℝ := fun j t =>
    (pfInterval (H+1-hh P n j) H).eval₂ (algebraMap ℚ ℝ) t/((hh P n j-1).factorial : ℝ)
  let a : ℕ → ℤ := fun j => ((k : ℤ)-1)/p-((k : ℤ)-hh P n j)/p-((hh P n j-1 : ℕ) : ℤ)/p
  let b : ℕ → ℤ := fun j => ((H : ℤ)-1-k)/p-((H : ℤ)-hh P n j-k)/p-((hh P n j-1 : ℕ) : ℤ)/p
  let c : ℕ → ℤ := fun j => ((H-2*hh P n j : ℕ) : ℤ)/p-((k : ℤ)-hh P n j)/p-((H : ℤ)-hh P n j-k)/p
  have hqr := P.q_ge
  have hH : H=P.eta 0*n+2 := by simp [H, hh]
  have hR := pf_hh_bounds P n (P.r+1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hk' := mem_Icc.mp hk
  have hkH : 1 ≤ k ∧ k ≤ H-1 := by dsimp [H]; omega
  have hjq (j : ℕ) (hj : j ∈ J) : j ∈ Icc 1 P.q :=
    mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
  have htq (j : ℕ) (hj : j ∈ T) : j ∈ Icc 1 P.q :=
    mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
  have hdiff (l : ℕ) (hl : l ∈ Icc 1 (H-1)) : ((l : ℤ)-k).natAbs < p*p := by
    have hl' := mem_Icc.mp hl
    apply Int.ofNat_lt.mp
    rw [Int.natCast_natAbs]
    apply abs_lt.mpr
    constructor <;> omega
  have hm (j : ℕ) (hj : j ∈ Icc 1 P.q) :
      hh P n j-1 < p*p ∧ H-2*hh P n j < p*p := by
    have hb := pf_hh_bounds P n j hj
    change 0 < hh P n j ∧ 2*hh P n j ≤ H at hb
    constructor <;> omega
  have hgap (j : ℕ) (hj : j ∈ J) : hh P n j ≤ k ∧ k ≤ H-hh P n j := by
    have hj' := mem_Icc.mp hj
    have hmono := cs_hh_mono P n (i := j) (j := P.r+1) hj'.1 (by omega) (by omega)
    change hh P n (P.r+1) ≤ k ∧ k ≤ H-hh P n (P.r+1) at hk'
    constructor <;> omega
  have ha (j : ℕ) (hj : j ∈ J) : PadicTaylor p (a j) (A j) (-(k : ℝ)) := by
    have hbj := pf_hh_bounds P n j (hjq j hj)
    change 0 < hh P n j ∧ 2*hh P n j ≤ H at hbj
    have hgapj := hgap j hj
    have hknot : k ∉ Ico 1 (hh P n j) := by intro h; have := mem_Ico.mp h; omega
    have h := padicTaylor_polynomial_interval p 1 (hh P n j) k hp (by omega) hknot
      (hm j (hjq j hj)).1 (fun l hl => hdiff l (mem_Icc.mpr ⟨(mem_Ico.mp hl).1, by have := (mem_Ico.mp hl).2; omega⟩))
    have he1 : ((hh P n j : ℤ)-1-k)/p = -(((k : ℤ)-hh P n j)/p)-1 := by
      rw [show (hh P n j : ℤ)-1-k = -((k : ℤ)-hh P n j)-1 by ring]
      exact ediv_negative_complement p hp.pos _
    have he2 : ((1 : ℤ)-1-k)/p = -(((k : ℤ)-1)/p)-1 := by
      rw [show (1 : ℤ)-1-k = -((k : ℤ)-1)-1 by ring]
      exact ediv_negative_complement p hp.pos _
    rw [Nat.cast_one, he1, he2] at h
    have he : -(((k : ℤ)-hh P n j)/p)-1-(-(((k : ℤ)-1)/p)-1)-((hh P n j-1 : ℕ) : ℤ)/p = a j := by
      dsimp only [a]
      ring
    rw [he] at h
    simpa only [A, pfInterval_eval] using h
  have hb (j : ℕ) (hj : j ∈ J) : PadicTaylor p (b j) (B j) (-(k : ℝ)) := by
    have hbj := pf_hh_bounds P n j (hjq j hj)
    change 0 < hh P n j ∧ 2*hh P n j ≤ H at hbj
    have hgapj := hgap j hj
    have hknot : k ∉ Ico (H+1-hh P n j) H := by intro h; have := mem_Ico.mp h; omega
    have hlen : H-(H+1-hh P n j)=hh P n j-1 := by omega
    have h := padicTaylor_polynomial_interval p (H+1-hh P n j) H k hp (by omega) hknot
      (by rw [hlen]; exact (hm j (hjq j hj)).1) (fun l hl =>
        hdiff l (mem_Icc.mpr ⟨by have := (mem_Ico.mp hl).1; omega, by have := (mem_Ico.mp hl).2; omega⟩))
    have he : ((H+1-hh P n j : ℕ) : ℤ)-1-k=(H : ℤ)-hh P n j-k := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hlen, he] at h
    simpa only [B, b, pfInterval_eval] using h
  have hsub (j : ℕ) (hj : j ∈ T) : Ico (hh P n j) (H+1-hh P n j) ⊆ poleRange P n := by
    have hmono := cs_hh_mono P n (i := P.r+1) (j := j) (by omega)
      (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
    have hbj := pf_hh_bounds P n j (htq j hj)
    change 0 < hh P n j ∧ 2*hh P n j ≤ H at hbj
    intro l hl
    have hl' := mem_Ico.mp hl
    apply mem_Icc.mpr
    change hh P n (P.r+1) ≤ l ∧ l ≤ H-hh P n (P.r+1)
    constructor <;> omega
  have hc (j : ℕ) : ∃ f : ℝ → ℝ, j ∈ T → PadicTaylor p (c j) f (-(k : ℝ)) ∧
      ∀ t : ℝ, (∀ l ∈ poleRange P n, t+(l : ℝ) ≠ 0) →
        f t = (t+k)*((H-2*hh P n j).factorial : ℝ)/
          (pfInterval (hh P n j) (H+1-hh P n j)).eval₂ (algebraMap ℚ ℝ) t := by
    by_cases hj : j ∈ T
    · have hbj := pf_hh_bounds P n j (htq j hj)
      change 0 < hh P n j ∧ 2*hh P n j ≤ H at hbj
      have hlen : H+1-hh P n j-hh P n j-1=H-2*hh P n j := by omega
      obtain ⟨f, hf, he⟩ := padicTaylor_inverse_interval p (hh P n j) (H+1-hh P n j) k hp
        (by omega) (by rw [hlen]; exact (hm j (htq j hj)).2) (fun l hl =>
          hdiff l (mem_Icc.mpr ⟨by have := (mem_Ico.mp hl).1; omega, by have := (mem_Ico.mp hl).2; omega⟩))
      have hex : ((H+1-hh P n j : ℕ) : ℤ)-1-k=(H : ℤ)-hh P n j-k := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hlen, hex] at hf
      refine ⟨f, fun _ => ⟨hf, fun t ht => ?_⟩⟩
      rw [he t (fun l hl => ht l (hsub j hj hl)), hlen, pfInterval_eval]
    · exact ⟨0, fun h => (hj h).elim⟩
  choose C hC using hc
  let F : ℝ → ℝ := fun t => ((H : ℝ)+2*t)*(∏ j ∈ J, A j t)*(∏ j ∈ J, B j t)*(∏ j ∈ T, C j t)
  have hpoly : PadicTaylor p 0 (fun t : ℝ => (H : ℝ)+2*t) (-(k : ℝ)) := by
    simpa only [Int.cast_natCast, Int.cast_ofNat, Int.cast_neg] using padicTaylor_integer_affine p (H : ℤ) 2 (-(k : ℤ))
  have hpa := hpoly.mul hp (padicTaylor_prod p hp J a A _ ha)
  have hpab := hpa.mul hp (padicTaylor_prod p hp J b B _ hb)
  have hpabc := hpab.mul hp (padicTaylor_prod p hp T c C _ (fun j hj => (hC j hj).1))
  have hweight : 0+(∑ j ∈ J, a j)+(∑ j ∈ J, b j)+(∑ j ∈ T, c j) =
      phiExpr P ((n : ℝ)/(p : ℝ)) (((k : ℝ)-1)/(p : ℝ)) := by
    simpa only [zero_add, a, b, c, J, T, H] using (prime_floor_identity P n p k).symm
  rw [hweight] at hpabc
  refine ⟨F, hpabc, fun t ht => ?_⟩
  have he := prod_congr rfl (fun j hj => (hC j hj).2 t ht)
  change (∏ j ∈ T, C j t) = _ at he
  dsimp only [F]
  rw [he]
  simp only [A, B, H, pfNumerator, pfDenominator, eval₂_mul, eval₂_add, eval₂_X,
    eval₂_C, eval₂_finsetProd, map_div₀, map_one, map_natCast, map_ofNat,
    eval₂_natCast, eval₂_ofNat, prod_mul_distrib, prod_div_distrib,
    prod_const, J, T, Nat.card_Icc]
  rw [show P.q+1-(P.r+1)=P.q-P.r by omega]
  ring

end ZudilinZeta

open ZudilinZeta

theorem solution (P : Params) (n : ℕ) (hn : 0 < n) (d : PartialFractionData P n) :
    ∀ s ∈ Icc 1 (P.q-P.r), ∀ k ∈ poleRange P n, d.coeff s k ≠ 0 →
      ∀ p : ℕ, p.Prime → P.eta 0*n < p*p → p ≤ m P (P.q-P.r)*n →
        -((P.q-P.r-s : ℕ) : ℤ)+phi P ((n : ℝ)/(p : ℝ)) ≤ padicValRat p (d.coeff s k) := by
  intro s hs k hk hc p hp hpp hpm
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hF, hFe⟩ := prime_factor_arithmetic P n k p hk hp hpp
  have hcoeff := partial_fraction_coefficient_derivative (poleRange P n) (P.q-P.r)
    (fun s k => (d.coeff s k : ℝ)) k hk F hF.1 (fun t ht => by
      rw [hFe t ht, mul_div_assoc, partial_fraction_continuation P n d t ht]) s hs
  obtain ⟨a, ha, hva⟩ := hF.2 (P.q-P.r-s)
  have he : a=(p : ℚ)^(P.q-P.r-s)*d.coeff s k := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [← ha, ← hcoeff]
    ring
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a ≠ 0 := by rw [he]; exact mul_ne_zero (pow_ne_zero _ hp0) hc
  have hv := hva.resolve_left ha0
  rw [he, padicValRat.mul (pow_ne_zero _ hp0) hc, padicValRat.pow, padicValRat.self hp.one_lt, mul_one] at hv
  have hphi := phi_le_phiExpr P ((n : ℝ)/(p : ℝ)) (((k : ℝ)-1)/(p : ℝ))
  omega
end
