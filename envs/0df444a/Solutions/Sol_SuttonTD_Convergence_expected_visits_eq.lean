-- Prove2me | solution 1 for SuttonTD.Convergence.expected_visits_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T23:59:53.179476+00:00
-- url     : https://prove2.me/submissions/28a31ca0-f39b-4adc-8f5b-968c2c66effe

import Mathlib
import Definitions.Def_SuttonTD_Convergence_ExpectedVisits

set_option autoImplicit false

open Filter Topology Matrix

namespace Pvba842610

open SuttonTD.Convergence

lemma sum_pi_succ {N : Type*} [Fintype N] (m : ℕ) (F : (Fin (m+1) → N) → ℝ) :
    ∑ s, F s = ∑ a : N, ∑ s' : Fin m → N, F (Fin.cons a s') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => N)) _ _ (fun _ => rfl)).symm

section
variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]

/-- row termination probability -/
noncomputable def ell (C : AbsorbingChain N T) (a : N) : ℝ := ∑ j, C.pT a j

lemma Q_apply (C : AbsorbingChain N T) (a k : N) : C.Q a k = C.pN a k := rfl

lemma E2_succ (C : AbsorbingChain N T) (m : ℕ) (a : N) :
    ∑ k, C.pN a k * (C.Q ^ m *ᵥ ell C) k = (C.Q ^ (m+1) *ᵥ ell C) a := by
  rw [pow_succ', ← mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Q_apply]

lemma sum_stepWeight (C : AbsorbingChain N T) (m : ℕ) (a : N) :
    ∑ s : Fin m → N, ∑ j, C.stepWeight a (List.ofFn s) j = (C.Q ^ m *ᵥ ell C) a := by
  induction m generalizing a with
  | zero => simp [AbsorbingChain.stepWeight, ell]
  | succ m ih =>
    rw [sum_pi_succ, ← E2_succ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, AbsorbingChain.stepWeight]
    simp_rw [← Finset.mul_sum, ← ih k]


lemma count_cons' (a i : N) (l : List N) :
    ((a :: l).count i : ℝ) = (if a = i then 1 else 0) + (l.count i : ℝ) := by
  by_cases h : a = i <;> simp [List.count_cons, h, add_comm]

/-- expected visits to `i` from `a`, with exactly `m` further nonterminal states -/
noncomputable def V (C : AbsorbingChain N T) (i : N) (m : ℕ) (a : N) : ℝ :=
  ∑ s : Fin m → N, ∑ j, C.stepWeight a (List.ofFn s) j * ((a :: List.ofFn s).count i : ℝ)

lemma V_zero (C : AbsorbingChain N T) (i a : N) :
    V C i 0 a = (if a = i then 1 else 0) * ell C a := by
  simp [V, AbsorbingChain.stepWeight, ell, count_cons', Finset.mul_sum, mul_comm]

lemma V_succ (C : AbsorbingChain N T) (i : N) (m : ℕ) (a : N) :
    V C i (m+1) a = (if a = i then 1 else 0) * (C.Q ^ (m+1) *ᵥ ell C) a
      + ∑ k, C.pN a k * V C i m k := by
  have hc : ∀ (k : N) (l : List N), ((a :: k :: l).count i : ℝ)
      = (if a = i then 1 else 0) + ((k :: l).count i : ℝ) := fun k l => count_cons' a i (k :: l)
  have h1 : V C i (m+1) a = ∑ k, ∑ s : Fin m → N, ∑ j, C.pN a k * (C.stepWeight k (List.ofFn s) j *
        (((a :: k :: List.ofFn s).count i : ℕ) : ℝ)) := by
    unfold V
    rw [sum_pi_succ]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, AbsorbingChain.stepWeight, mul_assoc]
  rw [h1]
  simp only [hc, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [← E2_succ]
    simp_rw [← sum_stepWeight, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl
      (fun j _ => by ring)))
  · unfold V
    simp only [Finset.mul_sum]

lemma V_closed (C : AbsorbingChain N T) (i : N) (m : ℕ) (a : N) :
    V C i m a = ∑ t ∈ Finset.range (m+1), (C.Q ^ (m - t)) a i * (C.Q ^ t *ᵥ ell C) i := by
  induction m generalizing a with
  | zero =>
    rw [V_zero]
    by_cases h : a = i
    · subst h; simp
    · simp [h, Matrix.one_apply]
  | succ m ih =>
    rw [V_succ, Finset.sum_range_succ]
    have h1 : (if a = i then (1:ℝ) else 0) * (C.Q ^ (m+1) *ᵥ ell C) a
        = (C.Q ^ (m + 1 - (m+1))) a i * (C.Q ^ (m+1) *ᵥ ell C) i := by
      by_cases h : a = i
      · subst h; simp
      · simp [h, Matrix.one_apply]
    rw [h1, add_comm]
    congr 1
    simp_rw [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have ht' : t ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [Nat.succ_sub ht', pow_succ', Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Q_apply]; ring

/-- weight of nonterminal paths of length `m+1` weighted by the number of visits to `i` -/
lemma W_eq (C : AbsorbingChain N T) (u : N → ℝ) (i : N) (m : ℕ) :
    ∑ s : Fin (m+1) → N, ∑ j, C.pathWeight u (List.ofFn s) j * ((List.ofFn s).count i : ℝ)
      = ∑ t ∈ Finset.range (m+1), (u ᵥ* C.Q ^ (m - t)) i * (C.Q ^ t *ᵥ ell C) i := by
  have h1 : ∑ s : Fin (m+1) → N, ∑ j, C.pathWeight u (List.ofFn s) j * ((List.ofFn s).count i : ℝ)
      = ∑ a, u a * V C i m a := by
    rw [sum_pi_succ]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold V
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, AbsorbingChain.pathWeight]
    ring
  rw [h1]
  simp_rw [V_closed, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

lemma hasSum_list_of_length {N T : Type*} [Fintype N] [Fintype T] (f : List N × T → ℝ)
    (hf : ∀ p, 0 ≤ f p) (a : ℝ)
    (h : HasSum (fun m : ℕ => ∑ s : Fin m → N, ∑ j, f (List.ofFn s, j)) a) : HasSum f a := by
  classical
  let e : List N × T ≃ (Σ m : ℕ, (Fin m → N) × T) :=
    (Equiv.prodCongr List.equivSigmaTuple (Equiv.refl T)).trans
      (Equiv.sigmaProdDistrib (fun m : ℕ => Fin m → N) T)
  let g : (Σ m : ℕ, (Fin m → N) × T) → ℝ := f ∘ e.symm
  have hg : ∀ m (s : Fin m → N) (j : T), g ⟨m, (s, j)⟩ = f (List.ofFn s, j) := fun m s j => rfl
  have hg0 : ∀ x, 0 ≤ g x := fun x => hf _
  have hfib : ∀ m : ℕ, ∑' y : (Fin m → N) × T, g ⟨m, y⟩
      = ∑ s : Fin m → N, ∑ j, f (List.ofFn s, j) := by
    intro m
    rw [tsum_fintype, Fintype.sum_prod_type]
    rfl
  have hsum : Summable g := by
    rw [summable_sigma_of_nonneg hg0]
    refine ⟨fun m => Summable.of_finite, ?_⟩
    simp_rw [hfib]
    exact h.summable
  have hg' : HasSum g a := by
    refine HasSum.sigma_of_hasSum (g := fun m : ℕ => ∑ s : Fin m → N, ∑ j, f (List.ofFn s, j)) h
      (fun m => ?_) hsum
    rw [← hfib m]
    exact (Summable.of_finite).hasSum
  exact (e.symm.hasSum_iff).mp hg'

lemma isUnit_one_sub (Q : Matrix N N ℝ) (hQ : Tendsto (fun n : ℕ => Q ^ n) atTop (𝓝 0)) :
    IsUnit (1 - Q) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  set x : N → ℝ := v - w with hx
  have h0 : (1 - Q) *ᵥ x = 0 := by
    rw [hx, mulVec_sub]; exact sub_eq_zero.mpr hvw
  have hQx : Q *ᵥ x = x := by
    rw [sub_mulVec, one_mulVec] at h0
    exact (sub_eq_zero.mp h0).symm
  have hpow : ∀ n : ℕ, Q ^ n *ᵥ x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← mulVec_mulVec, ih, hQx]
  have hlim : Tendsto (fun n : ℕ => Q ^ n *ᵥ x) atTop (𝓝 ((0 : Matrix N N ℝ) *ᵥ x)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp hQ
  simp only [hpow, zero_mulVec] at hlim
  have : x = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact sub_eq_zero.mp this

lemma partial_sums (Q : Matrix N N ℝ) (hQ : Tendsto (fun n : ℕ => Q ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑ t ∈ Finset.range n, Q ^ t) atTop (𝓝 (1 - Q)⁻¹) := by
  have hU := isUnit_one_sub Q hQ
  have hdet : IsUnit (1 - Q).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hS : ∀ n : ℕ, ∑ t ∈ Finset.range n, Q ^ t = (1 - Q ^ n) * (1 - Q)⁻¹ := by
    intro n
    rw [← geom_sum_mul_neg, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
  simp_rw [hS]
  have h1 := ((tendsto_const_nhds (x := (1 : Matrix N N ℝ))).sub hQ).mul_const ((1 - Q)⁻¹)
  simpa using h1

lemma Qpow_nonneg (C : AbsorbingChain N T) (t : ℕ) (a b : N) : 0 ≤ (C.Q ^ t) a b := by
  induction t generalizing a with
  | zero => by_cases h : a = b <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (C.pN_nonneg a k) (ih k))

lemma ell_nonneg (C : AbsorbingChain N T) (a : N) : 0 ≤ ell C a :=
  Finset.sum_nonneg (fun j _ => C.pT_nonneg a j)

lemma ell_eq (C : AbsorbingChain N T) : ell C = (1 - C.Q) *ᵥ (fun _ => (1 : ℝ)) := by
  funext a
  have := C.row_sum a
  simp only [ell, Matrix.mulVec, dotProduct, mul_one, Matrix.sub_apply, Matrix.one_apply,
    Finset.sum_sub_distrib, Q_apply]
  simp
  linarith

lemma ell_series (C : AbsorbingChain N T) (i : N) : ((1 - C.Q)⁻¹ *ᵥ ell C) i = 1 := by
  have hdet : IsUnit (1 - C.Q).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub C.Q C.absorbing)
  rw [ell_eq, mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]

lemma hasSum_of_lin (C : AbsorbingChain N T) (φ : Matrix N N ℝ →+ ℝ) (hφ : Continuous φ)
    (hnn : ∀ t : ℕ, 0 ≤ φ (C.Q ^ t)) : HasSum (fun t : ℕ => φ (C.Q ^ t)) (φ (1 - C.Q)⁻¹) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have := (hφ.tendsto _).comp (partial_sums C.Q C.absorbing)
  simpa [Function.comp_def, map_sum] using this

lemma pathWeight_nonneg (C : AbsorbingChain N T) (μ : N → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    ∀ (l : List N) (j : T), 0 ≤ C.pathWeight μ l j := by
  have hs : ∀ (l : List N) (a : N) (j : T), 0 ≤ C.stepWeight a l j := by
    intro l
    induction l with
    | nil => intro a j; exact C.pT_nonneg a j
    | cons k rest ih => intro a j; exact mul_nonneg (C.pN_nonneg a k) (ih k j)
  intro l j
  cases l with
  | nil => exact le_refl _
  | cons a rest => exact mul_nonneg (hμ a) (hs rest a j)

lemma main (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (i : N) :
    HasSum (fun p : List N × T => C.pathWeight μ p.1 p.2 * (p.1.count i : ℝ))
      ((μ ᵥ* (1 - C.Q)⁻¹) i) := by
  set d : ℝ := (μ ᵥ* (1 - C.Q)⁻¹) i with hd
  let φa : Matrix N N ℝ →+ ℝ := AddMonoidHom.mk' (fun M => (μ ᵥ* M) i) (by
    intro M M'; simp [Matrix.vecMul_add])
  let φb : Matrix N N ℝ →+ ℝ := AddMonoidHom.mk' (fun M => (M *ᵥ ell C) i) (by
    intro M M'; simp [Matrix.add_mulVec])
  have hca : Continuous φa := by
    show Continuous (fun M : Matrix N N ℝ => (μ ᵥ* M) i)
    simp only [Matrix.vecMul, dotProduct]
    fun_prop
  have hcb : Continuous φb := by
    show Continuous (fun M : Matrix N N ℝ => (M *ᵥ ell C) i)
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hna : ∀ t : ℕ, 0 ≤ φa (C.Q ^ t) := fun t =>
    Finset.sum_nonneg (fun a _ => mul_nonneg (hμ0 a) (Qpow_nonneg C t a i))
  have hnb : ∀ t : ℕ, 0 ≤ φb (C.Q ^ t) := fun t =>
    Finset.sum_nonneg (fun a _ => mul_nonneg (Qpow_nonneg C t i a) (ell_nonneg C a))
  have hA := hasSum_of_lin C φa hca hna
  have hB := hasSum_of_lin C φb hcb hnb
  have hB1 : φb (1 - C.Q)⁻¹ = 1 := ell_series C i
  rw [hB1] at hB
  have hAn : Summable (fun t : ℕ => ‖φa (C.Q ^ t)‖) := by
    simpa [Real.norm_of_nonneg (hna _)] using hA.summable
  have hBn : Summable (fun t : ℕ => ‖φb (C.Q ^ t)‖) := by
    simpa [Real.norm_of_nonneg (hnb _)] using hB.summable
  have hcauchy := hasSum_sum_range_mul_of_summable_norm hBn hAn
  rw [hB.tsum_eq, hA.tsum_eq, one_mul] at hcauchy
  have hfib : HasSum (fun m : ℕ => ∑ s : Fin (m+1) → N, ∑ j,
      C.pathWeight μ (List.ofFn s) j * ((List.ofFn s).count i : ℝ)) d := by
    have hfun : (fun m : ℕ => ∑ s : Fin (m+1) → N, ∑ j,
        C.pathWeight μ (List.ofFn s) j * ((List.ofFn s).count i : ℝ))
        = fun m : ℕ => ∑ k ∈ Finset.range (m+1), φb (C.Q ^ k) * φa (C.Q ^ (m - k)) := by
      funext m
      rw [W_eq]
      exact Finset.sum_congr rfl (fun t _ => mul_comm _ _)
    rw [hfun]
    exact hcauchy
  refine hasSum_list_of_length _
    (fun p => mul_nonneg (pathWeight_nonneg C μ hμ0 _ _) (Nat.cast_nonneg _)) d ?_
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa [AbsorbingChain.pathWeight] using hfib

end
end Pvba842610

open Filter Topology Matrix SuttonTD.Convergence in
theorem solution {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]
    (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) (i : N) :
    HasSum (fun p : List N × T => C.pathWeight μ p.1 p.2 * (p.1.count i : ℝ))
      ((μ ᵥ* (1 - C.Q)⁻¹) i) := by
  exact Pvba842610.main C μ hμ0 i
