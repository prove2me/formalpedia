-- Prove2me | solution 1 for SuttonTD.Convergence.expected_update
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T16:34:09.499619+00:00
-- url     : https://prove2.me/submissions/a7eb2d1e-feff-4670-a3ce-d7a8689398b1

import Mathlib
import Definitions.Def_SuttonTD_Convergence_ExpectedVisits
import Definitions.Def_SuttonTD_Convergence_EpisodeStream
import Definitions.Def_SuttonTD_Convergence_LinearTD0

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

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

namespace Pvb19c043e
open SuttonTD.Convergence

section comb
variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]

/-- number of adjacent pairs `(a, b)` in a list -/
def tr (a b : N) : List N → ℕ
  | [] => 0
  | [_] => 0
  | i :: k :: rest => (if i = a ∧ k = b then 1 else 0) + tr a b (k :: rest)

lemma tr_le_count (a b : N) : ∀ s : List N, tr a b s ≤ s.count a
  | [] => by simp [tr]
  | [_] => by simp [tr]
  | i :: k :: rest => by
    have ih := tr_le_count a b (k :: rest)
    rw [tr, List.count_cons]
    by_cases h : i = a
    · subst h; simp; split_ifs <;> omega
    · simp [h]; omega

lemma hasSum_cons_split {g : List N × T → ℝ} {S : N → ℝ}
    (h : ∀ k, HasSum (fun p : List N × T => g (k :: p.1, p.2)) (S k)) :
    HasSum g (∑ j, g ([], j) + ∑ k, S k) := by
  classical
  let f0 : List N × T → ℝ := fun p => if p.1 = [] then g p else 0
  let fk : N → List N × T → ℝ := fun k p => if p.1.head? = some k then g p else 0
  have h0 : HasSum f0 (∑ j, g ([], j)) := by
    have hinj : Function.Injective (fun j : T => (([] : List N), j)) := fun a b h => by
      simpa using h
    rw [← hinj.hasSum_iff]
    · have : f0 ∘ (fun j : T => (([] : List N), j)) = fun j => g ([], j) := by
        funext j; simp [f0]
      rw [this]; exact hasSum_fintype _
    · intro p hp
      simp only [f0]
      split_ifs with h1
      · exact absurd ⟨p.2, by ext <;> simp [h1]⟩ hp
      · rfl
  have hk : ∀ k, HasSum (fk k) (S k) := by
    intro k
    have hinj : Function.Injective (fun p : List N × T => (k :: p.1, p.2)) := fun a b h => by
      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h
      exact Prod.ext h.1 h.2
    rw [← hinj.hasSum_iff]
    · have : fk k ∘ (fun p : List N × T => (k :: p.1, p.2)) = fun p => g (k :: p.1, p.2) := by
        funext p; simp [fk]
      rw [this]; exact h k
    · intro p hp
      simp only [fk]
      split_ifs with h1
      · exfalso; apply hp
        obtain ⟨l, t⟩ := p
        cases l with
        | nil => simp at h1
        | cons c l => simp at h1; subst h1; exact ⟨(l, t), rfl⟩
      · rfl
  have hsum := h0.add (hasSum_sum (s := Finset.univ) (fun k _ => hk k))
  convert hsum using 1
  funext p
  obtain ⟨l, t⟩ := p
  cases l with
  | nil => simp [f0, fk]
  | cons c l => simp [f0, fk]

lemma stepWeight_nonneg (C : AbsorbingChain N T) :
    ∀ (l : List N) (a : N) (j : T), 0 ≤ C.stepWeight a l j := by
  intro l
  induction l with
  | nil => intro a j; exact C.pT_nonneg a j
  | cons k rest ih => intro a j; exact mul_nonneg (C.pN_nonneg a k) (ih k j)

lemma cons_inj (k : N) : Function.Injective (fun p : List N × T => (k :: p.1, p.2)) :=
  fun a b h => by
    simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h
    exact Prod.ext h.1 h.2

lemma summable_count (C : AbsorbingChain N T) (i c : N) :
    Summable (fun p : List N × T => C.stepWeight i p.1 p.2 * ((i :: p.1).count c : ℝ)) := by
  have hm := (Pvba842610.main C (Pi.single i 1) (fun k => by
    by_cases h : k = i <;> simp [Pi.single_apply, h]) c).summable
  refine (hm.comp_injective (cons_inj i)).congr (fun p => ?_)
  simp [Function.comp, AbsorbingChain.pathWeight]

/-- summability of a nonneg functional from the start state `i` -/
lemma summable_from (C : AbsorbingChain N T) (i c c' : N) (f : List N × T → ℝ)
    (h0 : ∀ p, 0 ≤ f p)
    (hle : ∀ (v : List N) (j : T), f (i :: v, j) ≤ ((i :: v).count c : ℝ) + ((i :: v).count c' : ℝ)) :
    Summable (fun p : List N × T => C.stepWeight i p.1 p.2 * f (i :: p.1, p.2)) := by
  have hc := (summable_count C i c).add (summable_count C i c')
  refine Summable.of_nonneg_of_le (fun p => mul_nonneg (stepWeight_nonneg C _ _ _) (h0 _))
    (fun p => ?_) hc
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (hle _ _) (stepWeight_nonneg C _ _ _)

/-- first-step decomposition -/
lemma first_step (C : AbsorbingChain N T) (i : N) (f : List N × T → ℝ)
    (hk : ∀ k, Summable (fun p : List N × T => C.stepWeight k p.1 p.2 * f (i :: k :: p.1, p.2))) :
    HasSum (fun p : List N × T => C.stepWeight i p.1 p.2 * f (i :: p.1, p.2))
      (∑ j, C.pT i j * f ([i], j) + ∑ k, C.pN i k *
        ∑' p : List N × T, C.stepWeight k p.1 p.2 * f (i :: k :: p.1, p.2)) := by
  have hk' : ∀ k, HasSum (fun p : List N × T =>
      C.stepWeight i (k :: p.1) p.2 * f (i :: k :: p.1, p.2))
      (C.pN i k * ∑' p : List N × T, C.stepWeight k p.1 p.2 * f (i :: k :: p.1, p.2)) := by
    intro k
    have h2 : (fun p : List N × T => C.stepWeight i (k :: p.1) p.2 * f (i :: k :: p.1, p.2))
        = fun p => C.pN i k * (C.stepWeight k p.1 p.2 * f (i :: k :: p.1, p.2)) := by
      funext p; simp only [AbsorbingChain.stepWeight]; ring
    rw [h2]
    exact (hk k).hasSum.mul_left _
  have := hasSum_cons_split (g := fun p : List N × T => C.stepWeight i p.1 p.2 * f (i :: p.1, p.2))
    hk'
  simpa [AbsorbingChain.stepWeight] using this

end comb
end Pvb19c043e

namespace Pvb19c043e
open SuttonTD.Convergence

section comb2
variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]

lemma uniq (C : AbsorbingChain N T) (x y r : N → ℝ)
    (hx : ∀ i, x i = r i + ∑ k, C.pN i k * x k) (hy : ∀ i, y i = r i + ∑ k, C.pN i k * y k) :
    x = y := by
  have hU := Pvba842610.isUnit_one_sub C.Q C.absorbing
  rw [← Matrix.mulVec_injective_iff_isUnit] at hU
  have h0 : (1 - C.Q) *ᵥ (x - y) = (1 - C.Q) *ᵥ 0 := by
    funext i
    have h1 := hx i
    have h2 := hy i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.mulVec_zero,
      Pi.zero_apply]
    simp only [Matrix.mulVec, dotProduct, Pvba842610.Q_apply, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib]
    linarith
  have := hU h0
  exact sub_eq_zero.mp this

/-- mass from `i` -/
noncomputable def Mv (C : AbsorbingChain N T) (i : N) : ℝ :=
  ∑' p : List N × T, C.stepWeight i p.1 p.2 * (fun _ : List N × T => (1 : ℝ)) (i :: p.1, p.2)

/-- expected visits to `a` from `i` -/
noncomputable def Vv (C : AbsorbingChain N T) (a i : N) : ℝ :=
  ∑' p : List N × T, C.stepWeight i p.1 p.2 *
    (fun q : List N × T => (q.1.count a : ℝ)) (i :: p.1, p.2)

/-- expected `(a,b)` transitions from `i` -/
noncomputable def Uv (C : AbsorbingChain N T) (a b i : N) : ℝ :=
  ∑' p : List N × T, C.stepWeight i p.1 p.2 *
    (fun q : List N × T => (tr a b q.1 : ℝ)) (i :: p.1, p.2)

/-- probability (from `i`) that the last state is `a` and the terminal state is `j0` -/
noncomputable def Lv [DecidableEq T] (C : AbsorbingChain N T) (a : N) (j0 : T) (i : N) : ℝ :=
  ∑' p : List N × T, C.stepWeight i p.1 p.2 *
    (fun q : List N × T => if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0) (i :: p.1, p.2)

lemma count_le_one_add (a k : N) (v : List N) :
    (((k :: v).count a : ℕ) : ℝ) ≤ ((k :: v).count a : ℝ) + ((k :: v).count k : ℝ) := by
  have : (0 : ℝ) ≤ ((k :: v).count k : ℝ) := Nat.cast_nonneg _
  linarith

lemma one_le_count_self (k : N) (v : List N) : (1 : ℝ) ≤ ((k :: v).count k : ℝ) := by
  have : 1 ≤ (k :: v).count k := by simp [List.count_cons]
  exact_mod_cast this

lemma sM (C : AbsorbingChain N T) (k : N) :
    Summable (fun p : List N × T => C.stepWeight k p.1 p.2 *
      (fun _ : List N × T => (1 : ℝ)) (k :: p.1, p.2)) :=
  summable_from C k k k (fun _ : List N × T => (1 : ℝ)) (fun _ => zero_le_one) (fun v j => by
    have := one_le_count_self k v
    have h0 : (0 : ℝ) ≤ ((k :: v).count k : ℝ) := Nat.cast_nonneg _
    beta_reduce; linarith)

lemma sV (C : AbsorbingChain N T) (a k : N) :
    Summable (fun p : List N × T => C.stepWeight k p.1 p.2 *
      (fun q : List N × T => (q.1.count a : ℝ)) (k :: p.1, p.2)) :=
  summable_from C k a k (fun q : List N × T => (q.1.count a : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun v j => count_le_one_add a k v)

lemma sU (C : AbsorbingChain N T) (a b k : N) :
    Summable (fun p : List N × T => C.stepWeight k p.1 p.2 *
      (fun q : List N × T => (tr a b q.1 : ℝ)) (k :: p.1, p.2)) :=
  summable_from C k a k (fun q : List N × T => (tr a b q.1 : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun v j => by
    have h1 : (tr a b (k :: v) : ℝ) ≤ ((k :: v).count a : ℝ) := by
      exact_mod_cast tr_le_count a b (k :: v)
    have h0 : (0 : ℝ) ≤ ((k :: v).count k : ℝ) := Nat.cast_nonneg _
    simp only; linarith)

lemma last_le_count (a : N) (l : List N) (h : l.getLast? = some a) : (1 : ℝ) ≤ (l.count a : ℝ) := by
  have hm : a ∈ l := List.mem_of_getLast? h
  have : 0 < l.count a := List.count_pos_iff.mpr hm
  exact_mod_cast this

lemma sL [DecidableEq T] (C : AbsorbingChain N T) (a : N) (j0 : T) (k : N) :
    Summable (fun p : List N × T => C.stepWeight k p.1 p.2 *
      (fun q : List N × T => if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0)
        (k :: p.1, p.2)) :=
  summable_from C k a k
    (fun q : List N × T => if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num) (fun v j => by
    have h0 : (0 : ℝ) ≤ ((k :: v).count k : ℝ) := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ ((k :: v).count a : ℝ) := Nat.cast_nonneg _
    simp only
    split_ifs with h
    · have := last_le_count a (k :: v) h.1; linarith
    · linarith)

lemma Mv_eq (C : AbsorbingChain N T) (i : N) : Mv C i = 1 := by
  have hrec : ∀ i, Mv C i = Pvba842610.ell C i + ∑ k, C.pN i k * Mv C k := by
    intro i
    have := (first_step C i (fun _ => (1 : ℝ)) (fun k => sM C k)).tsum_eq
    rw [Mv, this]
    simp [Pvba842610.ell, Mv]
  have h1 : ∀ i, (fun _ : N => (1 : ℝ)) i = Pvba842610.ell C i + ∑ k, C.pN i k * (fun _ => (1:ℝ)) k := by
    intro i
    have := C.row_sum i
    simp only [Pvba842610.ell, mul_one]
    linarith
  exact congrFun (uniq C (Mv C) (fun _ => 1) (Pvba842610.ell C) hrec h1) i

lemma Vv_rec (C : AbsorbingChain N T) (a i : N) :
    Vv C a i = (if i = a then 1 else 0) + ∑ k, C.pN i k * Vv C a k := by
  have := (first_step C i (fun q : List N × T => (q.1.count a : ℝ)) (fun k => by
    have h : (fun p : List N × T => C.stepWeight k p.1 p.2 *
        (fun q : List N × T => (q.1.count a : ℝ)) (i :: k :: p.1, p.2)) =
        fun p => (if i = a then 1 else 0) * (C.stepWeight k p.1 p.2 *
          (fun _ : List N × T => (1 : ℝ)) (k :: p.1, p.2)) + C.stepWeight k p.1 p.2 *
          (fun q : List N × T => (q.1.count a : ℝ)) (k :: p.1, p.2) := by
      funext p; simp only [Pvba842610.count_cons' i a (k :: p.1)]; ring
    rw [h]; exact ((sM C k).mul_left _).add (sV C a k))).tsum_eq
  rw [Vv, this]
  have hin : ∀ k, ∑' p : List N × T, C.stepWeight k p.1 p.2 *
      (fun q : List N × T => (q.1.count a : ℝ)) (i :: k :: p.1, p.2) =
      (if i = a then 1 else 0) + Vv C a k := by
    intro k
    have h : (fun p : List N × T => C.stepWeight k p.1 p.2 *
        (fun q : List N × T => (q.1.count a : ℝ)) (i :: k :: p.1, p.2)) =
        fun p => (if i = a then 1 else 0) * (C.stepWeight k p.1 p.2 *
          (fun _ : List N × T => (1 : ℝ)) (k :: p.1, p.2)) + C.stepWeight k p.1 p.2 *
          (fun q : List N × T => (q.1.count a : ℝ)) (k :: p.1, p.2) := by
      funext p; simp only [Pvba842610.count_cons' i a (k :: p.1)]; ring
    rw [h, ((sM C k).mul_left _).tsum_add (sV C a k), tsum_mul_left]
    rw [show (∑' p : List N × T, C.stepWeight k p.1 p.2 *
      (fun _ : List N × T => (1 : ℝ)) (k :: p.1, p.2)) = Mv C k from rfl, Mv_eq, mul_one]
    rfl
  simp only [hin, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hr := C.row_sum i
  simp only [Pvba842610.count_cons', List.count_nil, Nat.cast_zero, add_zero]
  by_cases h : i = a
  · simp [h] at hr ⊢; linarith
  · simp [h]

end comb2
end Pvb19c043e

namespace Pvb19c043e
open SuttonTD.Convergence

section comb3
variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]

lemma Uv_rec (C : AbsorbingChain N T) (a b i : N) :
    Uv C a b i = (if i = a then C.pN a b else 0) + ∑ k, C.pN i k * Uv C a b k := by
  have hfun : ∀ k, (fun p : List N × T => C.stepWeight k p.1 p.2 *
      (fun q : List N × T => (tr a b q.1 : ℝ)) (i :: k :: p.1, p.2)) =
      fun p => (if i = a ∧ k = b then 1 else 0) * (C.stepWeight k p.1 p.2 *
        (fun _ : List N × T => (1 : ℝ)) (k :: p.1, p.2)) + C.stepWeight k p.1 p.2 *
        (fun q : List N × T => (tr a b q.1 : ℝ)) (k :: p.1, p.2) := by
    intro k; funext p
    simp only [tr]
    push_cast
    ring
  have := (first_step C i (fun q : List N × T => (tr a b q.1 : ℝ)) (fun k => by
    rw [hfun k]; exact ((sM C k).mul_left _).add (sU C a b k))).tsum_eq
  rw [Uv, this]
  have hin : ∀ k, ∑' p : List N × T, C.stepWeight k p.1 p.2 *
      (fun q : List N × T => (tr a b q.1 : ℝ)) (i :: k :: p.1, p.2) =
      (if i = a ∧ k = b then 1 else 0) + Uv C a b k := by
    intro k
    rw [hfun k, ((sM C k).mul_left _).tsum_add (sU C a b k), tsum_mul_left]
    rw [show (∑' p : List N × T, C.stepWeight k p.1 p.2 *
      (fun _ : List N × T => (1 : ℝ)) (k :: p.1, p.2)) = Mv C k from rfl, Mv_eq, mul_one]
    rfl
  simp only [hin, mul_add, Finset.sum_add_distrib]
  simp only [tr, Nat.cast_zero, mul_zero, Finset.sum_const_zero, zero_add]
  by_cases h : i = a
  · subst h; simp
  · simp [h]

lemma Lv_rec [DecidableEq T] (C : AbsorbingChain N T) (a : N) (j0 : T) (i : N) :
    Lv C a j0 i = (if i = a then C.pT a j0 else 0) + ∑ k, C.pN i k * Lv C a j0 k := by
  have hfun : ∀ k, (fun p : List N × T => C.stepWeight k p.1 p.2 *
      (fun q : List N × T => if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0)
        (i :: k :: p.1, p.2)) =
      fun p => C.stepWeight k p.1 p.2 *
      (fun q : List N × T => if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0)
        (k :: p.1, p.2) := by
    intro k; funext p
    simp only [List.getLast?_cons_cons]
  have := (first_step C i (fun q : List N × T =>
      if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0) (fun k => by
    rw [hfun k]; exact sL C a j0 k)).tsum_eq
  rw [Lv, this]
  simp only [hfun]
  congr 1
  by_cases h : i = a
  · subst h; simp
  · simp [h]

lemma Uv_eq (C : AbsorbingChain N T) (a b : N) : Uv C a b = fun i => C.pN a b * Vv C a i := by
  refine uniq C _ _ (fun i => if i = a then C.pN a b else 0) (Uv_rec C a b) (fun i => ?_)
  beta_reduce
  rw [Vv_rec C a i, mul_add, Finset.mul_sum]
  congr 1
  · split_ifs <;> simp
  · exact Finset.sum_congr rfl (fun k _ => by ring)

lemma Lv_eq [DecidableEq T] (C : AbsorbingChain N T) (a : N) (j0 : T) :
    Lv C a j0 = fun i => C.pT a j0 * Vv C a i := by
  refine uniq C _ _ (fun i => if i = a then C.pT a j0 else 0) (Lv_rec C a j0) (fun i => ?_)
  beta_reduce
  rw [Vv_rec C a i, mul_add, Finset.mul_sum]
  congr 1
  · split_ifs <;> simp
  · exact Finset.sum_congr rfl (fun k _ => by ring)

lemma top (C : AbsorbingChain N T) (μ : N → ℝ) (f : List N × T → ℝ)
    (hk : ∀ k, Summable (fun p : List N × T => C.stepWeight k p.1 p.2 * f (k :: p.1, p.2))) :
    HasSum (fun q : List N × T => C.pathWeight μ q.1 q.2 * f q)
      (∑ k, μ k * ∑' p : List N × T, C.stepWeight k p.1 p.2 * f (k :: p.1, p.2)) := by
  have := hasSum_cons_split (g := fun q : List N × T => C.pathWeight μ q.1 q.2 * f q)
    (S := fun k => μ k * ∑' p : List N × T, C.stepWeight k p.1 p.2 * f (k :: p.1, p.2))
    (fun k => by
      have h := (hk k).hasSum.mul_left (μ k)
      show HasSum (fun p : List N × T => C.pathWeight μ (k :: p.1) p.2 * f (k :: p.1, p.2)) _
      simp only [AbsorbingChain.pathWeight, mul_assoc]
      exact h)
  simpa [AbsorbingChain.pathWeight] using this

lemma d_eq (C : AbsorbingChain N T) (μ : N → ℝ) (a : N) :
    C.expectedVisits μ a = ∑ k, μ k * Vv C a k :=
  (top C μ (fun q : List N × T => (q.1.count a : ℝ)) (sV C a)).tsum_eq

lemma hasSum_tr (C : AbsorbingChain N T) (μ : N → ℝ) (a b : N) :
    HasSum (fun q : List N × T => C.pathWeight μ q.1 q.2 * (tr a b q.1 : ℝ))
      (C.expectedVisits μ a * C.pN a b) := by
  have h := top C μ (fun q : List N × T => (tr a b q.1 : ℝ)) (sU C a b)
  have e : (∑ k, μ k * ∑' p : List N × T, C.stepWeight k p.1 p.2 *
      (fun q : List N × T => (tr a b q.1 : ℝ)) (k :: p.1, p.2)) =
      C.expectedVisits μ a * C.pN a b := by
    rw [d_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (∑' p : List N × T, C.stepWeight k p.1 p.2 *
      (fun q : List N × T => (tr a b q.1 : ℝ)) (k :: p.1, p.2)) = Uv C a b k from rfl, Uv_eq]
    ring
  rw [e] at h; exact h

lemma hasSum_last [DecidableEq T] (C : AbsorbingChain N T) (μ : N → ℝ) (a : N) (j0 : T) :
    HasSum (fun q : List N × T => C.pathWeight μ q.1 q.2 *
        (if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0))
      (C.expectedVisits μ a * C.pT a j0) := by
  have h := top C μ (fun q : List N × T =>
    if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0) (sL C a j0)
  have e : (∑ k, μ k * ∑' p : List N × T, C.stepWeight k p.1 p.2 *
      (fun q : List N × T => if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0)
        (k :: p.1, p.2)) = C.expectedVisits μ a * C.pT a j0 := by
    rw [d_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (∑' p : List N × T, C.stepWeight k p.1 p.2 *
      (fun q : List N × T => if q.1.getLast? = some a ∧ q.2 = j0 then (1 : ℝ) else 0)
        (k :: p.1, p.2)) = Lv C a j0 k from rfl, Lv_eq]
    ring
  rw [e] at h; exact h

end comb3
end Pvb19c043e

namespace Pvb19c043e
open SuttonTD.Convergence MeasureTheory ProbabilityTheory

section prob
variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]

lemma mset_pt (S : Set (List N × T)) :
    MeasurableSet {ep : Episode N T | (ep.path, ep.term) ∈ S} := by
  have h : MeasurableSpace.comap (fun ep : Episode N T => (ep.path, ep.term)) ⊤ ≤
      Episode.instMeasurableSpace N T := le_sup_left
  exact h _ ⟨S, MeasurableSpace.measurableSet_top, rfl⟩

lemma meas_pt {β : Type*} [MeasurableSpace β] (f : List N × T → β) :
    Measurable (fun ep : Episode N T => f (ep.path, ep.term)) :=
  fun s _ => mset_pt (f ⁻¹' s)

lemma meas_out : Measurable (fun ep : Episode N T => ep.out) := by
  have h : MeasurableSpace.comap (fun ep : Episode N T => ep.out) (borel ℝ) ≤
      Episode.instMeasurableSpace N T := le_sup_right
  exact Measurable.of_comap_le h

variable {Ω : Type*} [MeasurableSpace Ω]

lemma lint_master (C : AbsorbingChain N T) (μ : N → ℝ) (ν : T → Measure ℝ) (P : Measure Ω)
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e) (n : ℕ)
    (g : List N × T → ENNReal) (B : Set ℝ) (hB : MeasurableSet B) :
    ∫⁻ ω, g ((e n ω).path, (e n ω).term) * B.indicator 1 (e n ω).out ∂P =
      ∑' q : List N × T, g q * (ENNReal.ofReal (C.pathWeight μ q.1 q.2) * ν q.2 B) := by
  let A : List N × T → Set Ω :=
    fun q => {ω | (e n ω).path = q.1 ∧ (e n ω).term = q.2 ∧ (e n ω).out ∈ B}
  have hA : ∀ q, MeasurableSet (A q) := by
    intro q
    have h1 : MeasurableSet {ep : Episode N T | (ep.path, ep.term) ∈ ({q} : Set (List N × T))} :=
      mset_pt _
    have h2 : MeasurableSet {ep : Episode N T | ep.out ∈ B} := meas_out hB
    have := (he.1 n) (h1.inter h2)
    convert this using 1
    ext ω
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff,
      Prod.ext_iff, and_assoc]
  have hpt : ∀ ω, g ((e n ω).path, (e n ω).term) * B.indicator 1 (e n ω).out =
      ∑' q, (A q).indicator (fun _ => g q) ω := by
    intro ω
    rw [tsum_eq_single ((e n ω).path, (e n ω).term)]
    · by_cases hb : (e n ω).out ∈ B
      · simp [A, hb, Set.indicator_apply]
      · simp [A, hb, Set.indicator_apply]
    · intro q hq
      apply Set.indicator_of_notMem
      rintro ⟨h1, h2, -⟩
      exact hq (Prod.ext h1.symm h2.symm)
  simp_rw [hpt]
  rw [lintegral_tsum (fun q => (measurable_const.indicator (hA q)).aemeasurable)]
  refine tsum_congr (fun q => ?_)
  rw [lintegral_indicator_const (hA q)]
  exact congrArg _ (he.2.2 n q.1 q.2 B hB)

lemma law (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (P : Measure Ω)
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e) (n : ℕ)
    (f : List N × T → ℝ) (hf : ∀ q, 0 ≤ f q) (c : ℝ)
    (hc : HasSum (fun q : List N × T => C.pathWeight μ q.1 q.2 * f q) c) :
    Integrable (fun ω => f ((e n ω).path, (e n ω).term)) P ∧
      ∫ ω, f ((e n ω).path, (e n ω).term) ∂P = c := by
  have hm : Measurable (fun ω => f ((e n ω).path, (e n ω).term)) := (meas_pt f).comp (he.1 n)
  have hpw := Pvba842610.pathWeight_nonneg C μ hμ0
  have hL : ∫⁻ ω, ENNReal.ofReal (f ((e n ω).path, (e n ω).term)) ∂P = ENNReal.ofReal c := by
    have := lint_master C μ ν P e he n (fun q => ENNReal.ofReal (f q)) Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, mul_one, measure_univ] at this
    rw [this, ← hc.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun q => mul_nonneg (hpw _ _) (hf q)) hc.summable]
    refine tsum_congr (fun q => ?_)
    rw [ENNReal.ofReal_mul (hpw _ _), mul_comm]
  have hc0 : 0 ≤ c := hc.nonneg (fun q => mul_nonneg (hpw _ _) (hf q))
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun ω => hf _)), hL]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => hf _)) hm.aestronglyMeasurable,
      hL, ENNReal.toReal_ofReal hc0]

lemma out_lemma (C : AbsorbingChain N T) (μ : N → ℝ)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (hν : ∀ j, Integrable id (ν j))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e) (n : ℕ)
    (S : Set (List N × T)) (j0 : T) (hS : ∀ q ∈ S, q.2 = j0) :
    Integrable ({ω | ((e n ω).path, (e n ω).term) ∈ S}.indicator (fun ω => (e n ω).out)) P ∧
      ∫ ω, {ω | ((e n ω).path, (e n ω).term) ∈ S}.indicator (fun ω => (e n ω).out) ω ∂P =
        (P {ω | ((e n ω).path, (e n ω).term) ∈ S}).toReal * ∫ z, z ∂ν j0 := by
  set A : Set Ω := {ω | ((e n ω).path, (e n ω).term) ∈ S} with hAdef
  have hA : MeasurableSet A := (he.1 n) (mset_pt S)
  have hout : Measurable (fun ω => (e n ω).out) := meas_out.comp (he.1 n)
  have key : ∀ B, MeasurableSet B →
      P (A ∩ (fun ω => (e n ω).out) ⁻¹' B) = P A * ν j0 B := by
    intro B hB
    have h1 := lint_master C μ ν P e he n (S.indicator 1) B hB
    have h2 := lint_master C μ ν P e he n (S.indicator 1) Set.univ MeasurableSet.univ
    have e1 : ∫⁻ ω, S.indicator 1 ((e n ω).path, (e n ω).term) * B.indicator 1 (e n ω).out ∂P =
        P (A ∩ (fun ω => (e n ω).out) ⁻¹' B) := by
      rw [← lintegral_indicator_one (hA.inter (hout hB))]
      refine lintegral_congr (fun ω => ?_)
      by_cases h1 : ((e n ω).path, (e n ω).term) ∈ S <;>
        by_cases h2 : (e n ω).out ∈ B <;>
        simp [Set.indicator_apply, h1, h2, hAdef]
    have e2 : ∫⁻ ω, S.indicator 1 ((e n ω).path, (e n ω).term) *
        (Set.univ : Set ℝ).indicator 1 (e n ω).out ∂P = P A := by
      rw [← lintegral_indicator_one hA]
      refine lintegral_congr (fun ω => ?_)
      by_cases h1 : ((e n ω).path, (e n ω).term) ∈ S <;>
        simp [Set.indicator_apply, h1, hAdef]
    rw [← e1, h1, ← e2, h2, ← ENNReal.tsum_mul_right]
    refine tsum_congr (fun q => ?_)
    by_cases hq : q ∈ S
    · simp [Set.indicator_of_mem hq, hS q hq, mul_assoc]
    · simp [Set.indicator_of_notMem hq]
  have hmap : Measure.map (fun ω => (e n ω).out) (P.restrict A) = P A • ν j0 := by
    ext B hB
    rw [Measure.map_apply hout hB, Measure.restrict_apply (hout hB), Set.inter_comm, key B hB,
      Measure.smul_apply, smul_eq_mul]
  have hPA : P A ≠ ⊤ := measure_ne_top P A
  have hint : Integrable id (P A • ν j0) := (hν j0).smul_measure hPA
  have hint' : Integrable (fun ω => (e n ω).out) (P.restrict A) := by
    rw [← hmap] at hint
    exact (integrable_map_measure aestronglyMeasurable_id hout.aemeasurable).mp hint
  refine ⟨(integrable_indicator_iff hA).mpr hint', ?_⟩
  rw [integral_indicator hA]
  have := integral_map (μ := P.restrict A) hout.aemeasurable (f := id) aestronglyMeasurable_id
  rw [hmap, integral_smul_measure] at this
  simpa [smul_eq_mul] using this.symm

/-- the past σ-algebra -/
noncomputable def Mpast (e : ℕ → Ω → Episode N T) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Iio m, MeasurableSpace.comap (e i) inferInstance

lemma Mpast_mono (e : ℕ → Ω → Episode N T) (m : ℕ) : Mpast e m ≤ Mpast e (m + 1) :=
  biSup_mono (fun i (hi : i < m) => Nat.lt_succ_of_lt hi)

lemma Mpast_le (e : ℕ → Ω → Episode N T) (he : ∀ n, Measurable (e n)) (m : ℕ) :
    Mpast e m ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le (fun i _ => (he i).comap_le)

lemma meas_e_past (e : ℕ → Ω → Episode N T) (i m : ℕ) (h : i < m) :
    Measurable[Mpast e m] (e i) :=
  (comap_measurable (e i)).mono
    (le_iSup₂ (f := fun i (_ : i ∈ Set.Iio m) => MeasurableSpace.comap (e i) inferInstance) i h)
    le_rfl

lemma indep_cur (C : AbsorbingChain N T) (μ : N → ℝ) (ν : T → Measure ℝ) (P : Measure Ω)
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e) (n : ℕ)
    (F : Episode N T → ℝ) (hF : Measurable F) (Y : Ω → ℝ) (hY : Measurable[Mpast e n] Y) :
    IndepFun (fun ω => F (e n ω)) Y P := by
  have hI := (iIndepFun_iff_iIndep _ e P).mp he.2.1
  have hle : ∀ i, MeasurableSpace.comap (e i) inferInstance ≤ ‹MeasurableSpace Ω› :=
    fun i => (he.1 i).comap_le
  have H := indep_iSup_of_disjoint hle hI (S := {n}) (T := Set.Iio n)
    (Set.disjoint_singleton_left.mpr (by simp))
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left H ?_) ?_
  · have h1 : Measurable[MeasurableSpace.comap (e n) inferInstance] (fun ω => F (e n ω)) :=
      hF.comp (comap_measurable (e n))
    exact h1.comap_le.trans
      (le_iSup₂ (f := fun i (_ : i ∈ ({n} : Set ℕ)) => MeasurableSpace.comap (e i) inferInstance)
        n rfl)
  · exact hY.comap_le

end prob

section incr
variable {N : Type*} [Fintype N] [DecidableEq N] {K : ℕ}

/-- indicator that the last state is `a` -/
def lastI (a : N) (s : List N) : ℝ := if s.getLast? = some a then 1 else 0

lemma incr_eq (x : N → Fin K → ℝ) (α : ℝ) (w : Fin K → ℝ) :
    ∀ (s : List N) (z : ℝ) (k : Fin K), tdIncrement x α w s z k =
      ∑ a, ∑ b, α * (tr a b s : ℝ) * x a k * (w ⬝ᵥ x b - w ⬝ᵥ x a) +
        ∑ a, α * lastI a s * x a k * (z - w ⬝ᵥ x a)
  | [], z, k => by simp [tdIncrement, tr, lastI]
  | [i], z, k => by
    simp only [tdIncrement, tr, lastI, Nat.cast_zero, mul_zero, zero_mul, Finset.sum_const_zero,
      zero_add, List.getLast?_singleton, Option.some.injEq, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  | i :: j :: rest, z, k => by
    rw [tdIncrement, Pi.add_apply, incr_eq x α w (j :: rest) z k]
    simp only [tr, lastI, List.getLast?_cons_cons, Pi.smul_apply, smul_eq_mul]
    push_cast
    simp only [add_mul, mul_add, Finset.sum_add_distrib]
    have h : ∑ a, ∑ b, α * (if i = a ∧ j = b then (1:ℝ) else 0) * x a k *
        (w ⬝ᵥ x b - w ⬝ᵥ x a) = α * (w ⬝ᵥ x j - w ⬝ᵥ x i) * x i k := by
      rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
      · simp; ring
      · intro b _ hb; simp [Ne.symm hb]
      · simp
      · intro a _ ha; simp [Ne.symm ha]
      · simp
    rw [h]; ring

end incr
end Pvb19c043e

namespace Pvb19c043e
open SuttonTD.Convergence MeasureTheory ProbabilityTheory

section main
variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T] {K : ℕ}
  {Ω : Type*} [MeasurableSpace Ω]

lemma step_eq (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ) (e : ℕ → Ω → Episode N T)
    (m : ℕ) (ω : Ω) (k : Fin K) :
    tdWeights x α w₀ e (m+1) ω k = tdWeights x α w₀ e m ω k +
      (∑ a, ∑ b, (α * x a k) * ((tr a b (e m ω).path : ℝ) *
          (tdWeights x α w₀ e m ω ⬝ᵥ x b - tdWeights x α w₀ e m ω ⬝ᵥ x a)) +
        ∑ a, (α * x a k) * (lastI a (e m ω).path * (e m ω).out -
          lastI a (e m ω).path * (tdWeights x α w₀ e m ω ⬝ᵥ x a))) := by
  simp only [tdWeights, tdStep, Pi.add_apply]
  rw [incr_eq]
  congr 2
  · exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  · exact Finset.sum_congr rfl (fun a _ => by ring)

lemma meas_dot (M : MeasurableSpace Ω) (W : Ω → Fin K → ℝ) (hW : Measurable[M] W)
    (v : Fin K → ℝ) : Measurable[M] (fun ω => W ω ⬝ᵥ v) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ (fun l _ => (measurable_pi_iff.mp hW l).mul_const _)

lemma meas_pi_mk (M : MeasurableSpace Ω) (W : Ω → Fin K → ℝ)
    (h : ∀ k, Measurable[M] (fun ω => W ω k)) : Measurable[M] W := measurable_pi_iff.mpr h

lemma meas_pi_comp (M : MeasurableSpace Ω) (W : Ω → Fin K → ℝ) (h : Measurable[M] W) (k : Fin K) :
    Measurable[M] (fun ω => W ω k) := measurable_pi_iff.mp h k

lemma meas_W (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ) (e : ℕ → Ω → Episode N T) :
    ∀ m, Measurable[Mpast e m] (tdWeights x α w₀ e m)
  | 0 => measurable_const
  | m+1 => by
    have ih := (meas_W x α w₀ e m).mono (Mpast_mono e m) le_rfl
    have hem := meas_e_past e m (m+1) (Nat.lt_succ_self m)
    refine meas_pi_mk _ _ (fun k => ?_)
    simp_rw [step_eq x α w₀ e m _ k]
    have htr : ∀ a b, Measurable[Mpast e (m+1)] (fun ω => (tr a b (e m ω).path : ℝ)) :=
      fun a b => (meas_pt (fun q : List N × T => (tr a b q.1 : ℝ))).comp hem
    have hla : ∀ a, Measurable[Mpast e (m+1)] (fun ω => lastI a (e m ω).path) :=
      fun a => (meas_pt (fun q : List N × T => lastI a q.1)).comp hem
    have hout : Measurable[Mpast e (m+1)] (fun ω => (e m ω).out) := meas_out.comp hem
    have hd := meas_dot _ _ ih
    exact (meas_pi_comp _ _ ih k).add ((Finset.measurable_sum _ (fun a _ =>
      Finset.measurable_sum _ (fun b _ => ((htr a b).mul ((hd _).sub (hd _))).const_mul _))).add
      (Finset.measurable_sum _ (fun a _ =>
        (((hla a).mul hout).sub ((hla a).mul (hd _))).const_mul _)))

lemma dot_lemma (P : Measure Ω) (W : Ω → Fin K → ℝ) (hint : ∀ l, Integrable (fun ω => W ω l) P)
    (v : Fin K → ℝ) : Integrable (fun ω => W ω ⬝ᵥ v) P ∧
      ∫ ω, W ω ⬝ᵥ v ∂P = (fun l => ∫ ω, W ω l ∂P) ⬝ᵥ v := by
  simp only [dotProduct]
  refine ⟨integrable_finsetSum _ (fun l _ => (hint l).mul_const _), ?_⟩
  rw [integral_finsetSum _ (fun l _ => (hint l).mul_const _)]
  simp [integral_mul_const]

lemma prod_lemma (C : AbsorbingChain N T) (μ : N → ℝ) (ν : T → Measure ℝ) (P : Measure Ω)
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e) (m : ℕ)
    (F : Episode N T → ℝ) (hF : Measurable F) (hFi : Integrable (fun ω => F (e m ω)) P)
    (Y : Ω → ℝ) (hY : Measurable[Mpast e m] Y) (hYi : Integrable Y P) :
    Integrable (fun ω => F (e m ω) * Y ω) P ∧
      ∫ ω, F (e m ω) * Y ω ∂P = (∫ ω, F (e m ω) ∂P) * ∫ ω, Y ω ∂P := by
  have hind := indep_cur C μ ν P e he m F hF Y hY
  exact ⟨hind.integrable_mul hFi hYi,
    hind.integral_mul_eq_mul_integral hFi.aestronglyMeasurable hYi.aestronglyMeasurable⟩

lemma lastI_nonneg (a : N) (s : List N) : 0 ≤ lastI a s := by
  unfold lastI; split_ifs <;> norm_num

lemma hasSum_lastI (C : AbsorbingChain N T) (μ : N → ℝ) (a : N) :
    HasSum (fun q : List N × T => C.pathWeight μ q.1 q.2 * lastI a q.1)
      (C.expectedVisits μ a * ∑ j, C.pT a j) := by
  classical
  have h := hasSum_sum (s := Finset.univ) (fun j _ => hasSum_last C μ a j)
  have e : (fun q : List N × T => C.pathWeight μ q.1 q.2 * lastI a q.1) =
      fun q => ∑ j, C.pathWeight μ q.1 q.2 *
        (if q.1.getLast? = some a ∧ q.2 = j then (1 : ℝ) else 0) := by
    funext q
    rw [← Finset.mul_sum]
    congr 1
    by_cases hq : q.1.getLast? = some a
    · simp [lastI, hq]
    · simp [lastI, hq]
  rw [e, Finset.mul_sum]
  exact h

lemma int_lastout (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (hν : ∀ j, Integrable id (ν j))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e) (m : ℕ) (a : N) :
    Integrable (fun ω => lastI a (e m ω).path * (e m ω).out) P ∧
      ∫ ω, lastI a (e m ω).path * (e m ω).out ∂P =
        C.expectedVisits μ a * ∑ j, C.pT a j * ∫ z, z ∂ν j := by
  classical
  let S : T → Set (List N × T) := fun j => {q | q.1.getLast? = some a ∧ q.2 = j}
  have hpt : (fun ω => lastI a (e m ω).path * (e m ω).out) = fun ω => ∑ j,
      {ω | ((e m ω).path, (e m ω).term) ∈ S j}.indicator (fun ω => (e m ω).out) ω := by
    funext ω
    by_cases h : (e m ω).path.getLast? = some a
    · simp [lastI, h, Set.indicator_apply, S]
    · simp [lastI, h, Set.indicator_apply, S]
  have hj := fun j => out_lemma C μ ν hν P e he m (S j) j (fun q hq => hq.2)
  have hPA : ∀ j, (P {ω | ((e m ω).path, (e m ω).term) ∈ S j}).toReal =
      C.expectedVisits μ a * C.pT a j := by
    intro j
    have hl := (law C μ hμ0 ν P e he m
      (fun q : List N × T => if q.1.getLast? = some a ∧ q.2 = j then (1 : ℝ) else 0)
      (fun q => by split_ifs <;> norm_num) _ (hasSum_last C μ a j)).2
    have hA : MeasurableSet {ω | ((e m ω).path, (e m ω).term) ∈ S j} := (he.1 m) (mset_pt (S j))
    rw [← hl, ← measureReal_def, ← integral_indicator_one hA]
    refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
    simp [Set.indicator_apply, S]
  rw [hpt]
  refine ⟨integrable_finsetSum _ (fun j _ => (hj j).1), ?_⟩
  rw [integral_finsetSum _ (fun j _ => (hj j).1), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(hj j).2, hPA j]
  ring

end main
end Pvb19c043e

namespace Pvb19c043e
open SuttonTD.Convergence MeasureTheory ProbabilityTheory

section main2
variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T] {K : ℕ}
  {Ω : Type*} [MeasurableSpace Ω]

lemma step_terms (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (hν : ∀ j, Integrable id (ν j))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e)
    (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ) (m : ℕ)
    (hint : ∀ l, Integrable (fun ω => tdWeights x α w₀ e m ω l) P) (a b : N) :
    (Integrable (fun ω => (tr a b (e m ω).path : ℝ) *
        (tdWeights x α w₀ e m ω ⬝ᵥ x b - tdWeights x α w₀ e m ω ⬝ᵥ x a)) P ∧
      ∫ ω, (tr a b (e m ω).path : ℝ) *
        (tdWeights x α w₀ e m ω ⬝ᵥ x b - tdWeights x α w₀ e m ω ⬝ᵥ x a) ∂P =
        (C.expectedVisits μ a * C.pN a b) *
          ((fun l => ∫ ω, tdWeights x α w₀ e m ω l ∂P) ⬝ᵥ x b -
            (fun l => ∫ ω, tdWeights x α w₀ e m ω l ∂P) ⬝ᵥ x a)) ∧
    (Integrable (fun ω => lastI a (e m ω).path * (e m ω).out -
        lastI a (e m ω).path * (tdWeights x α w₀ e m ω ⬝ᵥ x a)) P ∧
      ∫ ω, (lastI a (e m ω).path * (e m ω).out -
        lastI a (e m ω).path * (tdWeights x α w₀ e m ω ⬝ᵥ x a)) ∂P =
        C.expectedVisits μ a * ∑ j, C.pT a j * ∫ z, z ∂ν j -
          (C.expectedVisits μ a * ∑ j, C.pT a j) *
            ((fun l => ∫ ω, tdWeights x α w₀ e m ω l ∂P) ⬝ᵥ x a)) := by
  have hW := meas_W x α w₀ e m
  have hdb := dot_lemma P _ hint (x b)
  have hda := dot_lemma P _ hint (x a)
  have hY : Measurable[Mpast e m] (fun ω => tdWeights x α w₀ e m ω ⬝ᵥ x b -
      tdWeights x α w₀ e m ω ⬝ᵥ x a) := (meas_dot _ _ hW _).sub (meas_dot _ _ hW _)
  have hYi : Integrable (fun ω => tdWeights x α w₀ e m ω ⬝ᵥ x b -
      tdWeights x α w₀ e m ω ⬝ᵥ x a) P := hdb.1.sub hda.1
  have htr : Integrable (fun ω => (tr a b (e m ω).path : ℝ)) P ∧
      ∫ ω, (tr a b (e m ω).path : ℝ) ∂P = C.expectedVisits μ a * C.pN a b :=
    law C μ hμ0 ν P e he m (fun q : List N × T => (tr a b q.1 : ℝ))
      (fun _ => Nat.cast_nonneg _) _ (hasSum_tr C μ a b)
  have hla : Integrable (fun ω => lastI a (e m ω).path) P ∧
      ∫ ω, lastI a (e m ω).path ∂P = C.expectedVisits μ a * ∑ j, C.pT a j :=
    law C μ hμ0 ν P e he m (fun q : List N × T => lastI a q.1) (fun q => lastI_nonneg a q.1) _
      (hasSum_lastI C μ a)
  have p1 : Integrable (fun ω => (tr a b (e m ω).path : ℝ) *
        (tdWeights x α w₀ e m ω ⬝ᵥ x b - tdWeights x α w₀ e m ω ⬝ᵥ x a)) P ∧
      ∫ ω, (tr a b (e m ω).path : ℝ) *
        (tdWeights x α w₀ e m ω ⬝ᵥ x b - tdWeights x α w₀ e m ω ⬝ᵥ x a) ∂P =
      (∫ ω, (tr a b (e m ω).path : ℝ) ∂P) * ∫ ω, (tdWeights x α w₀ e m ω ⬝ᵥ x b -
        tdWeights x α w₀ e m ω ⬝ᵥ x a) ∂P :=
    prod_lemma C μ ν P e he m (fun ep => (tr a b ep.path : ℝ))
      (meas_pt (fun q : List N × T => (tr a b q.1 : ℝ))) htr.1 _ hY hYi
  have p2 : Integrable (fun ω => lastI a (e m ω).path * (tdWeights x α w₀ e m ω ⬝ᵥ x a)) P ∧
      ∫ ω, lastI a (e m ω).path * (tdWeights x α w₀ e m ω ⬝ᵥ x a) ∂P =
      (∫ ω, lastI a (e m ω).path ∂P) * ∫ ω, tdWeights x α w₀ e m ω ⬝ᵥ x a ∂P :=
    prod_lemma C μ ν P e he m (fun ep => lastI a ep.path)
      (meas_pt (fun q : List N × T => lastI a q.1)) hla.1 _ (meas_dot _ _ hW (x a)) hda.1
  have hlo := int_lastout C μ hμ0 ν hν P e he m a
  refine ⟨⟨p1.1, ?_⟩, ⟨hlo.1.sub p2.1, ?_⟩⟩
  · rw [p1.2, htr.2, integral_sub hdb.1 hda.1, hdb.2, hda.2]
  · rw [integral_sub hlo.1 p2.1, hlo.2, p2.2, hla.2, hda.2]

lemma int_W (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (hν : ∀ j, Integrable id (ν j))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e)
    (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ) :
    ∀ m k, Integrable (fun ω => tdWeights x α w₀ e m ω k) P
  | 0, k => integrable_const _
  | m+1, k => by
    have ih := int_W C μ hμ0 ν hν P e he x α w₀ m
    have ht := fun a b => step_terms C μ hμ0 ν hν P e he x α w₀ m ih a b
    simp_rw [step_eq x α w₀ e m _ k]
    exact (ih k).add ((integrable_finsetSum _ (fun a _ => integrable_finsetSum _
      (fun b _ => (ht a b).1.1.const_mul _))).add
      (integrable_finsetSum _ (fun a _ => (ht a a).2.1.const_mul _)))

lemma exp_step (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (hν : ∀ j, Integrable id (ν j))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e)
    (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ) (m : ℕ) (k : Fin K) :
    ∫ ω, tdWeights x α w₀ e (m+1) ω k ∂P = ∫ ω, tdWeights x α w₀ e m ω k ∂P +
      (∑ a, ∑ b, (α * x a k) * ((C.expectedVisits μ a * C.pN a b) *
          ((fun l => ∫ ω, tdWeights x α w₀ e m ω l ∂P) ⬝ᵥ x b -
            (fun l => ∫ ω, tdWeights x α w₀ e m ω l ∂P) ⬝ᵥ x a)) +
        ∑ a, (α * x a k) * (C.expectedVisits μ a * ∑ j, C.pT a j * ∫ z, z ∂ν j -
          (C.expectedVisits μ a * ∑ j, C.pT a j) *
            ((fun l => ∫ ω, tdWeights x α w₀ e m ω l ∂P) ⬝ᵥ x a))) := by
  have ih := int_W C μ hμ0 ν hν P e he x α w₀ m
  have ht := fun a b => step_terms C μ hμ0 ν hν P e he x α w₀ m ih a b
  simp_rw [step_eq x α w₀ e m _ k]
  have i1 := integrable_finsetSum (μ := P) Finset.univ (fun a _ => integrable_finsetSum
      Finset.univ (fun b _ => (ht a b).1.1.const_mul (α * x a k)))
  have i2 := integrable_finsetSum (μ := P) Finset.univ
      (fun a _ => (ht a a).2.1.const_mul (α * x a k))
  have i12 : Integrable (fun ω => (∑ a, ∑ b, (α * x a k) * ((tr a b (e m ω).path : ℝ) *
          (tdWeights x α w₀ e m ω ⬝ᵥ x b - tdWeights x α w₀ e m ω ⬝ᵥ x a))) +
        ∑ a, (α * x a k) * (lastI a (e m ω).path * (e m ω).out -
          lastI a (e m ω).path * (tdWeights x α w₀ e m ω ⬝ᵥ x a))) P := i1.add i2
  rw [integral_add (ih k) i12, integral_add i1 i2,
    integral_finsetSum _ (fun a _ => integrable_finsetSum Finset.univ
      (fun b _ => (ht a b).1.1.const_mul (α * x a k))),
    integral_finsetSum _ (fun a _ => (ht a a).2.1.const_mul (α * x a k))]
  congr 2
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [integral_finsetSum _ (fun b _ => (ht a b).1.1.const_mul (α * x a k))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [integral_const_mul, (ht a b).1.2]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [integral_const_mul, (ht a a).2.2]

theorem main_thm (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (hν : ∀ j, Integrable id (ν j))
    (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e) (n : ℕ) :
    (∀ k, Integrable (fun ω => tdWeights x α w₀ e n ω k) P) ∧
      (fun k => ∫ ω, tdWeights x α w₀ e (n+1) ω k ∂P) =
        (fun k => ∫ ω, tdWeights x α w₀ e n ω k ∂P) +
        α • (((Matrix.of fun k i => x i k) * diagonal (C.expectedVisits μ)) *ᵥ
          (C.h (fun j => ∫ z, z ∂ν j) +
            C.Q *ᵥ ((Matrix.of fun k i => x i k)ᵀ *ᵥ (fun k => ∫ ω, tdWeights x α w₀ e n ω k ∂P)) -
            (Matrix.of fun k i => x i k)ᵀ *ᵥ (fun k => ∫ ω, tdWeights x α w₀ e n ω k ∂P))) := by
  refine ⟨int_W C μ hμ0 ν hν P e he x α w₀ n, ?_⟩
  funext k
  rw [exp_step C μ hμ0 ν hν P e he x α w₀ n k]
  set wb : Fin K → ℝ := fun l => ∫ ω, tdWeights x α w₀ e n ω l ∂P with hwb
  set d := C.expectedVisits μ with hd
  have hX : ∀ v : Fin K → ℝ, ∀ b, ((Matrix.of fun k i => x i k)ᵀ *ᵥ v) b = v ⬝ᵥ x b := by
    intro v b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
  have hXD : ∀ u : N → ℝ, (((Matrix.of fun k i => x i k) * diagonal d) *ᵥ u) k =
      ∑ a, x a k * d a * u a := by
    intro u
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal, Matrix.of_apply]
  have hQ : ∀ u : N → ℝ, ∀ a, (C.Q *ᵥ u) a = ∑ b, C.pN a b * u b := by
    intro u a
    simp only [Matrix.mulVec, dotProduct, AbsorbingChain.Q, Matrix.of_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hXD]
  simp only [Pi.add_apply, Pi.sub_apply, hQ, hX, AbsorbingChain.h]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hr := C.row_sum a
  have hs : ∑ j, C.pT a j = 1 - ∑ b, C.pN a b := by linarith
  have e1 : ∑ b, (α * x a k) * ((d a * C.pN a b) * (wb ⬝ᵥ x b - wb ⬝ᵥ x a)) =
      (α * x a k * d a) * (∑ b, C.pN a b * (wb ⬝ᵥ x b) - (∑ b, C.pN a b) * (wb ⬝ᵥ x a)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  rw [e1, hs]
  ring

end main2
end Pvb19c043e

open Filter Topology MeasureTheory Matrix SuttonTD.Convergence in
theorem solution {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]
    (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (hν : ∀ j, Integrable id (ν j))
    {K : ℕ} (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → Ω → Episode N T) (he : IsEpisodeStream C μ ν P e) (n : ℕ) :
    let X : Matrix (Fin K) N ℝ := Matrix.of fun k i => x i k
    let d : N → ℝ := C.expectedVisits μ
    let wbar : ℕ → Fin K → ℝ := fun m k => ∫ ω, tdWeights x α w₀ e m ω k ∂P
    (∀ k, Integrable (fun ω => tdWeights x α w₀ e n ω k) P) ∧
      wbar (n + 1) = wbar n + α • ((X * diagonal d) *ᵥ
        (C.h (fun j => ∫ z, z ∂ν j) + C.Q *ᵥ (Xᵀ *ᵥ wbar n) - Xᵀ *ᵥ wbar n)) := by
  intro X d wbar
  exact Pvb19c043e.main_thm C μ hμ0 ν hν x α w₀ P e he n
