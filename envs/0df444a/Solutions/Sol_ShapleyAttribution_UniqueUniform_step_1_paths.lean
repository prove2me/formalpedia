-- Prove2me | solution 1 for ShapleyAttribution.UniqueUniform.step_1_paths
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:55:44.817205+00:00
-- url     : https://prove2.me/submissions/1e2c1c6a-8023-46fe-bbdc-91f1e8a2f49d

import Mathlib
import Definitions.Def_ShapleyAttribution_UniqueUniform_Model

open Matrix Finset Filter Topology
open ShapleyAttribution.UniqueUniform

namespace CasvThm2Aux

variable {m n : ℕ}

/-! ### Neumann series for a nonnegative matrix dominated by a convergent one -/

lemma pow_bounds (Q A : Matrix (Fin m) (Fin m) ℝ) (h0 : ∀ i j, 0 ≤ Q i j)
    (hle : ∀ i j, Q i j ≤ A i j) (k : ℕ) :
    ∀ i j, 0 ≤ (Q ^ k) i j ∧ (Q ^ k) i j ≤ (A ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, pow_succ, mul_apply, mul_apply]
    refine ⟨Finset.sum_nonneg fun l _ => mul_nonneg (ih i l).1 (h0 l j), ?_⟩
    refine Finset.sum_le_sum fun l _ => ?_
    exact mul_le_mul (ih i l).2 (hle l j) (h0 l j) (le_trans (ih i l).1 (ih i l).2)

lemma tendsto_pow_zero (Q A : Matrix (Fin m) (Fin m) ℝ) (h0 : ∀ i j, 0 ≤ Q i j)
    (hle : ∀ i j, Q i j ≤ A i j)
    (hA : Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => Q ^ k) atTop (𝓝 0) := by
  have hA' : Tendsto (fun k : ℕ => ((A ^ k : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ))
      atTop (𝓝 (0 : Fin m → Fin m → ℝ)) := hA
  have hgoal : Tendsto (fun k : ℕ => ((Q ^ k : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ))
      atTop (𝓝 (0 : Fin m → Fin m → ℝ)) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have hAij : Tendsto (fun k : ℕ => (A ^ k) i j) atTop (𝓝 0) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hA' i) j
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAij
      (fun k => (pow_bounds Q A h0 hle k i j).1) (fun k => (pow_bounds Q A h0 hle k i j).2)
  exact hgoal

lemma isUnit_det (Q : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Tendsto (fun k : ℕ => Q ^ k) atTop (𝓝 0)) : IsUnit (1 - Q).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have hQv : Q *ᵥ v = v := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  have hpow : ∀ k : ℕ, Q ^ k *ᵥ v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, hQv]
  have hc : Continuous fun A : Matrix (Fin m) (Fin m) ℝ => A *ᵥ v :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have ht : Tendsto (fun k : ℕ => Q ^ k *ᵥ v) atTop (𝓝 ((0 : Matrix (Fin m) (Fin m) ℝ) *ᵥ v)) :=
    (hc.tendsto 0).comp hQ
  simp only [hpow, zero_mulVec] at ht
  exact hv0 (tendsto_nhds_unique tendsto_const_nhds ht)

lemma neumann_hasSum (Q : Matrix (Fin m) (Fin m) ℝ) (lam c : Fin m → ℝ)
    (h0 : ∀ i j, 0 ≤ Q i j) (hl : ∀ i, 0 ≤ lam i) (hc : ∀ i, 0 ≤ c i)
    (hQ : Tendsto (fun k : ℕ => Q ^ k) atTop (𝓝 0)) :
    HasSum (fun k : ℕ => lam ⬝ᵥ (Q ^ k *ᵥ c)) (lam ⬝ᵥ ((1 - Q)⁻¹ *ᵥ c)) := by
  have hpow0 : ∀ k i j, 0 ≤ (Q ^ k) i j := fun k i j =>
    (pow_bounds Q Q h0 (fun _ _ => le_rfl) k i j).1
  have hnn : ∀ k : ℕ, 0 ≤ lam ⬝ᵥ (Q ^ k *ᵥ c) := by
    intro k
    refine Finset.sum_nonneg fun i _ => mul_nonneg (hl i) ?_
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hpow0 k i j) (hc j)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hdet := isUnit_det Q hQ
  have hpart : ∀ N : ℕ, ∑ k ∈ range N, lam ⬝ᵥ (Q ^ k *ᵥ c) =
      lam ⬝ᵥ (((1 - Q)⁻¹ * (1 - Q ^ N)) *ᵥ c) := by
    intro N
    have h1 : (1 - Q)⁻¹ * (1 - Q ^ N) = ∑ k ∈ range N, Q ^ k := by
      rw [← mul_neg_geom_sum, ← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
    rw [h1, Matrix.sum_mulVec, dotProduct_sum]
  simp only [hpart]
  have hcont : Continuous fun A : Matrix (Fin m) (Fin m) ℝ =>
      lam ⬝ᵥ (((1 - Q)⁻¹ * (1 - A)) *ᵥ c) := by
    refine Continuous.dotProduct continuous_const ?_
    refine Continuous.matrix_mulVec ?_ continuous_const
    exact Continuous.matrix_mul continuous_const (continuous_const.sub continuous_id)
  have := (hcont.tendsto 0).comp hQ
  simp only [sub_zero, Matrix.mul_one] at this
  exact this

/-! ### Masked transition matrices and path expansions -/

abbrev α (m n : ℕ) := Fin m × Fin n

def Qm (M : Model m n) (S : Finset (α m n)) : Matrix (Fin m) (Fin m) ℝ :=
  fun s s' => ∑ a, if (s, a) ∈ S then M.chain.β s a * M.chain.P a s s' else 0

def cm (M : Model m n) (S : Finset (α m n)) : Fin m → ℝ :=
  fun s => ∑ a, if (s, a) ∈ S then M.chain.β s a * M.chain.pc a s else 0

noncomputable def ind (S : Finset (α m n)) (l : List (α m n)) : ℝ :=
  if l.toFinset ⊆ S then 1 else 0

lemma ind_cons (S : Finset (α m n)) (x : α m n) (l : List (α m n)) :
    ind S (x :: l) = (if x ∈ S then 1 else 0) * ind S l := by
  unfold ind
  by_cases hx : x ∈ S <;> by_cases hl : l.toFinset ⊆ S <;>
    simp [hx, hl, List.toFinset_cons, Finset.insert_subset_iff]

noncomputable def H (M : Model m n) (S : Finset (α m n)) (k : ℕ) (x : α m n) : ℝ :=
  ∑ v : Fin k → α m n, ind S (x :: List.ofFn v) * M.convTail (x :: List.ofFn v)

lemma H_zero (M : Model m n) (S : Finset (α m n)) (s : Fin m) (a : Fin n) :
    H M S 0 (s, a) = if (s, a) ∈ S then M.chain.β s a * M.chain.pc a s else 0 := by
  unfold H
  rw [Fintype.sum_unique]
  simp only [List.ofFn_zero]
  rw [ind_cons]
  simp [ind, Model.convTail]

lemma sum_fin_succ_fun {β : Type*} [Fintype β] (k : ℕ) (f : (Fin (k + 1) → β) → ℝ) :
    ∑ v : Fin (k + 1) → β, f v = ∑ y : β, ∑ w : Fin k → β, f (Fin.cons y w) := by
  rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
  rfl

lemma H_succ (M : Model m n) (S : Finset (α m n)) (k : ℕ) (s : Fin m) (a : Fin n) :
    H M S (k + 1) (s, a) = ∑ y : α m n,
      (if (s, a) ∈ S then M.chain.β s a * M.chain.P a s y.1 else 0) * H M S k y := by
  unfold H
  rw [sum_fin_succ_fun]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨s', a'⟩ := y
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [ind_cons, Model.convTail]
  by_cases h : (s, a) ∈ S <;> simp [h] <;> ring

lemma H_sum (M : Model m n) (S : Finset (α m n)) (k : ℕ) (s : Fin m) :
    ∑ a, H M S k (s, a) = (Qm M S ^ k *ᵥ cm M S) s := by
  induction k generalizing s with
  | zero =>
    simp only [pow_zero, one_mulVec]
    simp only [H_zero, cm]
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec]
    rw [show (Qm M S *ᵥ (Qm M S ^ k *ᵥ cm M S)) s =
      ∑ s', Qm M S s s' * (Qm M S ^ k *ᵥ cm M S) s' from rfl]
    simp only [← ih]
    simp only [H_succ]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s' _ => ?_
    simp only [Qm, Finset.sum_mul, Finset.mul_sum]

lemma len_sum (M : Model m n) (S : Finset (α m n)) (k : ℕ) :
    ∑ v : Fin (k + 1) → α m n, ind S (List.ofFn v) * M.convProb (List.ofFn v) =
      M.chain.lam ⬝ᵥ (Qm M S ^ k *ᵥ cm M S) := by
  rw [sum_fin_succ_fun, Fintype.sum_prod_type]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← H_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold H
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Model.convProb]
  ring

lemma path_hasSum (M : Model m n) (S : Finset (α m n))
    (hnn : ∀ l, 0 ≤ ind S l * M.convProb l) {V : ℝ}
    (hV : HasSum (fun k : ℕ => M.chain.lam ⬝ᵥ (Qm M S ^ k *ᵥ cm M S)) V) :
    HasSum (fun l => ind S l * M.convProb l) V := by
  set f : List (α m n) → ℝ := fun l => ind S l * M.convProb l with hf
  set F : (Σ k, Fin k → α m n) → ℝ := f ∘ List.equivSigmaTuple.symm with hF
  have hFv : ∀ k (v : Fin k → α m n), F ⟨k, v⟩ = f (List.ofFn v) := fun _ _ => rfl
  set g : ℕ → ℝ := fun k => ∑ v : Fin k → α m n, F ⟨k, v⟩ with hg
  have hg0 : g 0 = 0 := by
    simp only [hg, hFv, hf]
    rw [Fintype.sum_unique]
    simp [Model.convProb]
  have hgs : ∀ k, g (k + 1) = M.chain.lam ⬝ᵥ (Qm M S ^ k *ᵥ cm M S) := by
    intro k
    simp only [hg, hFv, hf]
    exact len_sum M S k
  have hgV : HasSum g V := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [hgs, hg0] using hV
  have hFnn : ∀ x, 0 ≤ F x := fun x => hnn _
  have hFs : Summable F := by
    rw [summable_sigma_of_nonneg hFnn]
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simp only [tsum_fintype]
    exact hgV.summable
  have h2 : HasSum g (∑' x, F x) :=
    HasSum.sigma hFs.hasSum (fun k => hasSum_fintype _)
  have hEq : (∑' x, F x) = V := h2.unique hgV
  have hF' : HasSum F V := hEq ▸ hFs.hasSum
  exact (Equiv.hasSum_iff List.equivSigmaTuple.symm).1 hF'

/-! ### Nonnegativity and domination -/

structure NN (M : Model m n) : Prop where
  lam : ∀ s, 0 ≤ M.chain.lam s
  β : ∀ s a, 0 ≤ M.chain.β s a
  P : ∀ a s s', 0 ≤ M.chain.P a s s'
  pc : ∀ a s, 0 ≤ M.chain.pc a s

lemma NN.of_valid {M : Model m n} (hM : M.Valid) : NN M :=
  ⟨hM.1, hM.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2.1⟩

lemma NN.cf {M : Model m n} (h : NN M) (r : α m n) : NN (M.cfModel r) := by
  refine ⟨h.lam, h.β, ?_, ?_⟩
  · intro a s s'
    simp only [Model.cfModel]
    split_ifs
    · exact h.P _ _ _
    · exact h.P _ _ _
  · intro a s
    simp only [Model.cfModel]
    split_ifs
    · exact h.pc _ _
    · exact h.pc _ _

lemma convTail_nn {M : Model m n} (h : NN M) : ∀ l, 0 ≤ M.convTail l
  | [] => by simp [Model.convTail]
  | [(s, a)] => by simp only [Model.convTail]; exact mul_nonneg (h.β _ _) (h.pc _ _)
  | (s, a) :: (s', a') :: rest => by
      simp only [Model.convTail]
      exact mul_nonneg (mul_nonneg (h.β _ _) (h.P _ _ _)) (convTail_nn h _)

lemma convProb_nn {M : Model m n} (h : NN M) : ∀ l, 0 ≤ M.convProb l
  | [] => by simp [Model.convProb]
  | (s, a) :: rest => by
      simp only [Model.convProb]
      exact mul_nonneg (h.lam _) (convTail_nn h _)

lemma ind_nn (S : Finset (α m n)) (l : List (α m n)) : 0 ≤ ind S l := by
  unfold ind; split_ifs <;> norm_num

/-- The general path expansion: the coalition value of the masked chain equals the
expected indicator of staying within `S` on converting paths. -/
lemma masked_hasSum (M : Model m n) (h : NN M)
    (hA : Tendsto (fun k : ℕ => M.Pβ ^ k) atTop (𝓝 0)) (S : Finset (α m n)) :
    HasSum (fun k : ℕ => M.chain.lam ⬝ᵥ (Qm M S ^ k *ᵥ cm M S))
        (M.chain.lam ⬝ᵥ ((1 - Qm M S)⁻¹ *ᵥ cm M S)) ∧
      HasSum (fun l => ind S l * M.convProb l)
        (M.chain.lam ⬝ᵥ ((1 - Qm M S)⁻¹ *ᵥ cm M S)) := by
  have h0 : ∀ i j, 0 ≤ Qm M S i j := by
    intro i j
    refine Finset.sum_nonneg fun a _ => ?_
    split_ifs
    · exact mul_nonneg (h.β _ _) (h.P _ _ _)
    · exact le_rfl
  have hle : ∀ i j, Qm M S i j ≤ M.Pβ i j := by
    intro i j
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (h.β _ _) (h.P _ _ _)
  have hc : ∀ i, 0 ≤ cm M S i := by
    intro i
    refine Finset.sum_nonneg fun a _ => ?_
    split_ifs
    · exact mul_nonneg (h.β _ _) (h.pc _ _)
    · exact le_rfl
  have hQ := tendsto_pow_zero (Qm M S) M.Pβ h0 hle hA
  have hN := neumann_hasSum (Qm M S) M.chain.lam (cm M S) h0 h.lam hc hQ
  exact ⟨hN, path_hasSum M S (fun l => mul_nonneg (ind_nn S l) (convProb_nn h l)) hN⟩

lemma coalP_empty (M : Model m n) (X : Finset (α m n)) : M.coalP X ∅ = Qm M X := by
  ext s s'
  simp [Model.coalP, Qm]

lemma coalPc_empty (M : Model m n) (X : Finset (α m n)) : M.coalPc X ∅ = cm M X := by
  ext s
  simp [Model.coalPc, cm]

lemma val_empty (M : Model m n) (X : Finset (α m n)) :
    M.val X ∅ = M.chain.lam ⬝ᵥ ((1 - Qm M X)⁻¹ *ᵥ cm M X) := by
  rw [Model.val, coalP_empty, coalPc_empty]

lemma coalP_cf (M : Model m n) (r : α m n) (X : Finset (α m n)) (hr : r ∉ X) :
    M.coalP X {r} = Qm (M.cfModel r) (insert r X) := by
  ext s s'
  simp only [Model.coalP, Qm, Model.cfModel]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : (s, a) = r
  · subst h
    simp [hr]
  · have h' : (s, a) ∉ ({r} : Finset (α m n)) := by simpa using h
    simp [h, h', Finset.mem_insert]

lemma coalPc_cf (M : Model m n) (r : α m n) (X : Finset (α m n)) (hr : r ∉ X) :
    M.coalPc X {r} = cm (M.cfModel r) (insert r X) := by
  ext s
  simp only [Model.coalPc, cm, Model.cfModel]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : (s, a) = r
  · subst h
    simp [hr]
  · have h' : (s, a) ∉ ({r} : Finset (α m n)) := by simpa using h
    simp [h, h', Finset.mem_insert]

lemma val_cf (M : Model m n) (r : α m n) (X : Finset (α m n)) (hr : r ∉ X) :
    M.val X {r} = (M.cfModel r).chain.lam ⬝ᵥ
      ((1 - Qm (M.cfModel r) (insert r X))⁻¹ *ᵥ cm (M.cfModel r) (insert r X)) := by
  rw [Model.val, coalP_cf M r X hr, coalPc_cf M r X hr]
  rfl

/-! ### Paths avoiding `r` have the same probability under the counterfactual -/

lemma convTail_cf (M : Model m n) (r : α m n) :
    ∀ l : List (α m n), r ∉ l → (M.cfModel r).convTail l = M.convTail l
  | [] => fun _ => rfl
  | [(s, a)] => by
      intro h
      have h' : (s, a) ≠ r := fun e => h (by simp [e])
      simp [Model.convTail, Model.cfModel, h']
  | (s, a) :: (s', a') :: rest => by
      intro h
      have h' : (s, a) ≠ r := fun e => h (by simp [e])
      have ht : r ∉ (s', a') :: rest := fun e => h (List.mem_cons_of_mem _ e)
      have ih := convTail_cf M r ((s', a') :: rest) ht
      simp only [Model.convTail] at ih ⊢
      rw [ih]
      simp [Model.cfModel, h']

lemma convProb_cf (M : Model m n) (r : α m n) (l : List (α m n)) (h : r ∉ l) :
    (M.cfModel r).convProb l = M.convProb l := by
  cases l with
  | nil => rfl
  | cons x rest =>
    obtain ⟨s, a⟩ := x
    simp only [Model.convProb]
    rw [convTail_cf M r _ h]
    rfl

/-! ### The carrier-game identity -/

lemma hockey (a M : ℕ) :
    (a + 1) * ∑ j ∈ range (M + 1), M.choose j * (a + j).factorial * (M - j).factorial =
      (a + 1 + M).factorial := by
  have h1 : ∀ j ∈ range (M + 1), M.choose j * (a + j).factorial * (M - j).factorial =
      M.factorial * a.factorial * (j + a).choose a := by
    intro j hj
    have hj' : j ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have e1 := Nat.choose_mul_factorial_mul_factorial hj'
    have e2 := Nat.add_choose_mul_factorial_mul_factorial a j
    rw [show j + a = a + j by ring, Nat.choose_symm_add]
    rw [← e2, ← e1]
    rw [show a + j = j + a by ring]
    rw [Nat.choose_symm_add]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Nat.sum_range_add_choose]
  have e3 := Nat.add_choose_mul_factorial_mul_factorial M (a + 1)
  rw [show M + a + 1 = M + (a + 1) by ring, show a + 1 + M = M + (a + 1) by ring, ← e3,
    Nat.factorial_succ]
  ring

lemma weight_sum (a M : ℕ) :
    ∑ j ∈ range (M + 1), (M.choose j : ℝ) * weight (a + 1 + M) (a + j) = 1 / (a + 1) := by
  have h := hockey a M
  have hpos : (0 : ℝ) < ((a + 1 + M).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hcast : ((a : ℝ) + 1) * ∑ j ∈ range (M + 1),
      ((M.choose j : ℝ) * (a + j).factorial * (M - j).factorial) =
      ((a + 1 + M).factorial : ℝ) := by exact_mod_cast h
  have hw : ∀ j ∈ range (M + 1), (M.choose j : ℝ) * weight (a + 1 + M) (a + j) =
      ((M.choose j : ℝ) * (a + j).factorial * (M - j).factorial) /
        ((a + 1 + M).factorial : ℝ) := by
    intro j hj
    have hj' : j ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hj)
    unfold weight
    rw [show a + 1 + M - (a + j) - 1 = M - j by omega]
    ring
  rw [Finset.sum_congr rfl hw, ← Finset.sum_div]
  rw [eq_div_iff (by positivity), div_mul_eq_mul_div, div_eq_iff hpos.ne']
  linarith [hcast]

lemma carrier (r : α m n) (U : Finset (α m n)) (hr : r ∈ U) :
    ∑ X ∈ (univ.erase r).powerset,
      (if U ⊆ insert r X then weight (m * n) X.card else 0) = 1 / (U.card : ℝ) := by
  classical
  set T := U.erase r with hT
  set D := (univ : Finset (α m n)) \ U with hD
  have hN : (univ : Finset (α m n)).card = m * n := by simp
  have hUc : U.card = T.card + 1 := (Finset.card_erase_add_one hr).symm
  have hDc : D.card + U.card = m * n := by
    rw [hD, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U), hN]
  have hsub : ∀ X : Finset (α m n), r ∉ X → (U ⊆ insert r X ↔ T ⊆ X) := by
    intro X hX
    constructor
    · intro h x hx
      have hx1 := Finset.mem_erase.1 hx
      rcases Finset.mem_insert.1 (h hx1.2) with e | e
      · exact absurd e hx1.1
      · exact e
    · intro h x hx
      by_cases e : x = r
      · exact Finset.mem_insert.2 (Or.inl e)
      · exact Finset.mem_insert.2 (Or.inr (h (Finset.mem_erase.2 ⟨e, hx⟩)))
  rw [← Finset.sum_filter]
  have hfilter : ((univ.erase r).powerset.filter (fun X => U ⊆ insert r X)) =
      ((univ.erase r).powerset.filter (fun X => T ⊆ X)) := by
    apply Finset.filter_congr
    intro X hX
    have : r ∉ X := fun h => by
      have := Finset.mem_powerset.1 hX h
      simp at this
    exact hsub X this
  rw [hfilter]
  have hbij : ∑ X ∈ (univ.erase r).powerset.filter (fun X => T ⊆ X), weight (m * n) X.card =
      ∑ Z ∈ D.powerset, weight (m * n) (T.card + Z.card) := by
    symm
    refine Finset.sum_nbij' (fun Z => T ∪ Z) (fun X => X \ T) ?_ ?_ ?_ ?_ ?_
    · intro Z hZ
      have hZ' := Finset.mem_powerset.1 hZ
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, Finset.subset_union_left⟩
      intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 h).1, Finset.mem_univ _⟩
      · have := Finset.mem_sdiff.1 (hZ' h)
        exact Finset.mem_erase.2 ⟨fun e => this.2 (e ▸ hr), Finset.mem_univ _⟩
    · intro X hX
      rw [Finset.mem_filter, Finset.mem_powerset] at hX
      rw [Finset.mem_powerset]
      intro x hx
      have h1 := Finset.mem_sdiff.1 hx
      refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hu => h1.2 ?_⟩
      have hxr : x ≠ r := (Finset.mem_erase.1 (hX.1 h1.1)).1
      exact Finset.mem_erase.2 ⟨hxr, hu⟩
    · intro Z hZ
      have hZ' := Finset.mem_powerset.1 hZ
      have hdis : Disjoint T Z := by
        rw [Finset.disjoint_left]
        intro x hxT hxZ
        exact (Finset.mem_sdiff.1 (hZ' hxZ)).2 (Finset.mem_erase.1 hxT).2
      rw [Finset.union_sdiff_left]
      exact Finset.sdiff_eq_self_of_disjoint hdis.symm
    · intro X hX
      rw [Finset.mem_filter, Finset.mem_powerset] at hX
      exact Finset.union_sdiff_of_subset hX.2
    · intro Z hZ
      have hZ' := Finset.mem_powerset.1 hZ
      have hdis : Disjoint T Z := by
        rw [Finset.disjoint_left]
        intro x hxT hxZ
        exact (Finset.mem_sdiff.1 (hZ' hxZ)).2 (Finset.mem_erase.1 hxT).2
      rw [Finset.card_union_of_disjoint hdis]
  rw [hbij]
  rw [Finset.sum_powerset_apply_card (fun k => weight (m * n) (T.card + k))]
  simp only [nsmul_eq_mul]
  have hmn : m * n = T.card + 1 + D.card := by omega
  rw [hmn, weight_sum, hUc]
  push_cast
  ring

/-! ### Main argument -/

lemma wUU_nn (r : α m n) (l : List (α m n)) : 0 ≤ wUU r l ∧ wUU r l ≤ 1 := by
  unfold wUU uniq
  split_ifs with h
  · have hpos : 1 ≤ (l.toFinset.card : ℝ) := by
      have : 0 < l.toFinset.card := Finset.card_pos.2 ⟨r, List.mem_toFinset.2 h⟩
      exact_mod_cast this
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    exact hpos
  · exact ⟨le_rfl, zero_le_one⟩

lemma pathExp_hasSum (M : Model m n) (h : NN M)
    (hA : Tendsto (fun k : ℕ => M.Pβ ^ k) atTop (𝓝 0)) (r : α m n) :
    HasSum (fun l => M.convProb l * wUU r l) (M.pathExp (wUU r)) := by
  have hall := (masked_hasSum M h hA univ).2
  have hind : ∀ l, ind (univ : Finset (α m n)) l = 1 := fun l => by simp [ind]
  simp only [hind, one_mul] at hall
  have hs : Summable (fun l => M.convProb l * wUU r l) := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (convProb_nn h l) (wUU_nn r l).1)
      (fun l => ?_) hall.summable
    have := wUU_nn r l
    have := convProb_nn h l
    nlinarith
  exact hs.hasSum

theorem main {m n : ℕ} (M : Model m n) (hM : M.Valid)
    (hA : M.Absorbing) (r : Fin m × Fin n)
    (hAcf : (M.cfModel r).Absorbing) :
    M.casv r = M.pathExp (wUU r) - (M.cfModel r).pathExp (wUU r) := by
  have h := NN.of_valid hM
  have hcf := h.cf r
  have hX : ∀ X ∈ (univ.erase r).powerset,
      HasSum (fun l => weight (m * n) X.card *
        (ind (insert r X) l * M.convProb l - ind (insert r X) l * (M.cfModel r).convProb l))
        (weight (m * n) X.card * (M.val (insert r X) ∅ - M.val X {r})) := by
    intro X hX
    have hrX : r ∉ X := fun e => by
      have := Finset.mem_powerset.1 hX e
      simp at this
    have h1 := (masked_hasSum M h hA (insert r X)).2
    have h2 := (masked_hasSum (M.cfModel r) hcf hAcf (insert r X)).2
    rw [val_empty, val_cf M r X hrX]
    exact (h1.sub h2).mul_left _
  have hsum := hasSum_sum hX
  have hfun : (fun l => ∑ X ∈ (univ.erase r).powerset, weight (m * n) X.card *
        (ind (insert r X) l * M.convProb l - ind (insert r X) l * (M.cfModel r).convProb l)) =
      fun l => M.convProb l * wUU r l - (M.cfModel r).convProb l * wUU r l := by
    funext l
    by_cases hr : r ∈ l
    · have hc := carrier r l.toFinset (List.mem_toFinset.2 hr)
      have e : ∀ X ∈ (univ.erase r).powerset, weight (m * n) X.card *
          (ind (insert r X) l * M.convProb l - ind (insert r X) l * (M.cfModel r).convProb l) =
          (if l.toFinset ⊆ insert r X then weight (m * n) X.card else 0) *
            (M.convProb l - (M.cfModel r).convProb l) := by
        intro X _
        unfold ind
        split_ifs <;> ring
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul, hc]
      simp only [wUU, uniq, if_pos hr]
      ring
    · rw [convProb_cf M r l hr]
      simp [wUU, hr]
  rw [hfun] at hsum
  have hE := (pathExp_hasSum M h hA r).sub (pathExp_hasSum (M.cfModel r) hcf hAcf r)
  unfold Model.casv
  exact hsum.unique hE


/-! ### Milestone corollaries -/

theorem neumann_ms {m n : ℕ} (M : Model m n)
    (hM : M.Valid) (hA : M.Absorbing) (X : Finset (Fin m × Fin n)) :
    HasSum (fun k : ℕ => M.chain.lam ⬝ᵥ ((M.coalP X ∅ ^ k) *ᵥ M.coalPc X ∅))
      (M.val X ∅) := by
  rw [coalP_empty, coalPc_empty, val_empty]
  exact (masked_hasSum M (NN.of_valid hM) hA X).1

theorem paths_ms {m n : ℕ} (M : Model m n)
    (hM : M.Valid) (hA : M.Absorbing) (X : Finset (Fin m × Fin n)) :
    M.val X ∅ = M.pathExp (fun path => if path.toFinset ⊆ X then 1 else 0) := by
  rw [val_empty]
  have h := (masked_hasSum M (NN.of_valid hM) hA X).2
  unfold Model.pathExp
  rw [← h.tsum_eq]
  refine tsum_congr fun l => ?_
  unfold ind
  ring

lemma shap_eq (M : Model m n) (r : α m n) :
    M.shap r = ∑ X ∈ (univ.erase r).powerset,
      weight (m * n) X.card * (M.val (insert r X) ∅ - M.val X ∅) := by
  unfold Model.shap Supermodularity.Cooperative.ShapleyValue
  refine Finset.sum_nbij' (fun S => S.map finProdFinEquiv.symm.toEmbedding)
    (fun X => X.map finProdFinEquiv.toEmbedding) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_powerset] at hS ⊢
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hS hy
    rw [Finset.mem_erase] at this ⊢
    refine ⟨fun e => this.1 ?_, Finset.mem_univ _⟩
    exact (Equiv.symm_apply_eq _).1 e
  · intro X hX
    rw [Finset.mem_powerset] at hX ⊢
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hX hy
    rw [Finset.mem_erase] at this ⊢
    refine ⟨fun e => this.1 ?_, Finset.mem_univ _⟩
    simpa using e
  · intro S _
    simp [Finset.map_map]
  · intro X _
    simp [Finset.map_map]
  · intro S _
    simp only [Finset.map_insert, Finset.card_map, weight]
    simp

lemma cf_val_of_not_mem (M : Model m n) (r : α m n) (X : Finset (α m n)) (hr : r ∉ X) :
    (M.cfModel r).val X ∅ = M.val X ∅ := by
  rw [val_empty, val_empty]
  have hQ : Qm (M.cfModel r) X = Qm M X := by
    ext s s'
    simp only [Qm, Model.cfModel]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : (s, a) ∈ X
    · have : (s, a) ≠ r := fun e => hr (e ▸ h)
      simp [h, this]
    · simp [h]
  have hc : cm (M.cfModel r) X = cm M X := by
    ext s
    simp only [cm, Model.cfModel]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : (s, a) ∈ X
    · have : (s, a) ≠ r := fun e => hr (e ▸ h)
      simp [h, this]
    · simp [h]
  rw [hQ, hc]
  rfl

theorem eq6_ms {m n : ℕ} (M : Model m n) (r : Fin m × Fin n) :
    M.casv r = M.shap r - (M.cfModel r).shap r := by
  rw [shap_eq, shap_eq, ← Finset.sum_sub_distrib]
  unfold Model.casv
  refine Finset.sum_congr rfl fun X hX => ?_
  have hrX : r ∉ X := fun e => by
    have := Finset.mem_powerset.1 hX e
    simp at this
  have h1 : (M.cfModel r).val (insert r X) ∅ = M.val X {r} := by
    rw [val_empty, val_cf M r X hrX]
  rw [h1, cf_val_of_not_mem M r X hrX]
  ring

theorem prop1_ms {m n : ℕ} (M : Model m n)
    (hM : M.Valid) (hA : M.Absorbing) (r : Fin m × Fin n) :
    M.shap r = M.pathExp (wUU r) := by
  have h := NN.of_valid hM
  rw [shap_eq]
  have hX : ∀ X ∈ (univ.erase r).powerset,
      HasSum (fun l => weight (m * n) X.card *
        (ind (insert r X) l * M.convProb l - ind X l * M.convProb l))
        (weight (m * n) X.card * (M.val (insert r X) ∅ - M.val X ∅)) := by
    intro X _
    have h1 := (masked_hasSum M h hA (insert r X)).2
    have h2 := (masked_hasSum M h hA X).2
    rw [val_empty, val_empty]
    exact (h1.sub h2).mul_left _
  have hsum := hasSum_sum hX
  have hfun : (fun l => ∑ X ∈ (univ.erase r).powerset, weight (m * n) X.card *
        (ind (insert r X) l * M.convProb l - ind X l * M.convProb l)) =
      fun l => M.convProb l * wUU r l := by
    funext l
    by_cases hr : r ∈ l
    · have hc := carrier r l.toFinset (List.mem_toFinset.2 hr)
      have e : ∀ X ∈ (univ.erase r).powerset, weight (m * n) X.card *
          (ind (insert r X) l * M.convProb l - ind X l * M.convProb l) =
          (if l.toFinset ⊆ insert r X then weight (m * n) X.card else 0) * M.convProb l := by
        intro X hX
        have hrX : r ∉ X := fun e => by
          have := Finset.mem_powerset.1 hX e
          simp at this
        have hn : ¬ l.toFinset ⊆ X := fun hs => hrX (hs (List.mem_toFinset.2 hr))
        unfold ind
        rw [if_neg hn]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul, hc]
      simp only [wUU, uniq, if_pos hr]
      ring
    · have e : ∀ X ∈ (univ.erase r).powerset, weight (m * n) X.card *
          (ind (insert r X) l * M.convProb l - ind X l * M.convProb l) = 0 := by
        intro X _
        have hiff : l.toFinset ⊆ insert r X ↔ l.toFinset ⊆ X := by
          constructor
          · intro hs x hx
            rcases Finset.mem_insert.1 (hs hx) with e | e
            · exact absurd (List.mem_toFinset.1 (e ▸ hx)) hr
            · exact e
          · intro hs
            exact hs.trans (Finset.subset_insert _ _)
        unfold ind
        by_cases hs : l.toFinset ⊆ X
        · rw [if_pos (hiff.2 hs), if_pos hs]; ring
        · rw [if_neg (fun h' => hs (hiff.1 h')), if_neg hs]; ring
      rw [Finset.sum_congr rfl e]
      simp [wUU, hr]
  rw [hfun] at hsum
  exact hsum.unique (pathExp_hasSum M h hA r)

end CasvThm2Aux

theorem solution {m n : ℕ} (M : ShapleyAttribution.UniqueUniform.Model m n)
    (hM : M.Valid) (hA : M.Absorbing) (X : Finset (Fin m × Fin n)) :
    M.val X ∅ = M.pathExp (fun path => if path.toFinset ⊆ X then 1 else 0) :=
  CasvThm2Aux.paths_ms M hM hA X
