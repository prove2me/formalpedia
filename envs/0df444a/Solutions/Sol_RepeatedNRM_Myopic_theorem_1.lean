-- Prove2me | solution 1 for RepeatedNRM.Myopic.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:12:42.418131+00:00
-- url     : https://prove2.me/submissions/ffae3410-3d26-4203-b60b-dee9bc3a87bb

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model
import Definitions.Def_RepeatedNRM_Myopic_Proof
import Theorems.Thm_LP_strong_duality_matrix
import Theorems.Thm_RepeatedNRM_Myopic_ec5_quality_bound
import Theorems.Thm_RepeatedNRM_Myopic_proposition_2

set_option linter.unusedSectionVars false

open Matrix


open Matrix

namespace RepeatedNRM.Myopic.Aux

open RepeatedNRM.Myopic

variable (I : Instance)

/-- spend of customer `j` under allocation `x` -/
def spend (x : Fin I.n → Fin I.m → ℝ) (j : Fin I.m) : ℝ := ∑ i, I.p i j * x i j

/-- LP matrix encoding of (7). -/
def lpA : Matrix ((Fin I.n × Fin I.m) ⊕ (Fin I.m ⊕ Fin I.n)) (Fin I.n × Fin I.m) ℝ :=
  fun r v => match r with
    | Sum.inl w => if w = v then -1 else 0
    | Sum.inr (Sum.inl j) => if v.2 = j then I.p v.1 j else 0
    | Sum.inr (Sum.inr i) => if v.1 = i then 1 else 0

def lpB (b : Fin I.m → ℝ) : ((Fin I.n × Fin I.m) ⊕ (Fin I.m ⊕ Fin I.n)) → ℝ :=
  fun r => match r with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl j) => b j
    | Sum.inr (Sum.inr i) => I.s i

def lpC : (Fin I.n × Fin I.m) → ℝ := fun v => I.p v.1 v.2

lemma lpA_mulVec_inl (X : Fin I.n × Fin I.m → ℝ) (w : Fin I.n × Fin I.m) :
    (lpA I *ᵥ X) (Sum.inl w) = - X w := by
  simp [lpA, Matrix.mulVec, dotProduct]

lemma lpA_mulVec_inr_inl (X : Fin I.n × Fin I.m → ℝ) (j : Fin I.m) :
    (lpA I *ᵥ X) (Sum.inr (Sum.inl j)) = ∑ i, I.p i j * X (i, j) := by
  simp only [lpA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

lemma lpA_mulVec_inr_inr (X : Fin I.n × Fin I.m → ℝ) (i : Fin I.n) :
    (lpA I *ᵥ X) (Sum.inr (Sum.inr i)) = ∑ j, X (i, j) := by
  simp only [lpA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp [ite_mul]

lemma lpAT_mulVec (y : ((Fin I.n × Fin I.m) ⊕ (Fin I.m ⊕ Fin I.n)) → ℝ)
    (v : Fin I.n × Fin I.m) :
    ((lpA I)ᵀ *ᵥ y) v = - y (Sum.inl v) + I.p v.1 v.2 * y (Sum.inr (Sum.inl v.2)) +
      y (Sum.inr (Sum.inr v.1)) := by
  simp only [lpA, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_sum_type]
  simp [ite_mul, eq_comm]; ring

lemma lp_feasible_iff (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) :
    lpA I *ᵥ (fun v => x v.1 v.2) ≤ lpB I b ↔ feasible I b x := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have := h (Sum.inl (i, j))
      rw [lpA_mulVec_inl] at this
      simp [lpB] at this
      linarith
    · intro j
      have := h (Sum.inr (Sum.inl j))
      rw [lpA_mulVec_inr_inl] at this
      simpa [lpB] using this
    · intro i
      have := h (Sum.inr (Sum.inr i))
      rw [lpA_mulVec_inr_inr] at this
      simpa [lpB] using this
  · rintro ⟨h0, h1, h2⟩ r
    rcases r with w | j | i
    · rw [lpA_mulVec_inl]; simp [lpB]; exact h0 w.1 w.2
    · rw [lpA_mulVec_inr_inl]; simpa [lpB] using h1 j
    · rw [lpA_mulVec_inr_inr]; simpa [lpB] using h2 i

lemma lpC_dot (x : Fin I.n → Fin I.m → ℝ) :
    lpC I ⬝ᵥ (fun v => x v.1 v.2) = revenue I x := by
  simp [lpC, dotProduct, Fintype.sum_prod_type, revenue]

/-- weak duality -/
lemma weak_duality (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) (hx : feasible I b x)
    (μ : Fin I.m → ℝ) (lam : Fin I.n → ℝ) (h : DualFeasible I μ lam) :
    revenue I x ≤ dualObj I b μ lam := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hl, hm, hd⟩ := h
  have e1 : ∑ i, ∑ j, (lam i + I.p i j * μ j) * x i j =
      ∑ i, lam i * ∑ j, x i j + ∑ j, μ j * ∑ i, I.p i j * x i j := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    ring
  calc revenue I x = ∑ i, ∑ j, I.p i j * x i j := rfl
    _ ≤ ∑ i, ∑ j, (lam i + I.p i j * μ j) * x i j := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_right (hd i j) (hx0 i j)
    _ = ∑ i, lam i * ∑ j, x i j + ∑ j, μ j * ∑ i, I.p i j * x i j := e1
    _ ≤ ∑ i, lam i * I.s i + ∑ j, μ j * b j := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_left (hx2 i) (hl i)
        · apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hx1 j) (hm j)
    _ = dualObj I b μ lam := by
        unfold dualObj
        congr 1
        · apply Finset.sum_congr rfl; intro i _; ring
        · apply Finset.sum_congr rfl; intro j _; ring

/-- strong duality / attainment for (7) -/
lemma lp_attain (b : Fin I.m → ℝ) (hfeas : ∃ z, feasible I b z) :
    ∃ x0 μ lam, feasible I b x0 ∧ (∀ y, feasible I b y → revenue I y ≤ revenue I x0) ∧
      DualFeasible I μ lam ∧ dualObj I b μ lam = revenue I x0 := by
  obtain ⟨z, hz⟩ := hfeas
  have hP : ∃ X, lpA I *ᵥ X ≤ lpB I b :=
    ⟨fun v => z v.1 v.2, (lp_feasible_iff I b z).2 hz⟩
  have hD : ∃ y, 0 ≤ y ∧ (lpA I)ᵀ *ᵥ y = lpC I := by
    refine ⟨Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)), ?_, ?_⟩
    · intro r; rcases r with w | j | i <;> simp
    · funext v; rw [lpAT_mulVec]; simp [lpC]
  obtain ⟨X, y, hX, hy0, hyc, hval, hopt⟩ := LP.strong_duality_matrix (lpA I) (lpB I b) (lpC I) hP hD
  let x0 : Fin I.n → Fin I.m → ℝ := fun i j => X (i, j)
  have hXeq : (fun v : Fin I.n × Fin I.m => x0 v.1 v.2) = X := by funext v; rfl
  have hx0 : feasible I b x0 := by
    rw [← lp_feasible_iff, hXeq]; exact hX
  refine ⟨x0, fun j => y (Sum.inr (Sum.inl j)), fun i => y (Sum.inr (Sum.inr i)), hx0, ?_, ?_, ?_⟩
  · intro y' hy'
    have := hopt (fun v => y' v.1 v.2) ((lp_feasible_iff I b y').2 hy')
    rw [lpC_dot, ← hXeq, lpC_dot] at this
    exact this
  · refine ⟨fun i => hy0 _, fun j => hy0 _, ?_⟩
    intro i j
    have h1 := congrFun hyc (i, j)
    rw [lpAT_mulVec] at h1
    simp [lpC] at h1
    have h2 := hy0 (Sum.inl (i, j))
    simp at h2
    linarith
  · have h1 : lpC I ⬝ᵥ X = lpB I b ⬝ᵥ y := hval
    rw [← hXeq, lpC_dot] at h1
    rw [h1]
    simp [dualObj, lpB, dotProduct, Fintype.sum_sum_type, add_comm]

end RepeatedNRM.Myopic.Aux


namespace RepeatedNRM.Myopic.Aux

open RepeatedNRM.Myopic

variable (I : Instance)

lemma revenue_nonneg (hI : I.Standing) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) : 0 ≤ revenue I x := by
  unfold revenue
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact mul_nonneg (hI.2.1 i j) (hx.1 i j)

lemma x_le_s (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) (hx : feasible I b x)
    (i : Fin I.n) (j : Fin I.m) : x i j ≤ I.s i := by
  have h1 : x i j ≤ ∑ k, x i k :=
    Finset.single_le_sum (f := fun k => x i k) (fun k _ => hx.1 i k) (Finset.mem_univ j)
  exact h1.trans (hx.2.2 i)

lemma revenue_bdd (hI : I.Standing) (b : Fin I.m → ℝ) :
    BddAbove (revenue I '' {x | feasible I b x}) := by
  refine ⟨∑ i, ∑ j, I.p i j * I.s i, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  unfold revenue
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_left (x_le_s I b x hx i j) (hI.2.1 i j)

lemma le_MY (hI : I.Standing) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) : revenue I x ≤ MY I b :=
  le_csSup (revenue_bdd I hI b) ⟨x, hx, rfl⟩

lemma MY_le (b : Fin I.m → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ y, feasible I b y → revenue I y ≤ a) : MY I b ≤ a := by
  unfold MY
  apply Real.sSup_le _ ha
  rintro r ⟨y, hy, rfl⟩
  exact h y hy

lemma MY_eq_of_opt (hI : I.Standing) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) (hopt : ∀ y, feasible I b y → revenue I y ≤ revenue I x) :
    MY I b = revenue I x :=
  le_antisymm (MY_le I b _ (revenue_nonneg I hI b x hx) hopt) (le_MY I hI b x hx)

lemma MY_myopic (hI : I.Standing) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : IsMyopicAlloc I b x) : MY I b = revenue I x :=
  MY_eq_of_opt I hI b x hx.1 hx.2

lemma zero_feasible (hI : I.Standing) (b : Fin I.m → ℝ) (hb : ∀ j, 0 ≤ b j) :
    feasible I b (fun _ _ => 0) := by
  refine ⟨fun _ _ => le_refl _, fun j => by simpa using hb j, fun i => by simpa using hI.1 i⟩

lemma MY_nonneg (hI : I.Standing) (b : Fin I.m → ℝ) : 0 ≤ MY I b := by
  unfold MY
  apply Real.sSup_nonneg
  rintro r ⟨y, hy, rfl⟩
  exact revenue_nonneg I hI b y hy

lemma MY_mono (hI : I.Standing) (u w : Fin I.m → ℝ) (h : ∀ j, u j ≤ w j) :
    MY I u ≤ MY I w := by
  apply MY_le I u _ (MY_nonneg I hI w)
  intro y hy
  apply le_MY I hI w y
  exact ⟨hy.1, fun j => (hy.2.1 j).trans (h j), hy.2.2⟩

lemma MY_scale (hI : I.Standing) (u : Fin I.m → ℝ) (hu : ∀ j, 0 ≤ u j) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : a * MY I u ≤ MY I (fun j => a * u j) := by
  obtain ⟨x0, μ, lam, hx0, hopt, -, -⟩ := lp_attain I u ⟨_, zero_feasible I hI u hu⟩
  rw [MY_eq_of_opt I hI u x0 hx0 hopt]
  have hf : feasible I (fun j => a * u j) (fun i j => a * x0 i j) := by
    refine ⟨fun i j => mul_nonneg ha0 (hx0.1 i j), fun j => ?_, fun i => ?_⟩
    · have : ∑ i, I.p i j * (a * x0 i j) = a * ∑ i, I.p i j * x0 i j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [this]; exact mul_le_mul_of_nonneg_left (hx0.2.1 j) ha0
    · have : ∑ j, a * x0 i j = a * ∑ j, x0 i j := by rw [Finset.mul_sum]
      rw [this]
      calc a * ∑ j, x0 i j ≤ a * I.s i := mul_le_mul_of_nonneg_left (hx0.2.2 i) ha0
        _ ≤ 1 * I.s i := mul_le_mul_of_nonneg_right ha1 (hI.1 i)
        _ = I.s i := one_mul _
  have := le_MY I hI _ _ hf
  have e : revenue I (fun i j => a * x0 i j) = a * revenue I x0 := by
    unfold revenue; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  linarith

lemma dualObj_sub (b : Fin I.m → ℝ) (μ1 μ2 : Fin I.m → ℝ) (l1 l2 : Fin I.n → ℝ) :
    dualObj I b μ1 l1 - dualObj I b μ2 l2 =
      ∑ i, I.s i * (l1 i - l2 i) + ∑ j, b j * (μ1 j - μ2 j) := by
  unfold dualObj
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Complementary slackness of an optimal dual on slack budgets. -/
lemma cs_slack (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) (hx : feasible I b x)
    (μ : Fin I.m → ℝ) (lam : Fin I.n → ℝ) (h : DualFeasible I μ lam)
    (heq : dualObj I b μ lam = revenue I x) :
    ∀ j, μ j * spend I x j = μ j * b j := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hl, hm, hd⟩ := h
  have e1 : ∑ i, ∑ j, (lam i + I.p i j * μ j) * x i j =
      ∑ i, lam i * ∑ j, x i j + ∑ j, μ j * ∑ i, I.p i j * x i j := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    ring
  have A1 : revenue I x ≤ ∑ i, ∑ j, (lam i + I.p i j * μ j) * x i j := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_right (hd i j) (hx0 i j)
  have A2 : ∑ i, lam i * ∑ j, x i j ≤ ∑ i, lam i * I.s i := by
    apply Finset.sum_le_sum; intro i _
    exact mul_le_mul_of_nonneg_left (hx2 i) (hl i)
  have A3 : ∀ j, μ j * spend I x j ≤ μ j * b j := fun j =>
    mul_le_mul_of_nonneg_left (hx1 j) (hm j)
  have hobj : dualObj I b μ lam = ∑ i, lam i * I.s i + ∑ j, μ j * b j := by
    unfold dualObj
    congr 1
    · apply Finset.sum_congr rfl; intro i _; ring
    · apply Finset.sum_congr rfl; intro j _; ring
  have hsum : ∑ j, μ j * b j ≤ ∑ j, μ j * spend I x j := by
    unfold spend; linarith
  have hsum' : ∑ j, (μ j * b j - μ j * spend I x j) = 0 := by
    apply le_antisymm
    · rw [Finset.sum_sub_distrib]; linarith
    · apply Finset.sum_nonneg; intro j _; linarith [A3 j]
  intro j
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by linarith [A3 k])).1 hsum' j
    (Finset.mem_univ j)
  linarith

/-- Generalized dynamic complementary slackness: an optimal dual at any budget vector `u`
dominating the spends of a myopic allocation `x` (at `b`) vanishing on the customers whose
budget is slack under `x`. -/
lemma gdcs_dual (hI : I.Standing) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : IsMyopicAlloc I b x) (u : Fin I.m → ℝ) (hu : ∀ k, spend I x k ≤ u k) :
    ∃ μ lam, DualFeasible I μ lam ∧ dualObj I u μ lam = MY I u ∧
      (∀ μ' lam', DualFeasible I μ' lam' → dualObj I u μ lam ≤ dualObj I u μ' lam') ∧
      ∀ k, spend I x k < b k → μ k = 0 := by
  -- dual at b
  obtain ⟨x1, μs, ls, hx1, hopt1, hDs, hobjs⟩ := lp_attain I b ⟨x, hx.1⟩
  have hrx : revenue I x1 = revenue I x :=
    le_antisymm (hx.2 x1 hx1) (hopt1 x hx.1)
  rw [hrx] at hobjs
  have hcs := cs_slack I b x hx.1 μs ls hDs hobjs
  have hμs0 : ∀ k, spend I x k < b k → μs k = 0 := by
    intro k hk
    have h1 := hcs k
    by_contra hne
    have : spend I x k = b k := mul_left_cancel₀ hne h1
    linarith
  -- x feasible at u
  have hxu : feasible I u x := ⟨hx.1.1, fun k => hu k, hx.1.2.2⟩
  -- dual at u
  obtain ⟨x0, μ', l', hx0, hopt0, hD', hobj'⟩ := lp_attain I u ⟨x, hxu⟩
  have hMYu : MY I u = revenue I x0 := MY_eq_of_opt I hI u x0 hx0 hopt0
  let μ2 : Fin I.m → ℝ := fun k => min (μ' k) (μs k)
  let l2 : Fin I.n → ℝ := fun i => max (l' i) (ls i)
  let μ3 : Fin I.m → ℝ := fun k => max (μ' k) (μs k)
  let l3 : Fin I.n → ℝ := fun i => min (l' i) (ls i)
  have hD2 : DualFeasible I μ2 l2 := by
    refine ⟨fun i => le_max_of_le_left (hD'.1 i), fun k => le_min (hD'.2.1 k) (hDs.2.1 k), ?_⟩
    intro i j
    rcases min_choice (μ' j) (μs j) with h | h
    · have : μ2 j = μ' j := h
      rw [this]; linarith [hD'.2.2 i j, le_max_left (l' i) (ls i)]
    · have : μ2 j = μs j := h
      rw [this]; linarith [hDs.2.2 i j, le_max_right (l' i) (ls i)]
  have hD3 : DualFeasible I μ3 l3 := by
    refine ⟨fun i => le_min (hD'.1 i) (hDs.1 i), fun k => le_max_of_le_left (hD'.2.1 k), ?_⟩
    intro i j
    have hp := hI.2.1 i j
    rcases min_choice (l' i) (ls i) with h | h
    · have : l3 i = l' i := h
      rw [this]
      have := mul_le_mul_of_nonneg_left (le_max_left (μ' j) (μs j)) hp
      linarith [hD'.2.2 i j]
    · have : l3 i = ls i := h
      rw [this]
      have := mul_le_mul_of_nonneg_left (le_max_right (μ' j) (μs j)) hp
      linarith [hDs.2.2 i j]
  -- weak duality at S = spend x
  have hxS : feasible I (spend I x) x := ⟨hx.1.1, fun k => le_refl _, hx.1.2.2⟩
  have hw3 := weak_duality I (spend I x) x hxS μ3 l3 hD3
  have hobjS : dualObj I (spend I x) μs ls = revenue I x := by
    rw [← hobjs]; unfold dualObj; congr 1
    apply Finset.sum_congr rfl; intro k _
    rw [mul_comm, hcs k, mul_comm]
  -- key inequality
  have key : dualObj I u μ2 l2 ≤ dualObj I u μ' l' := by
    have e1 := dualObj_sub I u μ2 μ' l2 l'
    have e2 := dualObj_sub I (spend I x) μ3 μs l3 ls
    have hl : ∀ i, l2 i - l' i = ls i - l3 i := by
      intro i; simp only [l2, l3]
      rcases le_total (l' i) (ls i) with h | h
      · rw [max_eq_right h, min_eq_left h]
      · rw [max_eq_left h, min_eq_right h]; ring
    have hm : ∀ k, μ2 k - μ' k = μs k - μ3 k := by
      intro k; simp only [μ2, μ3]
      rcases le_total (μ' k) (μs k) with h | h
      · rw [min_eq_left h, max_eq_right h]; ring
      · rw [min_eq_right h, max_eq_left h]
    have hle : ∑ j, u j * (μ2 j - μ' j) ≤ ∑ j, spend I x j * (μ2 j - μ' j) := by
      apply Finset.sum_le_sum; intro j _
      have : μ2 j - μ' j ≤ 0 := by simp only [μ2]; linarith [min_le_left (μ' j) (μs j)]
      exact mul_le_mul_of_nonpos_right (hu j) this
    have e3 : ∑ i, I.s i * (l2 i - l' i) + ∑ j, spend I x j * (μ2 j - μ' j) =
        -(∑ i, I.s i * (l3 i - ls i) + ∑ j, spend I x j * (μ3 j - μs j)) := by
      rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl; intro i _; rw [hl i]; ring
      · apply Finset.sum_congr rfl; intro j _; rw [hm j]; ring
    linarith
  have hlow : MY I u ≤ dualObj I u μ2 l2 := by
    rw [hMYu]; exact weak_duality I u x0 hx0 μ2 l2 hD2
  refine ⟨μ2, l2, hD2, ?_, ?_, ?_⟩
  · apply le_antisymm _ hlow
    rw [hMYu, ← hobj']; exact key
  · intro μ'' l'' hD''
    calc dualObj I u μ2 l2 ≤ dualObj I u μ' l' := key
      _ = revenue I x0 := hobj'
      _ ≤ dualObj I u μ'' l'' := weak_duality I u x0 hx0 μ'' l'' hD''
  · intro k hk
    simp only [μ2]
    rw [hμs0 k hk]
    exact le_antisymm (min_le_right _ _) (le_min (hD'.2.1 k) (le_refl 0))

/-- Raising slack customers' budgets above `u` does not increase `MY`. -/
lemma gdcs (hI : I.Standing) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : IsMyopicAlloc I b x) (u w : Fin I.m → ℝ) (hu : ∀ k, spend I x k ≤ u k)
    (hw : ∀ k, ¬ spend I x k < b k → w k ≤ u k) : MY I w ≤ MY I u := by
  obtain ⟨μ, lam, hD, hobj, -, h0⟩ := gdcs_dual I hI b x hx u hu
  apply MY_le I w _ (MY_nonneg I hI u)
  intro y hy
  calc revenue I y ≤ dualObj I w μ lam := weak_duality I w y hy μ lam hD
    _ ≤ dualObj I u μ lam := by
        unfold dualObj
        apply add_le_add (le_refl _)
        apply Finset.sum_le_sum; intro k _
        by_cases hk : spend I x k < b k
        · rw [h0 k hk]; simp
        · exact mul_le_mul_of_nonneg_right (hw k hk) (hD.2.1 k)
    _ = MY I u := hobj

end RepeatedNRM.Myopic.Aux


namespace RepeatedNRM.Myopic.Aux

open RepeatedNRM.Myopic

variable (I : Instance)

lemma utility_nonneg (hI : I.Standing) (j : Fin I.m) (bj : ℝ) (y : Fin I.n → ℝ)
    (hy : custFeasible I j bj y) : 0 ≤ utility I j y := by
  unfold utility
  apply Finset.sum_nonneg; intro i _
  exact mul_nonneg (by linarith [hI.2.2.1 i j]) (hy.1 i).1

lemma utility_bdd (hI : I.Standing) (j : Fin I.m) (bj : ℝ) :
    BddAbove (utility I j '' {y | custFeasible I j bj y}) := by
  refine ⟨∑ i, (I.v i j - I.p i j) * I.s i, ?_⟩
  rintro r ⟨y, hy, rfl⟩
  unfold utility
  apply Finset.sum_le_sum; intro i _
  exact mul_le_mul_of_nonneg_left (hy.1 i).2 (by linarith [hI.2.2.1 i j])

lemma utility_le_uStar (hI : I.Standing) (j : Fin I.m) (bj : ℝ) (y : Fin I.n → ℝ)
    (hy : custFeasible I j bj y) : utility I j y ≤ uStar I j bj :=
  le_csSup (utility_bdd I hI j bj) ⟨y, hy, rfl⟩

lemma quality_mem (hI : I.Standing) (j : Fin I.m) (bj : ℝ) (y : Fin I.n → ℝ)
    (hy : custFeasible I j bj y) : quality I j bj y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold quality
  split_ifs with h
  · exact ⟨zero_le_one, le_refl _⟩
  · push Not at h
    have h0 := utility_nonneg I hI j bj y hy
    have h1 := utility_le_uStar I hI j bj y hy
    have hpos : 0 < uStar I j bj := lt_of_le_of_ne (h0.trans h1) (Ne.symm h.2)
    exact ⟨div_nonneg h0 hpos.le, (div_le_one hpos).2 h1⟩

lemma col_custFeasible (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) (hx : feasible I b x)
    (j : Fin I.m) : custFeasible I j (b j) (fun i => x i j) :=
  ⟨fun i => ⟨hx.1 i j, x_le_s I b x hx i j⟩, hx.2.1 j⟩

lemma qualityVec_mem (hI : I.Standing) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) (j : Fin I.m) : qualityVec I b x j ∈ Set.Icc (0 : ℝ) 1 :=
  quality_mem I hI j (b j) _ (col_custFeasible I b x hx j)

lemma sumA_eq (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ) (h2 : Assumption2 I A γ)
    (j : Fin I.m) (y : Fin I.n → ℝ) : ∑ i ∈ A j, I.p i j * y i = ∑ i, I.p i j * y i := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [(h2.2.1 j i hi).2, zero_mul]

/-- for any feasible allocation, `(1-γ) * spend ≤ quality` -/
lemma quality_ge_spend (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ)
    (h2 : Assumption2 I A γ) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) (j : Fin I.m) (hb : b j ∈ Set.Icc (0 : ℝ) 1) :
    (1 - γ) * spend I x j ≤ qualityVec I b x j := by
  have hec := ec5_quality_bound I hI A γ h2 j (b j) hb _ (col_custFeasible I b x hx j)
  have hq := qualityVec_mem I hI b x hx j
  have hg : 0 ≤ 1 - γ := by linarith [h2.1.2]
  rw [sumA_eq I A γ h2 j] at hec
  have hS0 : 0 ≤ spend I x j := by
    unfold spend; apply Finset.sum_nonneg; intro i _; exact mul_nonneg (hI.2.1 i j) (hx.1 i j)
  have hSb : spend I x j ≤ b j := hx.2.1 j
  have hSP : spend I x j ≤ ∑ i ∈ A j, I.p i j * I.s i := by
    unfold spend; rw [← sumA_eq I A γ h2 j]
    apply Finset.sum_le_sum; intro i _
    exact mul_le_mul_of_nonneg_left (x_le_s I b x hx i j) (hI.2.1 i j)
  set M := min (b j) (∑ i ∈ A j, I.p i j * I.s i) with hM
  have hSM : spend I x j ≤ M := le_min hSb hSP
  have hM1 : M ≤ 1 := (min_le_left _ _).trans hb.2
  rcases eq_or_lt_of_le (hS0.trans hSM) with h | h
  · have : spend I x j = 0 := le_antisymm (h ▸ hSM) hS0
    rw [this, mul_zero]; exact hq.1
  · have : spend I x j ≤ spend I x j / M := by
      rw [le_div_iff₀ h]
      calc spend I x j * M ≤ spend I x j * 1 := mul_le_mul_of_nonneg_left hM1 hS0
        _ = spend I x j := mul_one _
    calc (1 - γ) * spend I x j ≤ (1 - γ) * (spend I x j / M) :=
          mul_le_mul_of_nonneg_left this hg
      _ ≤ _ := by unfold qualityVec spend at *; exact hec

/-- a customer whose budget binds receives quality at least `1-γ` -/
lemma quality_ge_of_tight (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ)
    (h2 : Assumption2 I A γ) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) (j : Fin I.m) (hb : b j ∈ Set.Icc (0 : ℝ) 1)
    (htight : ¬ spend I x j < b j) : 1 - γ ≤ qualityVec I b x j := by
  have hSb : spend I x j = b j := le_antisymm (hx.2.1 j) (not_lt.1 htight)
  rcases eq_or_lt_of_le hb.1 with h0 | hpos
  · unfold qualityVec quality
    rw [if_pos (Or.inl h0.symm)]; linarith [h2.1.1]
  · have hec := ec5_quality_bound I hI A γ h2 j (b j) hb _ (col_custFeasible I b x hx j)
    rw [sumA_eq I A γ h2 j] at hec
    have hSP : spend I x j ≤ ∑ i ∈ A j, I.p i j * I.s i := by
      unfold spend; rw [← sumA_eq I A γ h2 j]
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (x_le_s I b x hx i j) (hI.2.1 i j)
    have hmin : min (b j) (∑ i ∈ A j, I.p i j * I.s i) = b j := min_eq_left (hSb ▸ hSP)
    have : (∑ i, I.p i j * x i j) = b j := hSb
    rw [this, hmin, div_self hpos.ne', mul_one] at hec
    exact hec

lemma phiIter_succ (j : Fin I.m) (t : ℕ) (b q : ℝ) :
    phiIter I j (t + 1) b q = I.phi j (phiIter I j t b q) q := by
  unfold phiIter
  rw [Function.iterate_succ_apply']

lemma phiIter_zero (j : Fin I.m) (b q : ℝ) : phiIter I j 0 b q = b := rfl

lemma phiIter_mem (hI : I.Standing) (j : Fin I.m) (b q : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) : phiIter I j t b q ∈ Set.Icc (0 : ℝ) 1 := by
  induction t with
  | zero => exact hb
  | succ t ih => rw [phiIter_succ]; exact hI.2.2.2 j _ q ih hq

section traj

variable (hI : I.Standing) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
  (xMY : ℕ → Fin I.n → Fin I.m → ℝ) (bMY : ℕ → Fin I.m → ℝ)
  (hMY : IsMyopicTrajectory I b1 xMY bMY)
include hI hb1 hMY

lemma traj_mem : ∀ t j, bMY t j ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => intro j; rw [hMY.1.1]; exact hb1 j
  | succ t ih =>
    intro j
    rw [(hMY.1.2 t).2]
    exact hI.2.2.2 j _ _ (ih j) (qualityVec_mem I hI _ _ (hMY.1.2 t).1 j)

lemma traj_step (t : ℕ) (j : Fin I.m) :
    bMY (t + 1) j = I.phi j (bMY t j) (qualityVec I (bMY t) (xMY t) j) := by
  rw [(hMY.1.2 t).2]; rfl

lemma traj_le_relax (h1i : ∀ j, Assumption1i I j) :
    ∀ t j, bMY t j ≤ phiIterVec I t b1 1 j := by
  intro t
  induction t with
  | zero => intro j; rw [hMY.1.1]; rfl
  | succ t ih =>
    intro j
    rw [traj_step I hI b1 hb1 xMY bMY hMY]
    unfold phiIterVec; rw [phiIter_succ]
    have hq := qualityVec_mem I hI _ _ (hMY.1.2 t).1 j
    have hbm := traj_mem I hI b1 hb1 xMY bMY hMY t j
    have hBm := phiIter_mem I hI j (b1 j) 1 (hb1 j) ⟨zero_le_one, le_refl _⟩ t
    have one_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
    calc I.phi j (bMY t j) (qualityVec I (bMY t) (xMY t) j) ≤ I.phi j (bMY t j) 1 :=
          (h1i j).2 _ _ _ hbm one_mem hq hq.2
      _ ≤ I.phi j (phiIter I j t (b1 j) 1) 1 := (h1i j).1 1 _ _ one_mem hBm hbm (ih j)

end traj

lemma relax_mono (hI : I.Standing) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (h1ii : ∀ j, Assumption1ii I j) (j : Fin I.m) :
    ∀ t d, phiIterVec I t b1 1 j ≤ phiIterVec I (t + d) b1 1 j := by
  intro t d
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
    refine ih.trans ?_
    unfold phiIterVec
    rw [← add_assoc, phiIter_succ]
    have hm := phiIter_mem I hI j (b1 j) 1 (hb1 j) ⟨zero_le_one, le_refl _⟩ (t + d)
    have := h1ii j _ 1 hm ⟨zero_le_one, le_refl _⟩
    rwa [min_eq_left hm.2] at this

end RepeatedNRM.Myopic.Aux


namespace RepeatedNRM.Myopic.Aux

open RepeatedNRM.Myopic

variable (I : Instance)

section traj2

variable (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ) (h2 : Assumption2 I A γ)
  (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
  (xMY : ℕ → Fin I.n → Fin I.m → ℝ) (bMY : ℕ → Fin I.m → ℝ)
  (hMY : IsMyopicTrajectory I b1 xMY bMY)
include hI h2 hb1 hMY

lemma traj_ge_LB (h1i : ∀ j, Assumption1i I j) :
    ∀ t k, (∀ τ < t, ¬ spend I (xMY τ) k < bMY τ k) →
      phiIterVec I t b1 (1 - γ) k ≤ bMY t k := by
  have hg : 1 - γ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [h2.1.2], by linarith [h2.1.1]⟩
  intro t
  induction t with
  | zero => intro k _; rw [hMY.1.1]; rfl
  | succ t ih =>
    intro k hk
    have ih' := ih k (fun τ hτ => hk τ (by omega))
    rw [traj_step I hI b1 hb1 xMY bMY hMY]
    unfold phiIterVec at *; rw [phiIter_succ]
    have hq := qualityVec_mem I hI _ _ (hMY.1.2 t).1 k
    have hbm := traj_mem I hI b1 hb1 xMY bMY hMY t k
    have hcm := phiIter_mem I hI k (b1 k) (1 - γ) (hb1 k) hg t
    have hqg : 1 - γ ≤ qualityVec I (bMY t) (xMY t) k :=
      quality_ge_of_tight I hI A γ h2 _ _ (hMY.1.2 t).1 k hbm (hk t (by omega))
    calc I.phi k (phiIter I k t (b1 k) (1 - γ)) (1 - γ) ≤ I.phi k (bMY t k) (1 - γ) :=
          (h1i k).1 _ _ _ hg hbm hcm ih'
      _ ≤ I.phi k (bMY t k) (qualityVec I (bMY t) (xMY t) k) :=
          (h1i k).2 _ _ _ hbm hq hg hqg

lemma traj_retain (h1ii : ∀ j, Assumption1ii I j) (τ : ℕ) (k : Fin I.m) :
    ∀ d, (∀ σ, τ < σ → σ < τ + 1 + d → ¬ spend I (xMY σ) k < bMY σ k) →
      (1 - γ) * spend I (xMY τ) k ≤ bMY (τ + 1 + d) k := by
  have hg0 : 0 ≤ 1 - γ := by linarith [h2.1.2]
  have hg1 : 1 - γ ≤ 1 := by linarith [h2.1.1]
  have hbτ := traj_mem I hI b1 hb1 xMY bMY hMY τ k
  have hfτ := (hMY.1.2 τ).1
  have hS0 : 0 ≤ spend I (xMY τ) k := by
    unfold spend; apply Finset.sum_nonneg; intro i _
    exact mul_nonneg (hI.2.1 i k) (hfτ.1 i k)
  have hSb : spend I (xMY τ) k ≤ bMY τ k := hfτ.2.1 k
  have hS1 : (1 - γ) * spend I (xMY τ) k ≤ 1 - γ := by
    have := hSb.trans hbτ.2
    calc (1 - γ) * spend I (xMY τ) k ≤ (1 - γ) * 1 := mul_le_mul_of_nonneg_left this hg0
      _ = 1 - γ := mul_one _
  intro d
  induction d with
  | zero =>
    intro _
    rw [add_zero, traj_step I hI b1 hb1 xMY bMY hMY]
    have hq := qualityVec_mem I hI _ _ hfτ k
    refine le_trans ?_ (h1ii k _ _ hbτ hq)
    apply le_min
    · calc (1 - γ) * spend I (xMY τ) k ≤ 1 * spend I (xMY τ) k :=
            mul_le_mul_of_nonneg_right hg1 hS0
        _ ≤ bMY τ k := by rw [one_mul]; exact hSb
    · exact quality_ge_spend I hI A γ h2 _ _ hfτ k hbτ
  | succ d ih =>
    intro hk
    have ih' := ih (fun σ h1 h2 => hk σ h1 (by omega))
    have e : τ + 1 + (d + 1) = (τ + 1 + d) + 1 := by omega
    rw [e, traj_step I hI b1 hb1 xMY bMY hMY]
    set σ := τ + 1 + d
    have hfσ := (hMY.1.2 σ).1
    have hbσ := traj_mem I hI b1 hb1 xMY bMY hMY σ k
    have hq := qualityVec_mem I hI _ _ hfσ k
    have hqg : 1 - γ ≤ qualityVec I (bMY σ) (xMY σ) k :=
      quality_ge_of_tight I hI A γ h2 _ _ hfσ k hbσ (hk σ (by omega) (by omega))
    refine le_trans ?_ (h1ii k _ _ hbσ hq)
    exact le_min ih' (hS1.trans hqg)

/-- Per-period guarantee: the myopic revenue in period `t` is at least `(1-γ)` times the
revenue of the relaxation in that period. -/
theorem per_period (h1i : ∀ j, Assumption1i I j) (h1ii : ∀ j, Assumption1ii I j)
    (hc : ∀ t j, (1 - γ) * phiIterVec I t b1 1 j ≤ phiIterVec I t b1 (1 - γ) j) (t : ℕ) :
    (1 - γ) * MY I (phiIterVec I t b1 1) ≤ MY I (bMY t) := by
  classical
  by_cases hγ1 : γ = 1
  · rw [hγ1, sub_self, zero_mul]; exact MY_nonneg I hI _
  have hg : 0 < 1 - γ := by
    have := h2.1.2; rcases eq_or_lt_of_le this with h | h
    · exact absurd h hγ1
    · linarith
  set B := phiIterVec I t b1 1 with hB
  have hBm : ∀ k, B k ∈ Set.Icc (0 : ℝ) 1 := fun k =>
    phiIter_mem I hI k (b1 k) 1 (hb1 k) ⟨zero_le_one, le_refl _⟩ t
  let slack : ℕ → Fin I.m → Prop := fun τ k => spend I (xMY τ) k < bMY τ k
  let E : Fin I.m → Prop := fun k => ∃ τ, τ < t ∧ slack τ k
  let uh : Fin I.m → ℝ := fun k => if E k then bMY t k / (1 - γ) else B k
  let big : Fin I.m → ℝ := fun k => max (B k) (uh k)
  let cond : ℕ → Fin I.m → Prop := fun σ k => ∃ τ, σ ≤ τ ∧ τ < t ∧ slack τ k
  let w : ℕ → Fin I.m → ℝ := fun σ k => if cond σ k then big k else uh k
  have hBσ : ∀ σ, σ ≤ t → ∀ k, bMY σ k ≤ B k := by
    intro σ hσ k
    have h1 := traj_le_relax I hI b1 hb1 xMY bMY hMY h1i σ k
    have h2' := relax_mono I hI b1 hb1 h1ii k σ (t - σ)
    rw [show σ + (t - σ) = t by omega] at h2'
    exact h1.trans h2'
  have step : ∀ σ, σ < t → MY I (w σ) ≤ MY I (w (σ + 1)) := by
    intro σ hσ
    apply gdcs I hI (bMY σ) (xMY σ) (hMY.2 σ) (w (σ + 1)) (w σ)
    · intro k
      have hS : spend I (xMY σ) k ≤ B k := ((hMY.1.2 σ).1.2.1 k).trans (hBσ σ hσ.le k)
      simp only [w]
      split_ifs with hc1
      · exact hS.trans (le_max_left _ _)
      · simp only [uh]
        split_ifs with hE
        · rw [le_div_iff₀ hg, mul_comm]
          have hret := traj_retain I hI A γ h2 b1 hb1 xMY bMY hMY h1ii σ k (t - σ - 1)
            (by
              intro ρ h1 h2'
              intro hs
              exact hc1 ⟨ρ, by omega, by omega, hs⟩)
          rwa [show σ + 1 + (t - σ - 1) = t by omega] at hret
        · exact hS
    · intro k hk
      have : cond σ k ↔ cond (σ + 1) k := by
        constructor
        · rintro ⟨τ, h1, h2', h3⟩
          refine ⟨τ, ?_, h2', h3⟩
          rcases eq_or_lt_of_le h1 with h | h
          · subst h; exact absurd h3 hk
          · omega
        · rintro ⟨τ, h1, h2', h3⟩; exact ⟨τ, by omega, h2', h3⟩
      simp only [w]
      by_cases h : cond σ k
      · rw [if_pos h, if_pos (this.1 h)]
      · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]
  have chain : ∀ n, MY I (w (t - n)) ≤ MY I (w t) := by
    intro n
    induction n with
    | zero => exact le_refl _
    | succ n ih =>
      by_cases hn : n < t
      · have := step (t - (n + 1)) (by omega)
        rw [show t - (n + 1) + 1 = t - n by omega] at this
        exact this.trans ih
      · rw [show t - (n + 1) = t - n by omega]; exact ih
  have hwt : w t = uh := by
    funext k; simp only [w]
    rw [if_neg]; rintro ⟨τ, h1, h2', _⟩; omega
  have hB0 : MY I B ≤ MY I (w 0) := by
    apply MY_mono I hI
    intro k
    simp only [w]
    split_ifs with hc0
    · exact le_max_left _ _
    · simp only [uh]
      rw [if_neg]
      rintro ⟨τ, h1, h2'⟩
      exact hc0 ⟨τ, Nat.zero_le _, h1, h2'⟩
  have huh0 : ∀ k, 0 ≤ uh k := by
    intro k; simp only [uh]
    split_ifs
    · exact div_nonneg (traj_mem I hI b1 hb1 xMY bMY hMY t k).1 hg.le
    · exact (hBm k).1
  have hscale : ∀ k, (1 - γ) * uh k ≤ bMY t k := by
    intro k; simp only [uh]
    split_ifs with hE
    · rw [mul_div_cancel₀ _ hg.ne']
    · have hnot : ∀ τ < t, ¬ spend I (xMY τ) k < bMY τ k := by
        intro τ hτ hs; exact hE ⟨τ, hτ, hs⟩
      exact (hc t k).trans (traj_ge_LB I hI A γ h2 b1 hb1 xMY bMY hMY h1i t k hnot)
  have h0 := chain t
  rw [Nat.sub_self, hwt] at h0
  calc (1 - γ) * MY I B ≤ (1 - γ) * MY I uh :=
        mul_le_mul_of_nonneg_left (hB0.trans h0) hg.le
    _ ≤ MY I (fun k => (1 - γ) * uh k) := MY_scale I hI uh huh0 _ hg.le (by linarith [h2.1.1])
    _ ≤ MY I (bMY t) := MY_mono I hI _ _ hscale

end traj2

end RepeatedNRM.Myopic.Aux

open RepeatedNRM.Myopic RepeatedNRM.Myopic.Aux in
theorem solution (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ)
    (h1 : ∀ j, Assumption1i I j ∧ Assumption1ii I j ∧ Assumption1iii I j)
    (h2 : Assumption2 I A γ) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1) (T : ℕ)
    (xMY : ℕ → Fin I.n → Fin I.m → ℝ) (bMY : ℕ → Fin I.m → ℝ)
    (hMY : IsMyopicTrajectory I b1 xMY bMY)
    (x : ℕ → Fin I.n → Fin I.m → ℝ) (b : ℕ → Fin I.m → ℝ) (hx : IsTrajectory I b1 x b) :
    (1 - γ) * ∑ t ∈ Finset.range T, revenue I (x t) ≤ ∑ t ∈ Finset.range T, revenue I (xMY t) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  have hg0 : 0 ≤ 1 - γ := by linarith [h2.1.2]
  have hp2 := proposition_2 I hI (fun j => (h1 j).1) b1 hb1 T hT x b hx
  have hc : ∀ t j, (1 - γ) * phiIterVec I t b1 1 j ≤ phiIterVec I t b1 (1 - γ) j := by
    intro t j
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      show (1 - γ) * b1 j ≤ b1 j
      have := (hb1 j).1
      nlinarith [h2.1.1]
    · exact (h1 j).2.2 (b1 j) (hb1 j) t ht γ h2.1
  calc (1 - γ) * ∑ t ∈ Finset.range T, revenue I (x t) ≤ (1 - γ) * Jrelax I T b1 :=
        mul_le_mul_of_nonneg_left hp2 hg0
    _ = ∑ t ∈ Finset.range T, (1 - γ) * MY I (phiIterVec I t b1 1) := by
        unfold Jrelax; rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range T, MY I (bMY t) := by
        apply Finset.sum_le_sum; intro t _
        exact per_period I hI A γ h2 b1 hb1 xMY bMY hMY (fun j => (h1 j).1)
          (fun j => (h1 j).2.1) hc t
    _ = ∑ t ∈ Finset.range T, revenue I (xMY t) := by
        apply Finset.sum_congr rfl; intro t _
        exact MY_myopic I hI _ _ (hMY.2 t)
