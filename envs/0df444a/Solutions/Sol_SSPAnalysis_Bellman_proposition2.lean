-- Prove2me | solution 1 for SSPAnalysis.Bellman.proposition2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T16:09:04.542055+00:00
-- url     : https://prove2.me/submissions/e5f879dc-14b4-468f-9818-e34f4d244650

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

set_option autoImplicit false

namespace SSPAnalysis.Bellman.P2Aux

open SSPAnalysis.Bellman Matrix Filter Topology

variable {n : ℕ} {U : Fin n → Type*} (m : Model n U)

theorem P_nonneg (μ : Selector U) (i j : Fin n) : 0 ≤ m.P μ i j := m.p_nonneg i (μ i) j

theorem P_rowsum (μ : Selector U) (i : Fin n) : ∑ j, m.P μ i j = 1 := m.p_sum_one i (μ i)

theorem Ppow_nonneg (μ : Selector U) : ∀ (t : ℕ) (i j : Fin n), 0 ≤ (m.P μ ^ t) i j := by
  intro t
  induction t with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ t ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (P_nonneg m μ l j)

theorem Ppow_rowsum (μ : Selector U) : ∀ (t : ℕ) (i : Fin n), ∑ j, (m.P μ ^ t) i j = 1 := by
  intro t
  induction t with
  | zero => intro i; simp [Matrix.one_apply]
  | succ t ih =>
    intro i
    simp_rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, P_rowsum, mul_one]
    exact ih i

theorem mulVec_mono (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {x y : Fin n → ℝ} (h : ∀ j, x j ≤ y j) (i : Fin n) : (A *ᵥ x) i ≤ (A *ᵥ y) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hA i j)

theorem Tmu_apply (μ : Selector U) (x : Fin n → ℝ) (i : Fin n) :
    m.Tmu μ x i = m.c i (μ i) + ∑ j, m.p i (μ i) j * x j := by
  simp [Model.Tmu, Model.cvec, Model.P, Matrix.mulVec, dotProduct]

theorem Tmu_mono (μ : Selector U) {x y : Fin n → ℝ} (h : ∀ j, x j ≤ y j) (i : Fin n) :
    m.Tmu μ x i ≤ m.Tmu μ y i := by
  rw [Tmu_apply, Tmu_apply]
  have : ∑ j, m.p i (μ i) j * x j ≤ ∑ j, m.p i (μ i) j * y j :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (m.p_nonneg _ _ _)
  linarith

theorem Tmu_add_const (μ : Selector U) (x : Fin n → ℝ) (C : ℝ) (i : Fin n) :
    m.Tmu μ (fun j => x j + C) i = m.Tmu μ x i + C := by
  rw [Tmu_apply, Tmu_apply]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, m.p_sum_one, one_mul]
  ring

theorem Tmu_sub (μ : Selector U) (x y : Fin n → ℝ) :
    m.Tmu μ x - m.Tmu μ y = m.P μ *ᵥ (x - y) := by
  simp only [Model.Tmu, Matrix.mulVec_sub]
  abel

theorem p0_eq [NeZero n] (h1 : m.Assumption1) (u : U 0) (j : Fin n) :
    m.p 0 u j = if j = 0 then 1 else 0 := by
  have hs := m.p_sum_one 0 u
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), h1.absorbing u] at hs
  have hz : ∑ x ∈ Finset.univ.erase 0, m.p 0 u x = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => m.p_nonneg 0 u x)] at hz
  split_ifs with hj
  · subst hj; exact h1.absorbing u
  · exact hz j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)

theorem P_mulVec_zero [NeZero n] (h1 : m.Assumption1) (μ : Selector U) (x : Fin n → ℝ) :
    (m.P μ *ᵥ x) 0 = x 0 := by
  simp [Matrix.mulVec, dotProduct, Model.P, p0_eq m h1]

theorem Tmu_zero [NeZero n] (h1 : m.Assumption1) (μ : Selector U) (x : Fin n → ℝ) :
    m.Tmu μ x 0 = x 0 := by
  rw [Tmu_apply, h1.cost_free]
  simp [p0_eq m h1]

theorem Ppow_mulVec_zero [NeZero n] (h1 : m.Assumption1) (μ : Selector U) :
    ∀ (t : ℕ) (z : Fin n → ℝ), (m.P μ ^ t *ᵥ z) 0 = z 0 := by
  intro t
  induction t with
  | zero => intro z; simp
  | succ t ih =>
    intro z
    rw [pow_succ', ← Matrix.mulVec_mulVec, P_mulVec_zero m h1, ih]

theorem iterate_sub (μ : Selector U) : ∀ (k : ℕ) (x y : Fin n → ℝ),
    (m.Tmu μ)^[k] x - (m.Tmu μ)^[k] y = m.P μ ^ k *ᵥ (x - y) := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Tmu_sub, ih,
      Matrix.mulVec_mulVec, ← pow_succ']

theorem sum_eq_iterate (μ : Selector U) : ∀ k : ℕ,
    ∑ t ∈ Finset.range (k + 1), m.P μ ^ t *ᵥ m.cvec μ = (m.Tmu μ)^[k+1] 0 := by
  intro k
  induction k with
  | zero => simp [Model.Tmu]
  | succ k ih =>
    rw [Finset.sum_range_succ', Function.iterate_succ_apply', ← ih]
    have : ∀ t : ℕ, m.P μ ^ (t + 1) *ᵥ m.cvec μ = m.P μ *ᵥ (m.P μ ^ t *ᵥ m.cvec μ) := by
      intro t; rw [pow_succ', Matrix.mulVec_mulVec]
    simp only [this, ← Matrix.mulVec_sum, pow_zero, Matrix.one_mulVec, Model.Tmu]
    abel

theorem transProd_succ (π : Policy U) : ∀ t : ℕ,
    m.transProd π (t + 1) = m.P (π 0) * m.transProd (fun s => π (s + 1)) t := by
  intro t
  induction t with
  | zero => simp [Model.transProd]
  | succ t ih =>
    rw [show m.transProd π (t + 1 + 1) = m.transProd π (t + 1) * m.P (π (t + 1)) from rfl, ih,
      mul_assoc]
    rfl

theorem partialCost_zero (π : Policy U) : m.partialCost π 0 = m.Tmu (π 0) 0 := by
  simp [Model.partialCost, Model.transProd, Model.Tmu]

theorem partialCost_succ (π : Policy U) (k : ℕ) :
    m.partialCost π (k + 1) = m.Tmu (π 0) (m.partialCost (fun s => π (s + 1)) k) := by
  unfold Model.partialCost
  rw [Finset.sum_range_succ']
  have : ∀ t : ℕ, m.transProd π (t + 1) *ᵥ m.cvec (π (t + 1)) =
      m.P (π 0) *ᵥ (m.transProd (fun s => π (s + 1)) t *ᵥ m.cvec (π (t + 1))) := by
    intro t; rw [transProd_succ, Matrix.mulVec_mulVec]
  simp only [this, ← Matrix.mulVec_sum, Model.Tmu]
  simp only [show m.transProd π 0 = 1 from rfl, Matrix.one_mulVec]
  abel

theorem partialCost_stationary (μ : Selector U) : ∀ k : ℕ,
    m.partialCost (stationary μ) k = (m.Tmu μ)^[k+1] 0 := by
  intro k
  induction k with
  | zero => rw [partialCost_zero]; rfl
  | succ k ih =>
    rw [partialCost_succ, Function.iterate_succ_apply']
    exact congrArg (m.Tmu μ) ih

theorem closed_pow (Q : Matrix (Fin n) (Fin n) ℝ) (S : Set (Fin n))
    (hQ : ∀ i ∈ S, ∀ j ∉ S, Q i j = 0) : ∀ t : ℕ, ∀ i ∈ S, ∀ j ∉ S, (Q ^ t) i j = 0 := by
  intro t
  induction t with
  | zero =>
    intro i hi j hj
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl; exact hj hi
  | succ t ih =>
    intro i hi j hj
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l ∈ S
    · rw [hQ l hl j hj, mul_zero]
    · rw [ih i hi l hl, zero_mul]

/-- A real supersolution of `T_μ` forces properness. -/
theorem proper_of_super [NeZero n] (h1 : m.Assumption1) (μ : Selector U) (x : Fin n → ℝ)
    (hx : ∀ i, m.Tmu μ x i ≤ x i) : m.IsProper μ := by
  by_contra hμ
  obtain ⟨i, hi⟩ := h1.improper_infinite μ hμ
  have hz0 : ∀ j, 0 ≤ x j + -(Finset.univ.inf' Finset.univ_nonempty x) := fun j => by
    have := Finset.inf'_le x (Finset.mem_univ j); linarith
  have hzs : ∀ j, m.Tmu μ (fun l => x l + -(Finset.univ.inf' Finset.univ_nonempty x)) j ≤
      x j + -(Finset.univ.inf' Finset.univ_nonempty x) := fun j => by
    rw [Tmu_add_const]; have := hx j; linarith
  have hit : ∀ (k : ℕ) (j : Fin n), (m.Tmu μ)^[k] 0 j ≤
      x j + -(Finset.univ.inf' Finset.univ_nonempty x) := by
    intro k
    induction k with
    | zero => intro j; simpa using hz0 j
    | succ k ih =>
      intro j
      rw [Function.iterate_succ_apply']
      exact (Tmu_mono m μ ih j).trans (hzs j)
  obtain ⟨k, hk⟩ := (hi.eventually_gt_atTop (x i + -(Finset.univ.inf' Finset.univ_nonempty x))).exists
  rw [sum_eq_iterate] at hk
  linarith [hit (k + 1) i]

theorem Ppow_le [NeZero n] (μ : Selector U) (t : ℕ) (i j : Fin n) (hj : j ≠ 0) :
    (m.P μ ^ t) i j ≤ 1 - (m.P μ ^ t) i 0 := by
  have hs := Ppow_rowsum m μ t i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at hs
  have := Finset.single_le_sum (f := fun l => (m.P μ ^ t) i l)
    (fun l _ => Ppow_nonneg m μ t i l) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
  linarith

theorem pow_tendsto_zero [NeZero n] (μ : Selector U) (hμ : m.IsProper μ) (z : Fin n → ℝ)
    (hz : z ∈ X n) : Tendsto (fun t : ℕ => m.P μ ^ t *ᵥ z) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [show (0 : ℝ) = ∑ j : Fin n, (0 : ℝ) by simp]
  apply tendsto_finsetSum
  intro j _
  by_cases hj : j = 0
  · subst hj
    have : z 0 = 0 := hz
    simp [this]
  · have hup : Tendsto (fun t : ℕ => 1 - (m.P μ ^ t) i 0) atTop (𝓝 0) := by
      have := (hμ i).const_sub (1 : ℝ); simpa using this
    have hP : Tendsto (fun t : ℕ => (m.P μ ^ t) i j) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun t => Ppow_nonneg m μ t i j) (fun t => Ppow_le m μ t i j hj)
    simpa using hP.mul_const (z j)

theorem super_nonneg [NeZero n] (μ : Selector U) (hμ : m.IsProper μ) (z : Fin n → ℝ)
    (hz : z ∈ X n) (hsup : ∀ i, (m.P μ *ᵥ z) i ≤ z i) : ∀ i, 0 ≤ z i := by
  have hit : ∀ (t : ℕ) (i : Fin n), (m.P μ ^ t *ᵥ z) i ≤ z i := by
    intro t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      rw [pow_succ, ← Matrix.mulVec_mulVec]
      exact (mulVec_mono (m.P μ ^ t) (Ppow_nonneg m μ t) hsup i).trans (ih i)
  intro i
  have := (continuous_apply i).continuousAt.tendsto.comp (pow_tendsto_zero m μ hμ z hz)
  exact le_of_tendsto' this fun t => hit t i

theorem iterate_tendsto [NeZero n] (μ : Selector U) (hμ : m.IsProper μ) (xs : Fin n → ℝ)
    (hxs : xs ∈ X n) (hfix : m.Tmu μ xs = xs) (x : Fin n → ℝ) (hx : x ∈ X n) :
    Tendsto (fun t : ℕ => (m.Tmu μ)^[t] x) atTop (𝓝 xs) := by
  have hd : x - xs ∈ X n := by
    show (x - xs) 0 = 0
    have h1' : x 0 = 0 := hx
    have h2' : xs 0 = 0 := hxs
    simp [h1', h2']
  have h := (pow_tendsto_zero m μ hμ (x - xs) hd).add_const xs
  simp only [zero_add] at h
  refine h.congr fun t => ?_
  rw [← iterate_sub, Function.iterate_fixed hfix]
  abel

section TOps

variable [∀ i, MetricSpace (U i)]

theorem exists_min [NeZero n] (h1 : m.Assumption1) (h2 : m.Assumption2) (x : Fin n → ℝ)
    (i : Fin n) : ∃ u : U i, ∀ u' : U i,
      m.c i u + ∑ j, m.p i u j * x j ≤ m.c i u' + ∑ j, m.p i u' j * x j := by
  obtain ⟨μ, -⟩ := h1.exists_proper
  have hlsc : LowerSemicontinuous fun u : U i => m.c i u + ∑ j, m.p i u j * x j :=
    (h2.lsc i).add (continuous_finsetSum _ fun j _ =>
      (h2.cont i j).mul continuous_const).lowerSemicontinuous
  obtain ⟨a, -, ha⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨μ i, Set.mem_univ _⟩
    (h2.compact i) (hlsc.lowerSemicontinuousOn _)
  exact ⟨a, fun u' => (isMinOn_iff.1 ha) u' (Set.mem_univ _)⟩

noncomputable def greedy [NeZero n] (h1 : m.Assumption1) (h2 : m.Assumption2)
    (x : Fin n → ℝ) : Selector U :=
  fun i => Classical.choose (exists_min m h1 h2 x i)

theorem T_le_Tmu [NeZero n] (h1 : m.Assumption1) (h2 : m.Assumption2) (μ : Selector U)
    (x : Fin n → ℝ) (i : Fin n) : m.T x i ≤ m.Tmu μ x i := by
  obtain ⟨a, ha⟩ := exists_min m h1 h2 x i
  rw [Tmu_apply]
  exact ciInf_le ⟨_, Set.forall_mem_range.2 ha⟩ (μ i)

theorem T_eq_greedy [NeZero n] (h1 : m.Assumption1) (h2 : m.Assumption2) (x : Fin n → ℝ)
    (i : Fin n) : m.T x i = m.Tmu (greedy m h1 h2 x) x i := by
  apply le_antisymm (T_le_Tmu m h1 h2 _ x i)
  have hs := Classical.choose_spec (exists_min m h1 h2 x i)
  have : Nonempty (U i) := ⟨Classical.choose (exists_min m h1 h2 x i)⟩
  rw [Tmu_apply]
  exact le_ciInf fun u => hs u

theorem T_mono [NeZero n] (h1 : m.Assumption1) (h2 : m.Assumption2) {x y : Fin n → ℝ}
    (h : ∀ j, x j ≤ y j) (i : Fin n) : m.T x i ≤ m.T y i := by
  rw [T_eq_greedy m h1 h2 y i]
  exact (T_le_Tmu m h1 h2 _ x i).trans (Tmu_mono m _ h i)

theorem T_add_le [NeZero n] (h1 : m.Assumption1) (h2 : m.Assumption2) {x y : Fin n → ℝ}
    (δ : ℝ) (h : ∀ j, y j ≤ x j + δ) (i : Fin n) : m.T y i ≤ m.T x i + δ := by
  rw [T_eq_greedy m h1 h2 x i, ← Tmu_add_const]
  exact (T_le_Tmu m h1 h2 _ y i).trans (Tmu_mono m _ h i)

theorem T_zero [NeZero n] (h1 : m.Assumption1) (h2 : m.Assumption2) (x : Fin n → ℝ) :
    m.T x 0 = x 0 := by
  rw [T_eq_greedy m h1 h2, Tmu_zero m h1]

theorem T_continuous [NeZero n] (h1 : m.Assumption1) (h2 : m.Assumption2) :
    Continuous m.T := by
  apply continuous_pi
  intro i
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_le_add
  intro x y
  show m.T x i ≤ m.T y i + dist x y
  apply T_add_le m h1 h2
  intro j
  have := dist_le_pi_dist x y j
  rw [Real.dist_eq] at this
  linarith [le_abs_self (x j - y j)]

end TOps

theorem exists_super [NeZero n] (h1 : m.Assumption1) (μ : Selector U) (hμ : m.IsProper μ) :
    ∃ x0 ∈ X n, ∀ i, m.Tmu μ x0 i ≤ x0 i := by
  obtain ⟨K, hK⟩ := (Filter.eventually_all.2 fun i =>
    (hμ i).eventually_const_le (by norm_num : (1/2 : ℝ) < 1)).exists
  obtain ⟨e, he⟩ : ∃ e : Fin n → ℝ, e = fun j => if j = 0 then 0 else 1 := ⟨_, rfl⟩
  have he0 : e 0 = 0 := by simp [he]
  have he1 : ∀ j, j ≠ 0 → e j = 1 := fun j hj => by simp [he, hj]
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℝ, w = ∑ t ∈ Finset.range K, m.P μ ^ t *ᵥ e := ⟨_, rfl⟩
  have hPw : m.P μ *ᵥ w = w + m.P μ ^ K *ᵥ e - e := by
    have h := Finset.sum_range_succ' (fun t => m.P μ ^ t *ᵥ e) K
    rw [Finset.sum_range_succ] at h
    simp only [pow_zero, Matrix.one_mulVec] at h
    have : ∀ t : ℕ, m.P μ *ᵥ (m.P μ ^ t *ᵥ e) = m.P μ ^ (t + 1) *ᵥ e := fun t => by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hw, Matrix.mulVec_sum]
    simp only [this]
    linear_combination -h
  have hPKe : ∀ i, (m.P μ ^ K *ᵥ e) i ≤ 1 / 2 := by
    intro i
    have hs := Ppow_rowsum m μ K i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at hs
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    have : ∑ j ∈ Finset.univ.erase 0, (m.P μ ^ K) i j * e j =
        ∑ j ∈ Finset.univ.erase 0, (m.P μ ^ K) i j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [he1 j (Finset.ne_of_mem_erase hj), mul_one]
    rw [this, he0, mul_zero, zero_add]
    have := hK i
    linarith
  have hw0 : w 0 = 0 := by
    rw [hw, Finset.sum_apply]
    simp [Ppow_mulVec_zero m h1, he0]
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 2 * ∑ j, |m.cvec μ j| := ⟨_, rfl⟩
  refine ⟨α • w, ?_, ?_⟩
  · show (α • w) 0 = 0
    simp [hw0]
  · intro i
    by_cases hi : i = 0
    · subst hi; rw [Tmu_zero m h1]
    · have hc : m.cvec μ i ≤ ∑ j, |m.cvec μ j| := (le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |m.cvec μ j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i))
      have hs0 : 0 ≤ ∑ j, |m.cvec μ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
      have h3 := hPKe i
      have h4 : (m.P μ *ᵥ w) i = w i + (m.P μ ^ K *ᵥ e) i - 1 := by
        rw [hPw]; simp [he1 i hi]
      show m.cvec μ i + (m.P μ *ᵥ (α • w)) i ≤ (α • w) i
      rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h4]
      nlinarith

open Classical in
/-- The bottom-set argument: supersolutions whose normalized value at the absorbing state
blows up are impossible. -/
theorem core [NeZero n] [∀ i, MetricSpace (U i)] (h1 : m.Assumption1) (h2 : m.Assumption2)
    (νs : ℕ → Selector U) (vs : ℕ → Fin n → ℝ) (κ : Selector U) (y : Fin n → ℝ)
    (hκ : ∀ i, m.Tmu κ y i ≤ y i) (hnn : ∀ k j, 0 ≤ vs k j) (hz : ∀ k, ∃ j, vs k j = 0)
    (hsup : ∀ k i, m.Tmu (νs k) (vs k) i ≤ vs k i)
    (h0 : Tendsto (fun k => vs k 0) atTop atTop) : False := by
  have hcU : IsCompact (Set.univ : Set (Selector U)) := by
    have := isCompact_univ_pi (fun i => h2.compact i)
    simpa [Set.pi_univ] using this
  have hc : IsCompact (Set.univ : Set (Selector U × (Fin n → EReal))) := by
    rw [← Set.univ_prod_univ]; exact hcU.prod isCompact_univ
  obtain ⟨⟨ν, V⟩, -, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (x := fun k => (νs k, fun j => ((vs k j : ℝ) : EReal))) (fun _ => Set.mem_univ _)
  have hν : ∀ i, Tendsto (fun k => νs (φ k) i) atTop (𝓝 (ν i)) := fun i =>
    tendsto_pi_nhds.1 ((continuous_fst.tendsto (ν, V)).comp hlim) i
  have hV : ∀ j, Tendsto (fun k => ((vs (φ k) j : ℝ) : EReal)) atTop (𝓝 (V j)) := fun j =>
    tendsto_pi_nhds.1 ((continuous_snd.tendsto (ν, V)).comp hlim) j
  have hV0 : V 0 = ⊤ := by
    have : Tendsto (fun k => ((vs (φ k) 0 : ℝ) : EReal)) atTop (𝓝 ⊤) := by
      rw [EReal.tendsto_nhds_top_iff_real]
      intro x
      exact ((h0.comp hφ.tendsto_atTop).eventually_gt_atTop x).mono fun k hk =>
        EReal.coe_lt_coe_iff.2 hk
    exact tendsto_nhds_unique (hV 0) this
  have hVnb : ∀ j, V j ≠ ⊥ := by
    intro j hj
    have : (0 : EReal) ≤ V j := ge_of_tendsto' (hV j) fun k => EReal.coe_nonneg.2 (hnn _ j)
    rw [hj] at this
    exact absurd this (by simp)
  obtain ⟨h, hh⟩ : ∃ h : Fin n → ℝ, h = fun j => if V j ≠ ⊤ then (V j).toReal else 0 :=
    ⟨_, rfl⟩
  have hfin : ∀ j, V j ≠ ⊤ → Tendsto (fun k => vs (φ k) j) atTop (𝓝 (h j)) := by
    intro j hj
    have := (EReal.tendsto_toReal hj (hVnb j)).comp (hV j)
    rw [hh]
    simp only [if_pos hj]
    simpa [Function.comp_def] using this
  have hinf : ∀ j, V j = ⊤ → ∀ M : ℝ, ∀ᶠ k in atTop, M < vs (φ k) j := by
    intro j hj M
    have := hV j
    rw [hj, EReal.tendsto_nhds_top_iff_real] at this
    exact (this M).mono fun k hk => EReal.coe_lt_coe_iff.1 hk
  obtain ⟨i0, hi0⟩ : ∃ i0, V i0 ≠ ⊤ := by
    by_contra hall
    push_neg at hall
    have : ∀ᶠ k in atTop, ∀ j, 0 < vs (φ k) j := eventually_all.2 fun j => hinf j (hall j) 0
    obtain ⟨k, hk⟩ := this.exists
    obtain ⟨j, hj⟩ := hz (φ k)
    exact (hk j).ne' hj
  have hpk : ∀ i j, Tendsto (fun k => m.p i (νs (φ k) i) j) atTop (𝓝 (m.p i (ν i) j)) :=
    fun i j => ((h2.cont i j).tendsto _).comp (hν i)
  have hcl : ∀ i, V i ≠ ⊤ → ∀ j, V j = ⊤ → m.p i (ν i) j = 0 := by
    intro i hi j hj
    by_contra hne
    have hpos : 0 < m.p i (ν i) j := lt_of_le_of_ne (m.p_nonneg _ _ _) (Ne.symm hne)
    have e1 : ∀ᶠ k in atTop, m.p i (ν i) j / 2 < m.p i (νs (φ k) i) j :=
      (hpk i j).eventually (lt_mem_nhds (by linarith))
    have e2 : ∀ᶠ k in atTop, m.c i (ν i) - 1 < m.c i (νs (φ k) i) :=
      (hν i).eventually (h2.lsc i (ν i) _ (by linarith))
    have e3 : ∀ᶠ k in atTop, vs (φ k) i < h i + 1 :=
      (hfin i hi).eventually (gt_mem_nhds (by linarith))
    have e4 := hinf j hj (2 * |h i + 2 - m.c i (ν i)| / m.p i (ν i) j)
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := (e1.and (e2.and (e3.and e4))).exists
    have hs := hsup (φ k) i
    rw [Tmu_apply] at hs
    have hsingle : m.p i (νs (φ k) i) j * vs (φ k) j ≤
        ∑ l, m.p i (νs (φ k) i) l * vs (φ k) l :=
      Finset.single_le_sum (f := fun l => m.p i (νs (φ k) i) l * vs (φ k) l)
        (fun l _ => mul_nonneg (m.p_nonneg _ _ _) (hnn _ _)) (Finset.mem_univ j)
    have a1 : m.p i (ν i) j / 2 * vs (φ k) j ≤ m.p i (νs (φ k) i) j * vs (φ k) j :=
      mul_le_mul_of_nonneg_right hk1.le (hnn _ _)
    have a2 : m.p i (ν i) j / 2 * (2 * |h i + 2 - m.c i (ν i)| / m.p i (ν i) j) ≤
        m.p i (ν i) j / 2 * vs (φ k) j :=
      mul_le_mul_of_nonneg_left hk4.le (by positivity)
    have a3 : m.p i (ν i) j / 2 * (2 * |h i + 2 - m.c i (ν i)| / m.p i (ν i) j) =
        |h i + 2 - m.c i (ν i)| := by
      field_simp
    have a4 := le_abs_self (h i + 2 - m.c i (ν i))
    linarith
  have hsupI : ∀ i, V i ≠ ⊤ → m.c i (ν i) + ∑ j, m.p i (ν i) j * h j ≤ h i := by
    intro i hi
    have hSk : Tendsto (fun k => ∑ j, m.p i (νs (φ k) i) j *
        (if V j ≠ ⊤ then vs (φ k) j else 0)) atTop (𝓝 (∑ j, m.p i (ν i) j * h j)) := by
      apply tendsto_finsetSum
      intro j _
      by_cases hj : V j ≠ ⊤
      · simp only [if_pos hj]
        exact (hpk i j).mul (hfin j hj)
      · have : h j = 0 := by rw [hh]; simp only [if_neg hj]
        simp only [if_neg hj, this, mul_zero]
        exact tendsto_const_nhds
    have hr : ∀ k, m.c i (νs (φ k) i) ≤ vs (φ k) i - ∑ j, m.p i (νs (φ k) i) j *
        (if V j ≠ ⊤ then vs (φ k) j else 0) := by
      intro k
      have hs := hsup (φ k) i
      rw [Tmu_apply] at hs
      have : ∑ j, m.p i (νs (φ k) i) j * (if V j ≠ ⊤ then vs (φ k) j else 0) ≤
          ∑ j, m.p i (νs (φ k) i) j * vs (φ k) j := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (m.p_nonneg _ _ _)
        split_ifs
        · exact le_rfl
        · exact hnn _ _
      linarith
    by_contra hcon
    push_neg at hcon
    have hδ : 0 < (m.c i (ν i) + ∑ j, m.p i (ν i) j * h j - h i) / 2 := by linarith
    have e1 : ∀ᶠ k in atTop, m.c i (ν i) - (m.c i (ν i) + ∑ j, m.p i (ν i) j * h j - h i) / 2
        < m.c i (νs (φ k) i) :=
      (hν i).eventually (h2.lsc i (ν i) _ (by linarith))
    have e2 := ((hfin i hi).sub hSk).eventually (gt_mem_nhds (show h i - ∑ j, m.p i (ν i) j * h j
      < h i - ∑ j, m.p i (ν i) j * h j +
        (m.c i (ν i) + ∑ j, m.p i (ν i) j * h j - h i) / 2 by linarith))
    obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
    have := hr k
    linarith
  obtain ⟨ν', hν'⟩ : ∃ ν' : Selector U, ν' = fun j => if V j ≠ ⊤ then ν j else κ j := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑ j, |h j - y j| := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin n → ℝ, g = fun j => if V j ≠ ⊤ then h j else y j + D := ⟨_, rfl⟩
  have hgle : ∀ j, g j ≤ y j + D := by
    intro j
    rw [hg]
    dsimp only
    split_ifs
    · have := Finset.single_le_sum (f := fun l => |h l - y l|) (fun l _ => abs_nonneg _)
        (Finset.mem_univ j)
      have := le_abs_self (h j - y j)
      rw [hD]
      linarith
    · exact le_rfl
  have hsupg : ∀ i, m.Tmu ν' g i ≤ g i := by
    intro i
    rw [Tmu_apply]
    by_cases hi : V i ≠ ⊤
    · have hνi : ν' i = ν i := by rw [hν']; simp only [if_pos hi]
      rw [hνi]
      have : ∑ j, m.p i (ν i) j * g j = ∑ j, m.p i (ν i) j * h j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : V j ≠ ⊤
        · rw [hg]; simp only [if_pos hj]
        · push_neg at hj
          rw [hcl i hi j hj, zero_mul, zero_mul]
      rw [this]
      have hgi : g i = h i := by rw [hg]; simp only [if_pos hi]
      rw [hgi]
      exact hsupI i hi
    · have hνi : ν' i = κ i := by rw [hν']; simp only [if_neg hi]
      rw [hνi]
      have hk := hκ i
      rw [Tmu_apply] at hk
      have : ∑ j, m.p i (κ i) j * g j ≤ ∑ j, m.p i (κ i) j * y j + D := by
        calc ∑ j, m.p i (κ i) j * g j ≤ ∑ j, m.p i (κ i) j * (y j + D) :=
              Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hgle j) (m.p_nonneg _ _ _)
          _ = ∑ j, m.p i (κ i) j * y j + D := by
              simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, m.p_sum_one, one_mul]
      have hgi : g i = y i + D := by rw [hg]; simp only [if_neg hi]
      rw [hgi]
      linarith
  have hprop := proper_of_super m h1 ν' g hsupg
  have hcl' : ∀ t : ℕ, (m.P ν' ^ t) i0 0 = 0 := by
    intro t
    refine closed_pow (m.P ν') {j | V j ≠ ⊤} ?_ t i0 hi0 0 (by simp [hV0])
    intro a ha b hb
    simp only [Set.mem_ofPred_eq, not_not] at ha hb
    show m.p a (ν' a) b = 0
    have : ν' a = ν a := by rw [hν']; simp only [if_pos ha]
    rw [this]
    exact hcl a ha b hb
  have := hprop i0
  simp only [hcl'] at this
  exact absurd (tendsto_nhds_unique tendsto_const_nhds this) (by norm_num)

theorem exists_fixed [NeZero n] [∀ i, MetricSpace (U i)] (h1 : m.Assumption1)
    (h2 : m.Assumption2) : ∃ xs ∈ X n, m.T xs = xs := by
  obtain ⟨μ0, hμ0⟩ := h1.exists_proper
  obtain ⟨x0, hx0X, hx0⟩ := exists_super m h1 μ0 hμ0
  have hyX : ∀ t : ℕ, (m.T)^[t] x0 0 = 0 := by
    intro t
    induction t with
    | zero => exact hx0X
    | succ t ih => rw [Function.iterate_succ_apply', T_zero m h1 h2]; exact ih
  have hstep : ∀ (t : ℕ) (j : Fin n), (m.T)^[t + 1] x0 j ≤ (m.T)^[t] x0 j := by
    intro t
    induction t with
    | zero => intro j; exact (T_le_Tmu m h1 h2 μ0 x0 j).trans (hx0 j)
    | succ t ih =>
      intro j
      rw [Function.iterate_succ_apply' m.T (t + 1) x0]
      exact (T_mono m h1 h2 ih j).trans (le_of_eq (by rw [Function.iterate_succ_apply']))
  have hanti : ∀ j, Antitone (fun t => (m.T)^[t] x0 j) := fun j =>
    antitone_nat_of_succ_le fun t => hstep t j
  have hmn : ∀ t : ℕ, ∃ j, ∀ l, (m.T)^[t] x0 j ≤ (m.T)^[t] x0 l := fun t => by
    obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ ((m.T)^[t] x0) Finset.univ_nonempty
    exact ⟨j, fun l => hj l (Finset.mem_univ l)⟩
  choose a ha using hmn
  have hsup : ∀ (k : ℕ) (i : Fin n), m.Tmu (greedy m h1 h2 ((m.T)^[k] x0))
      (fun j => (m.T)^[k] x0 j + -((m.T)^[k] x0 (a k))) i ≤
      (m.T)^[k] x0 i + -((m.T)^[k] x0 (a k)) := by
    intro k i
    rw [Tmu_add_const, ← T_eq_greedy]
    have := hstep k i
    rw [Function.iterate_succ_apply'] at this
    linarith
  have hbdd : ∃ M : ℝ, ∀ t, M ≤ (m.T)^[t] x0 (a t) := by
    by_contra hnb
    push_neg at hnb
    have hmono : Monotone (fun t => -((m.T)^[t] x0 (a t))) := by
      apply monotone_nat_of_le_succ
      intro t
      have := ha (t + 1) (a t)
      have := hstep t (a t)
      show -((m.T)^[t] x0 (a t)) ≤ -((m.T)^[t + 1] x0 (a (t + 1)))
      linarith
    have hunb : ¬ BddAbove (Set.range fun t => -((m.T)^[t] x0 (a t))) := by
      rintro ⟨B, hB⟩
      obtain ⟨t, ht⟩ := hnb (-B)
      have := hB ⟨t, rfl⟩
      simp only at this
      linarith
    have htend := tendsto_atTop_atTop_of_monotone' hmono hunb
    refine core m h1 h2 (fun t => greedy m h1 h2 ((m.T)^[t] x0))
      (fun t j => (m.T)^[t] x0 j + -((m.T)^[t] x0 (a t)))
      (greedy m h1 h2 ((m.T)^[0] x0)) (fun j => (m.T)^[0] x0 j + -((m.T)^[0] x0 (a 0)))
      (hsup 0) ?_ ?_ hsup ?_
    · intro k j
      have := ha k j
      show 0 ≤ (m.T)^[k] x0 j + -((m.T)^[k] x0 (a k))
      linarith
    · intro k
      exact ⟨a k, by simp⟩
    · refine htend.congr fun t => ?_
      show -((m.T)^[t] x0 (a t)) = (m.T)^[t] x0 0 + -((m.T)^[t] x0 (a t))
      rw [hyX t, zero_add]
  obtain ⟨M, hM⟩ := hbdd
  have hbddj : ∀ j, BddBelow (Set.range fun t => (m.T)^[t] x0 j) := fun j =>
    ⟨M, by rintro _ ⟨t, rfl⟩; exact (hM t).trans (ha t j)⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : Fin n → ℝ, xs = fun j => ⨅ t, (m.T)^[t] x0 j := ⟨_, rfl⟩
  have hconv : Tendsto (fun t => (m.T)^[t] x0) atTop (𝓝 xs) := by
    rw [hxs]
    exact tendsto_pi_nhds.2 fun j => tendsto_atTop_ciInf (hanti j) (hbddj j)
  refine ⟨xs, ?_, ?_⟩
  · show xs 0 = 0
    exact tendsto_nhds_unique (tendsto_pi_nhds.1 hconv 0)
      (tendsto_const_nhds.congr fun t => (hyX t).symm)
  · have hA : Tendsto (fun t => m.T ((m.T)^[t] x0)) atTop (𝓝 (m.T xs)) :=
      ((T_continuous m h1 h2).tendsto xs).comp hconv
    have hB : Tendsto (fun t => m.T ((m.T)^[t] x0)) atTop (𝓝 xs) := by
      have := hconv.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun t => ?_
      simp only [Function.comp_apply]
      exact Function.iterate_succ_apply' _ _ _
    exact tendsto_nhds_unique hA hB

theorem main [NeZero n] [∀ i, MetricSpace (U i)]
    (h1 : m.Assumption1) (h2 : m.Assumption2) :
    ∃ xs : Fin n → ℝ,
      (∀ i, (xs i : EReal) = m.optCost i) ∧
      xs ∈ X n ∧
      m.T xs = xs ∧
      (∀ y ∈ X n, m.T y = y → y = xs) ∧
      (∀ x ∈ X n, Tendsto (fun t : ℕ => (m.T)^[t] x) atTop (𝓝 xs)) ∧
      (∀ μ : Selector U,
        m.IsOptimal (stationary μ) ↔ m.Tmu μ xs = m.T xs) ∧
      (∃ μ : Selector U, m.IsProper μ ∧ m.IsOptimal (stationary μ)) := by
  obtain ⟨xs, hxsX, hT⟩ := exists_fixed m h1 h2
  have hxs0 : xs 0 = 0 := hxsX
  obtain ⟨μs, hμs_def⟩ : ∃ μs : Selector U, μs = greedy m h1 h2 xs := ⟨_, rfl⟩
  have hμs : m.Tmu μs xs = xs := funext fun i => by rw [hμs_def, ← T_eq_greedy, hT]
  have hμsP : m.IsProper μs := proper_of_super m h1 μs xs fun i => by rw [hμs]
  have hX0 : (0 : Fin n → ℝ) ∈ X n := rfl
  have hXd : ∀ a b : Fin n → ℝ, a ∈ X n → b ∈ X n → a - b ∈ X n := fun a b ha hb => by
    show a 0 - b 0 = 0
    rw [show a 0 = 0 from ha, show b 0 = 0 from hb, sub_zero]
  -- uniqueness
  have hU : ∀ y ∈ X n, m.T y = y → y = xs := by
    intro y hy hTy
    have hν : m.Tmu (greedy m h1 h2 y) y = y := funext fun i => by rw [← T_eq_greedy, hTy]
    have hνP := proper_of_super m h1 _ y fun i => by rw [hν]
    have g1 := super_nonneg m _ hνP (y - xs) (hXd y xs hy hxsX) (fun i => by
      rw [← Tmu_sub, Pi.sub_apply, Pi.sub_apply, hν]
      have := T_le_Tmu m h1 h2 (greedy m h1 h2 y) xs i
      rw [hT] at this
      linarith)
    have g2 := super_nonneg m _ hμsP (xs - y) (hXd xs y hxsX hy) (fun i => by
      rw [← Tmu_sub, Pi.sub_apply, Pi.sub_apply, hμs]
      have := T_le_Tmu m h1 h2 μs y i
      rw [hTy] at this
      linarith)
    funext i
    have a1 := g1 i
    have a2 := g2 i
    simp only [Pi.sub_apply] at a1 a2
    linarith
  -- value iteration
  have hVI : ∀ x ∈ X n, Tendsto (fun t : ℕ => (m.T)^[t] x) atTop (𝓝 xs) := by
    intro x hx
    have hx0 : x 0 = 0 := hx
    have hup := iterate_tendsto m μs hμsP xs hxsX hμs x hx
    have hle_up : ∀ (t : ℕ) (j : Fin n), (m.T)^[t] x j ≤ (m.Tmu μs)^[t] x j := by
      intro t
      induction t with
      | zero => intro j; exact le_rfl
      | succ t ih =>
        intro j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact (T_mono m h1 h2 ih j).trans (T_le_Tmu m h1 h2 μs _ j)
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ∑ j, |x j - xs j| := ⟨_, rfl⟩
    have hδ0 : 0 ≤ δ := hδ ▸ Finset.sum_nonneg fun j _ => abs_nonneg _
    have hδj : ∀ j, |x j - xs j| ≤ δ := fun j => hδ ▸ Finset.single_le_sum
      (f := fun l => |x l - xs l|) (fun l _ => abs_nonneg _) (Finset.mem_univ j)
    obtain ⟨xl, hxl⟩ : ∃ xl : Fin n → ℝ, xl = fun j => if j = 0 then xs j else xs j - δ :=
      ⟨_, rfl⟩
    have hxl0 : xl 0 = 0 := by rw [hxl]; simp [hxs0]
    have hxl_le_x : ∀ j, xl j ≤ x j := by
      intro j
      rw [hxl]
      dsimp only
      split_ifs with hj
      · subst hj; rw [hxs0, hx0]
      · have := hδj j
        have := neg_abs_le (x j - xs j)
        linarith
    have hxl_le_xs : ∀ j, xl j ≤ xs j := by
      intro j; rw [hxl]; dsimp only; split_ifs <;> linarith
    have hxl_super : ∀ j, xl j ≤ m.T xl j := by
      intro j
      by_cases hj : j = 0
      · subst hj; rw [T_zero m h1 h2]
      · have := T_add_le m h1 h2 (x := xl) (y := xs) δ (fun l => by
          rw [hxl]; dsimp only; split_ifs <;> linarith) j
        rw [hT] at this
        have e : xl j = xs j - δ := by rw [hxl]; simp [hj]
        linarith
    have hl_mono : ∀ (t : ℕ) (j : Fin n), (m.T)^[t] xl j ≤ (m.T)^[t + 1] xl j := by
      intro t
      induction t with
      | zero => intro j; exact hxl_super j
      | succ t ih =>
        intro j
        rw [Function.iterate_succ_apply' m.T (t + 1) xl]
        exact (le_of_eq (by rw [Function.iterate_succ_apply'])).trans (T_mono m h1 h2 ih j)
    have hl_le : ∀ (t : ℕ) (j : Fin n), (m.T)^[t] xl j ≤ xs j := by
      intro t
      induction t with
      | zero => exact hxl_le_xs
      | succ t ih =>
        intro j
        rw [Function.iterate_succ_apply']
        have := T_mono m h1 h2 ih j
        rw [hT] at this
        exact this
    have hl_x : ∀ (t : ℕ) (j : Fin n), (m.T)^[t] xl j ≤ (m.T)^[t] x j := by
      intro t
      induction t with
      | zero => exact hxl_le_x
      | succ t ih =>
        intro j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact T_mono m h1 h2 ih j
    obtain ⟨L, hL⟩ : ∃ L : Fin n → ℝ, L = fun j => ⨆ t, (m.T)^[t] xl j := ⟨_, rfl⟩
    have hlconv : Tendsto (fun t => (m.T)^[t] xl) atTop (𝓝 L) := by
      rw [hL]
      exact tendsto_pi_nhds.2 fun j => tendsto_atTop_ciSup
        (monotone_nat_of_le_succ fun t => hl_mono t j)
        ⟨xs j, by rintro _ ⟨t, rfl⟩; exact hl_le t j⟩
    have hlX : ∀ t : ℕ, (m.T)^[t] xl 0 = 0 := by
      intro t
      induction t with
      | zero => exact hxl0
      | succ t ih => rw [Function.iterate_succ_apply', T_zero m h1 h2]; exact ih
    have hLX : L ∈ X n := by
      show L 0 = 0
      exact tendsto_nhds_unique (tendsto_pi_nhds.1 hlconv 0)
        (tendsto_const_nhds.congr fun t => (hlX t).symm)
    have hTL : m.T L = L := by
      have hA : Tendsto (fun t => m.T ((m.T)^[t] xl)) atTop (𝓝 (m.T L)) :=
        ((T_continuous m h1 h2).tendsto L).comp hlconv
      have hB : Tendsto (fun t => m.T ((m.T)^[t] xl)) atTop (𝓝 L) := by
        have := hlconv.comp (tendsto_add_atTop_nat 1)
        refine this.congr fun t => ?_
        simp only [Function.comp_apply]
        exact Function.iterate_succ_apply' _ _ _
      exact tendsto_nhds_unique hA hB
    have hLxs := hU L hLX hTL
    rw [hLxs] at hlconv
    rw [tendsto_pi_nhds]
    intro j
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_pi_nhds.1 hlconv j)
      (tendsto_pi_nhds.1 hup j) (fun t => hl_x t j) (fun t => hle_up t j)
  -- costs
  have hpc : ∀ (k : ℕ) (π : Policy U) (i : Fin n), (m.T)^[k + 1] 0 i ≤ m.partialCost π k i := by
    intro k
    induction k with
    | zero => intro π i; rw [partialCost_zero]; exact T_le_Tmu m h1 h2 _ _ i
    | succ k ih =>
      intro π i
      rw [partialCost_succ, Function.iterate_succ_apply']
      exact (T_mono m h1 h2 (ih _) i).trans (T_le_Tmu m h1 h2 _ _ i)
  have hVI0 : Tendsto (fun k : ℕ => (m.T)^[k + 1] 0) atTop (𝓝 xs) :=
    (hVI 0 hX0).comp (tendsto_add_atTop_nat 1)
  have hge : ∀ (π : Policy U) (i : Fin n), (xs i : EReal) ≤ m.cost π i := by
    intro π i
    have hc : Tendsto (fun k : ℕ => (((m.T)^[k + 1] 0 i : ℝ) : EReal)) atTop
        (𝓝 (xs i : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp
        ((continuous_apply i).continuousAt.tendsto.comp hVI0)
    rw [← hc.liminf_eq]
    unfold Model.cost
    exact liminf_le_liminf (Eventually.of_forall fun k => EReal.coe_le_coe_iff.2 (hpc k π i))
  have hpcost : ∀ μ : Selector U, m.IsProper μ → m.Tmu μ xs = xs →
      ∀ i, m.cost (stationary μ) i = xs i := by
    intro μ hμ hfix i
    have h := (iterate_tendsto m μ hμ xs hxsX hfix 0 hX0).comp (tendsto_add_atTop_nat 1)
    have hc : Tendsto (fun k => ((m.partialCost (stationary μ) k i : ℝ) : EReal)) atTop
        (𝓝 (xs i : EReal)) := by
      have := (continuous_coe_real_ereal.tendsto _).comp
        ((continuous_apply i).continuousAt.tendsto.comp h)
      refine this.congr fun k => ?_
      simp only [Function.comp_apply, partialCost_stationary]
    unfold Model.cost
    exact hc.liminf_eq
  have hopt : ∀ i, (xs i : EReal) = m.optCost i := by
    intro i
    unfold Model.optCost
    exact le_antisymm (le_iInf fun π => hge π i)
      ((iInf_le _ (stationary μs)).trans (hpcost μs hμsP hμs i).le)
  have hiff : ∀ μ : Selector U, m.IsOptimal (stationary μ) ↔ m.Tmu μ xs = m.T xs := by
    intro μ
    rw [hT]
    constructor
    · intro hopt'
      have hc : ∀ i, m.cost (stationary μ) i = xs i := fun i => (hopt' i).trans (hopt i).symm
      have hμP : m.IsProper μ := by
        by_contra hp
        obtain ⟨i, hi⟩ := h1.improper_infinite μ hp
        have ht : Tendsto (fun k => ((m.partialCost (stationary μ) k i : ℝ) : EReal)) atTop
            (𝓝 ⊤) := by
          rw [EReal.tendsto_nhds_top_iff_real]
          intro x
          refine (hi.eventually_gt_atTop x).mono fun k hk => ?_
          rw [partialCost_stationary, ← sum_eq_iterate]
          exact EReal.coe_lt_coe_iff.2 hk
        have := hc i
        unfold Model.cost at this
        rw [ht.liminf_eq] at this
        exact EReal.coe_ne_top _ this.symm
      have hmono : ∀ (k : ℕ) (j : Fin n), xs j ≤ (m.Tmu μ)^[k] xs j := by
        intro k
        induction k with
        | zero => intro j; exact le_rfl
        | succ k ih =>
          intro j
          rw [Function.iterate_succ_apply']
          have := Tmu_mono m μ ih j
          have h' := T_le_Tmu m h1 h2 μ xs j
          rw [hT] at h'
          linarith
      funext i
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        have hdiff : Tendsto (fun k : ℕ => (m.Tmu μ)^[k + 1] 0 i - (m.Tmu μ)^[k + 1] xs i)
            atTop (𝓝 0) := by
          have h3 := pow_tendsto_zero m μ hμP (0 - xs) (hXd 0 xs hX0 hxsX)
          have h4 := ((continuous_apply i).continuousAt.tendsto.comp h3).comp
            (tendsto_add_atTop_nat 1)
          refine h4.congr fun k => ?_
          simp only [Function.comp_apply]
          rw [← iterate_sub]
          rfl
        have ev : ∀ᶠ k : ℕ in atTop, -((m.Tmu μ xs i - xs i) / 2) <
            (m.Tmu μ)^[k + 1] 0 i - (m.Tmu μ)^[k + 1] xs i :=
          hdiff.eventually (lt_mem_nhds (by linarith))
        have hlow : ((xs i + (m.Tmu μ xs i - xs i) / 2 : ℝ) : EReal) ≤
            m.cost (stationary μ) i := by
          unfold Model.cost
          refine le_liminf_of_le (h := ev.mono fun k hk => ?_)
          rw [partialCost_stationary]
          have hb : m.Tmu μ xs i ≤ (m.Tmu μ)^[k + 1] xs i := by
            rw [Function.iterate_succ_apply']
            exact Tmu_mono m μ (hmono k) i
          exact EReal.coe_le_coe_iff.2 (by linarith)
        rw [hc i] at hlow
        have := EReal.coe_le_coe_iff.1 hlow
        linarith
      · have h' := T_le_Tmu m h1 h2 μ xs i
        rw [hT] at h'
        exact h'
    · intro hfix
      have hμP := proper_of_super m h1 μ xs fun i => by rw [hfix]
      intro i
      rw [hpcost μ hμP hfix i]
      exact hopt i
  refine ⟨xs, hopt, hxsX, hT, hU, hVI, hiff, μs, hμsP, (hiff μs).2 ?_⟩
  rw [hμs, hT]

end SSPAnalysis.Bellman.P2Aux

open Filter Topology SSPAnalysis.Bellman in
theorem solution {n : ℕ} [NeZero n] {U : Fin n → Type*}
    [∀ i, MetricSpace (U i)] (m : Model n U)
    (h1 : m.Assumption1) (h2 : m.Assumption2) :
    ∃ xs : Fin n → ℝ,
      (∀ i, (xs i : EReal) = m.optCost i) ∧
      xs ∈ X n ∧
      m.T xs = xs ∧
      (∀ y ∈ X n, m.T y = y → y = xs) ∧
      (∀ x ∈ X n, Tendsto (fun t : ℕ => (m.T)^[t] x) atTop (𝓝 xs)) ∧
      (∀ μ : Selector U,
        m.IsOptimal (stationary μ) ↔ m.Tmu μ xs = m.T xs) ∧
      (∃ μ : Selector U, m.IsProper μ ∧ m.IsOptimal (stationary μ)) := by
  exact SSPAnalysis.Bellman.P2Aux.main m h1 h2
