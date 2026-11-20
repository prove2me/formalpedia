-- Prove2me | solution 1 for SignRankMargin.OREquality.Supplement.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:11:25.15885+00:00
-- url     : https://prove2.me/submissions/5703c653-7aa8-499e-9d1c-1c09e35dec1c

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_SignRankMargin_OREquality_Composition
import Definitions.Def_SignRankMargin_OREquality_Geometry
import Theorems.Thm_SignRankMargin_OREquality_lemma_9
import Theorems.Thm_SignRankMargin_OREquality_lemma_13

section
namespace SignRankMargin.OREquality.Dev.Tensor

/-- Quadratic-form operator bound for a square real matrix. -/
def Bd {α : Type*} [Fintype α] (M : Matrix α α ℝ) (c : ℝ) : Prop :=
  ∀ w : α → ℝ, ∑ x, (∑ y, M x y * w y) ^ 2 ≤ c ^ 2 * ∑ y, w y ^ 2

theorem bd_of_opNorm {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℝ) :
    Bd M ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ := by
  intro w
  have h := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanLin M).toContinuousLinearMap
    (WithLp.toLp 2 w)
  have h2 : ‖(Matrix.toEuclideanLin M).toContinuousLinearMap (WithLp.toLp 2 w)‖ ^ 2 ≤
      (‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ * ‖WithLp.toLp 2 w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  have e1 : ‖(Matrix.toEuclideanLin M).toContinuousLinearMap (WithLp.toLp 2 w)‖ ^ 2 =
      ∑ x, (∑ y, M x y * w y) ^ 2 := by
    rw [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_toLp,
      EuclideanSpace.norm_sq_eq]
    simp [Matrix.mulVec, dotProduct]
  have e2 : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ α)‖ ^ 2 = ∑ y, w y ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  rw [e1, mul_pow, e2] at h2
  exact h2

theorem opNorm_le_of_bd {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h : Bd M c) : ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc (fun v => ?_)
  have e1 : ‖(Matrix.toEuclideanLin M).toContinuousLinearMap v‖ ^ 2 =
      ∑ x, (∑ y, M x y * v y) ^ 2 := by
    rw [LinearMap.coe_toContinuousLinearMap']
    have : v = WithLp.toLp 2 (WithLp.ofLp v) := rfl
    rw [this, Matrix.toEuclideanLin_toLp, EuclideanSpace.norm_sq_eq]
    simp [Matrix.mulVec, dotProduct]
  have e2 : ‖v‖ ^ 2 = ∑ y, v y ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have := h (WithLp.ofLp v)
  rw [← e1, ← e2, ← mul_pow] at this
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).1 this

theorem bd_kron {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (a b : ℝ) (hA : Bd A a) (hB : Bd B b) :
    Bd (α := ι × κ) (fun p q => A p.1 q.1 * B p.2 q.2) (a * b) := by
  intro w
  -- intermediate z i j' = ∑ i', A i i' * w (i', j')
  set z : ι → κ → ℝ := fun i j' => ∑ i', A i i' * w (i', j') with hz
  have step1 : ∀ i j, ∑ q : ι × κ, A i q.1 * B j q.2 * w q = ∑ j', B j j' * z i j' := by
    intro i j
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [hz]; simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    ring
  have lhs : ∑ p : ι × κ, (∑ q : ι × κ, A p.1 q.1 * B p.2 q.2 * w q) ^ 2
      = ∑ i, ∑ j, (∑ j', B j j' * z i j') ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [step1]
  rw [lhs]
  calc ∑ i, ∑ j, (∑ j', B j j' * z i j') ^ 2
      ≤ ∑ i, b ^ 2 * ∑ j', z i j' ^ 2 := Finset.sum_le_sum (fun i _ => hB (z i))
    _ = b ^ 2 * ∑ j', ∑ i, z i j' ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ b ^ 2 * ∑ j', a ^ 2 * ∑ i', w (i', j') ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j' _ => ?_)) (sq_nonneg _)
        exact hA (fun i' => w (i', j'))
    _ = (a * b) ^ 2 * ∑ q : ι × κ, w q ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_comm, ← Finset.mul_sum]
        ring

theorem bd_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (M : Matrix α α ℝ)
    (N : Matrix β β ℝ) (hMN : ∀ x y, M x y = N (e x) (e y)) (c : ℝ) (h : Bd N c) : Bd M c := by
  intro w
  have := h (fun b => w (e.symm b))
  have e1 : ∑ x, (∑ y, M x y * w y) ^ 2 = ∑ b, (∑ b', N b b' * w (e.symm b')) ^ 2 := by
    rw [← e.sum_comp (fun b => (∑ b', N b b' * w (e.symm b')) ^ 2)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    rw [← e.sum_comp (fun b' => N (e x) b' * w (e.symm b'))]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp [hMN]
  have e2 : ∑ y, w y ^ 2 = ∑ b, w (e.symm b) ^ 2 := by
    rw [← e.sum_comp]; simp
  rw [e1, e2]; exact this

theorem bd_tensorPow {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (c : ℝ)
    (hA : Bd A c) (k : ℕ) (A' : Matrix (Fin k → ι) (Fin k → ι) ℝ)
    (hA' : ∀ x y, A' x y = ∏ i, A (x i) (y i)) : Bd A' (c ^ k) := by
  induction k with
  | zero =>
    intro w
    have hu : ∀ x : Fin 0 → ι, x = default := fun x => Subsingleton.elim _ _
    simp only [Fintype.sum_unique, hA', Finset.univ_eq_empty, Finset.prod_empty, pow_zero,
      one_mul]
    simp
  | succ k ih =>
    have hk := ih (fun x y => ∏ i, A (x i) (y i)) (fun _ _ => rfl)
    have := bd_kron A _ c (c ^ k) hA hk
    rw [pow_succ']
    refine bd_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).symm A' _ ?_ _ this
    intro x y
    rw [hA', Fin.prod_univ_succ]
    rfl

theorem opNorm_tensorPow {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (A : Matrix ι ι ℝ)
    (A' : Matrix (Fin k → ι) (Fin k → ι) ℝ) (hA' : ∀ x y, A' x y = ∏ i, A (x i) (y i)) :
    ‖(Matrix.toEuclideanLin A').toContinuousLinearMap‖ ≤
      ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ^ k :=
  opNorm_le_of_bd A' _ (pow_nonneg (norm_nonneg _) _)
    (bd_tensorPow A _ (bd_of_opNorm A) k A' hA')

end SignRankMargin.OREquality.Dev.Tensor
end

section
namespace SignRankMargin.OREquality.Dev.T14

/-- The operator norm of a real square matrix on Euclidean space. -/
noncomputable def opn {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Matrix ι ι ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin Z).toContinuousLinearMap‖

lemma sq_bound {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ∑ a, (Z.mulVec x a) ^ 2 ≤ opn Z ^ 2 * ∑ i, (x i) ^ 2 := by
  have h := (Matrix.toEuclideanLin Z).toContinuousLinearMap.le_opNorm (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_toLp,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, mul_pow] at h2
  simpa [opn, Matrix.toLin'_apply] using h2

lemma opn_le_of_sq {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x : Fin n → ℝ, ∑ a, (Q.mulVec x a) ^ 2 ≤ c ^ 2 * ∑ i, (x i) ^ 2) : opn Q ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc (fun v => ?_)
  have hv : v = WithLp.toLp 2 v.ofLp := rfl
  have := h v.ofLp
  have h3 : ‖(Matrix.toEuclideanLin Q).toContinuousLinearMap v‖ ^ 2 ≤ (c * ‖v‖) ^ 2 := by
    rw [hv]
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_toLp,
      EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, mul_pow]
    simpa [Matrix.toLin'_apply] using this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h3


section Spectral

variable {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)

lemma mulVec_center (hrow : ∀ a, ∑ b, Z a b = 0) (x : Fin n → ℝ) (m : ℝ) :
    Z.mulVec (fun i => x i - m) = Z.mulVec x := by
  ext a
  simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hrow, zero_mul, sub_zero]

lemma sum_mulVec (hcol : ∀ b, ∑ a, Z a b = 0) (x : Fin n → ℝ) :
    ∑ a, Z.mulVec x a = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [← Finset.sum_mul, hcol, zero_mul]

lemma sumsq_center (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, (x i - (∑ j, x j) / n) ^ 2 = ∑ i, (x i) ^ 2 - (∑ j, x j) ^ 2 / n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma sq_bound_center (hn : 0 < n) (hrow : ∀ a, ∑ b, Z a b = 0) (x : Fin n → ℝ) :
    ∑ a, (Z.mulVec x a) ^ 2 ≤ opn Z ^ 2 * (∑ i, (x i) ^ 2 - (∑ j, x j) ^ 2 / n) := by
  rw [← sumsq_center hn, ← mulVec_center Z hrow x ((∑ j, x j) / n)]
  exact sq_bound Z _

lemma opn_Q_le (hn : 0 < n) (hrow : ∀ a, ∑ b, Z a b = 0) (hcol : ∀ b, ∑ a, Z a b = 0)
    (hl : 0 < opn Z) :
    opn (fun a b : Fin n => 1 / (n : ℝ) - Z a b / opn Z) ≤ 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  refine opn_le_of_sq _ 1 zero_le_one (fun x => ?_)
  have hq : ∀ a, (Matrix.mulVec (fun a b : Fin n => 1 / (n : ℝ) - Z a b / opn Z) x) a =
      (∑ j, x j) / n - Z.mulVec x a / opn Z := by
    intro a
    simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div,
      ← Finset.sum_div, ← Finset.mul_sum]
    field_simp
  simp only [hq, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, sum_mulVec Z hcol, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, div_pow]
  have h := sq_bound_center Z hn hrow x
  have h2 : (∑ a, (Z.mulVec x a) ^ 2) / opn Z ^ 2 ≤ ∑ i, (x i) ^ 2 - (∑ j, x j) ^ 2 / n := by
    rw [div_le_iff₀ (by positivity)]; linarith
  field_simp at h2 ⊢
  nlinarith [h2]


lemma frob_le (hn : 0 < n) (hrow : ∀ a, ∑ b, Z a b = 0) :
    ∑ a, ∑ b, (Z a b) ^ 2 ≤ ((n : ℝ) - 1) * opn Z ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h : ∀ j : Fin n, ∑ a, (Z a j) ^ 2 ≤ opn Z ^ 2 * (1 - 1 / (n : ℝ)) := by
    intro j
    have := sq_bound_center Z hn hrow (Pi.single j 1)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _j : Fin n, opn Z ^ 2 * (1 - 1 / (n : ℝ)) := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

lemma one_le_opn (hn : 2 ≤ n) (hrow : ∀ a, ∑ b, Z a b = 0)
    (hF : ((n : ℝ) - 1) ≤ ∑ a, ∑ b, (Z a b) ^ 2) : 1 ≤ opn Z := by
  have h1 := frob_le Z (by omega) hrow
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have h2 : 1 ≤ opn Z ^ 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h0 : 0 ≤ opn Z := norm_nonneg _
  nlinarith

end Spectral

section Regular

variable {n : ℕ} (D : ℕ) (B : Matrix (Fin n) (Fin n) Bool)

/-- The 0/1 real matrix of `B`. -/
noncomputable def bR (a b : Fin n) : ℝ := if B a b then 1 else 0

/-- The centered matrix. -/
noncomputable def ZB : Matrix (Fin n) (Fin n) ℝ := fun a b => bR B a b - (D : ℝ) / n

variable {D B}

lemma ZB_row (hn : 0 < n) (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D) (a : Fin n) :
    ∑ b, ZB D B a b = 0 := by
  have h : ∑ y, bR B a y = D := by
    have := congrArg (fun m : ℕ => (m : ℝ)) (hrows a)
    simpa [bR] using this
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [ZB, Finset.sum_sub_distrib, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

lemma ZB_col (hn : 0 < n) (hcols : ∀ y, (∑ x, if B x y then (1 : ℕ) else 0) = D) (b : Fin n) :
    ∑ a, ZB D B a b = 0 := by
  have h : ∑ y, bR B y b = D := by
    have := congrArg (fun m : ℕ => (m : ℝ)) (hcols b)
    simpa [bR] using this
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [ZB, Finset.sum_sub_distrib, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

lemma ZB_sq (hn : 0 < n) (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D) :
    ∑ a, ∑ b, (ZB D B a b) ^ 2 = D * ((n : ℝ) - D) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hrow : ∀ a, ∑ y, bR B a y = D := by
    intro a
    have := congrArg (fun m : ℕ => (m : ℝ)) (hrows a)
    simpa [bR] using this
  have hb : ∀ a b, bR B a b ^ 2 = bR B a b := by
    intro a b; unfold bR; split_ifs <;> norm_num
  have : ∀ a, ∑ b, (ZB D B a b) ^ 2 = D - (D : ℝ) ^ 2 / n := by
    intro a
    simp only [ZB, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, hb, hrow,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma ZB_abs (hn : 0 < n) (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D) :
    ∑ a, ∑ b, |ZB D B a b| ≤ 2 * n * D := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hrow : ∀ a, ∑ y, bR B a y = D := by
    intro a
    have := congrArg (fun m : ℕ => (m : ℝ)) (hrows a)
    simpa [bR] using this
  have h1 : ∀ a b, |ZB D B a b| ≤ bR B a b + (D : ℝ) / n := by
    intro a b
    have h0 : 0 ≤ bR B a b := by unfold bR; split_ifs <;> norm_num
    have h2 : 0 ≤ (D : ℝ) / n := by positivity
    rw [abs_le]; unfold ZB; constructor <;> linarith
  calc _ ≤ ∑ a, ∑ b, (bR B a b + (D : ℝ) / n) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => h1 a b))
    _ = _ := by
      simp only [Finset.sum_add_distrib, hrow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring

lemma one_le_opn_ZB (hD : 1 ≤ D) (hDn : D < n)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D)
    (hcols : ∀ y, (∑ x, if B x y then (1 : ℕ) else 0) = D) : 1 ≤ opn (ZB D B) := by
  have hn : 0 < n := by omega
  refine one_le_opn _ (by omega) (ZB_row hn hrows) ?_
  rw [ZB_sq hn hrows]
  have h1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h2 : (D : ℝ) + 1 ≤ n := by exact_mod_cast hDn
  nlinarith

end Regular


section Arith

lemma bern (D : ℕ) : ∀ k : ℕ, 1 + 2 * D * k ≤ (1 + 2 * D) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith [Nat.zero_le (D * k), Nat.zero_le D]

lemma one_add_two_le (D : ℕ) : 1 + 2 * D ≤ 2 ^ (2 * D) := by
  have : ∀ D : ℕ, 1 + 2 * D ≤ 4 ^ D := by
    intro D
    induction D with
    | zero => simp
    | succ D ih => rw [pow_succ]; omega
  have h := this D
  have h4 : (4 : ℕ) ^ D = 2 ^ (2 * D) := by
    rw [pow_mul]; norm_num
  omega

lemma fourteen_le (k : ℕ) : 14 * k ≤ 6 * 3 ^ k := by
  have : ∀ k : ℕ, 1 ≤ k → 14 * k ≤ 6 * 3 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
      rw [pow_succ]; omega
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · have := this k h; omega

lemma arith (D k : ℕ) (hD : 1 ≤ D) (hk : 1 ≤ k) :
    k * D * (1 + 2 * D) ^ (6 * k * (D + 1) ^ k) ≤ 2 ^ ((6 * D) ^ (k + 1)) := by
  have h1 : k * D ≤ (1 + 2 * D) ^ k := by
    have := bern D k; nlinarith
  have hk' : k ≤ k * (D + 1) ^ k :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have h2 : k * D * (1 + 2 * D) ^ (6 * k * (D + 1) ^ k) ≤
      (1 + 2 * D) ^ (7 * k * (D + 1) ^ k) := by
    calc _ ≤ (1 + 2 * D) ^ k * (1 + 2 * D) ^ (6 * k * (D + 1) ^ k) :=
          Nat.mul_le_mul_right _ h1
      _ = (1 + 2 * D) ^ (k + 6 * k * (D + 1) ^ k) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have h3 : (1 + 2 * D) ^ (7 * k * (D + 1) ^ k) ≤ 2 ^ (2 * D * (7 * k * (D + 1) ^ k)) := by
    exact (Nat.pow_le_pow_left (one_add_two_le D) _).trans (pow_mul 2 (2 * D) _).symm.le
  have h4 : (D + 1) ^ k ≤ 2 ^ k * D ^ k := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have h5 : 2 * D * (7 * k * (D + 1) ^ k) ≤ (6 * D) ^ (k + 1) := by
    have h6 := fourteen_le k
    have h7 : 14 * k * 2 ^ k ≤ 6 * 6 ^ k := by
      calc 14 * k * 2 ^ k ≤ (6 * 3 ^ k) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
        _ = 6 * 6 ^ k := by
          rw [show (6 : ℕ) ^ k = 3 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]; ring
    calc 2 * D * (7 * k * (D + 1) ^ k) ≤ 2 * D * (7 * k * (2 ^ k * D ^ k)) := by gcongr
      _ = (14 * k * 2 ^ k) * D ^ (k + 1) := by ring
      _ ≤ (6 * 6 ^ k) * D ^ (k + 1) := Nat.mul_le_mul_right _ h7
      _ = (6 * D) ^ (k + 1) := by rw [mul_pow, pow_succ 6 k]; ring
  exact h2.trans (h3.trans (Nat.pow_le_pow_right (by norm_num) h5))

end Arith


section Count

lemma sum_pi_prod {n : ℕ} (k : ℕ) (g : Fin k → Fin n → ℝ) :
    ∑ y : Fin k → Fin n, ∏ i, g i (y i) = ∏ i, ∑ b, g i b := by
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ]

lemma sum_sum_prod {n : ℕ} (k : ℕ) (f : Fin n → Fin n → ℝ) :
    ∑ x : Fin k → Fin n, ∑ y : Fin k → Fin n, ∏ i, f (x i) (y i) =
      (∑ a, ∑ b, f a b) ^ k := by
  have h1 : ∀ x : Fin k → Fin n, ∑ y : Fin k → Fin n, ∏ i, f (x i) (y i) =
      ∏ i, ∑ b, f (x i) b := fun x => sum_pi_prod k (fun i b => f (x i) b)
  simp only [h1]
  rw [sum_pi_prod k (fun _ a => ∑ b, f a b)]
  simp

variable {n : ℕ} {D k : ℕ} {B : Matrix (Fin n) (Fin n) Bool}

lemma indicator_or (k : ℕ) (x y : Fin k → Fin n) :
    (if orComposition k B x y = true then (1 : ℝ) else 0) =
      1 - ∏ i, (1 - bR B (x i) (y i)) := by
  classical
  have hor : orComposition k B x y = decide (∃ i : Fin k, B (x i) (y i) = true) := by
    unfold orComposition; rfl
  rw [hor]
  by_cases h : ∃ i : Fin k, B (x i) (y i) = true
  · obtain ⟨i, hi⟩ := h
    rw [decide_eq_true ⟨i, hi⟩, if_pos rfl]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [bR, hi])]
    norm_num
  · rw [decide_eq_false h]
    simp only [Bool.false_eq_true, if_false]
    push Not at h
    rw [Finset.prod_eq_one (fun i _ => by simp [bR, h i])]
    norm_num

lemma oneCount_eq (hn : 0 < n) (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D) (k : ℕ) :
    (oneCount (orComposition k B) : ℝ) = (n : ℝ) ^ (2 * k) - ((n : ℝ) ^ 2 - n * D) ^ k := by
  have hrow : ∀ a, ∑ y, bR B a y = D := by
    intro a
    have := congrArg (fun m : ℕ => (m : ℝ)) (hrows a)
    simpa [bR] using this
  have h1 : (oneCount (orComposition k B) : ℝ) =
      ∑ x : Fin k → Fin n, ∑ y : Fin k → Fin n, (1 - ∏ i, (1 - bR B (x i) (y i))) := by
    simp only [oneCount, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [← indicator_or]
    split_ifs <;> simp
  rw [h1]
  simp only [Finset.sum_sub_distrib]
  rw [sum_sum_prod k (fun a b => 1 - bR B a b)]
  simp only [Finset.sum_sub_distrib, hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Fintype.card_pi, Finset.prod_const]
  push_cast
  rw [pow_mul]
  ring_nf


lemma sparse (hD : 1 ≤ D) (hDn : D < n) (hk : 1 ≤ k) 
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D)
    (hnbig : 2 ^ ((6 * D) ^ (k + 1)) ≤ n) (β : ℝ) (hβ1 : 1 ≤ β) (hβ : β ≤ 1 + 2 * D)
    (d : ℕ) (hd : d ≤ (D + 1) ^ k) :
    (oneCount (orComposition k B) : ℝ) ≤
      (((β ^ k) ^ (6 * d))⁻¹) * ((n : ℝ) ^ k) * ((n : ℝ) ^ k) := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [oneCount_eq hn hrows]
  set T : ℝ := (β ^ k) ^ (6 * d) with hT
  have hT1 : 1 ≤ T := one_le_pow₀ (one_le_pow₀ hβ1)
  have hTpos : 0 < T := by linarith
  -- kD T ≤ n
  have hkDT : (k : ℝ) * D * T ≤ n := by
    have h1 : T ≤ (1 + 2 * (D : ℝ)) ^ (6 * k * (D + 1) ^ k) := by
      rw [hT, ← pow_mul]
      calc β ^ (k * (6 * d)) ≤ (1 + 2 * (D : ℝ)) ^ (k * (6 * d)) :=
            pow_le_pow_left₀ (by linarith) hβ _
        _ ≤ _ := by
          apply pow_le_pow_right₀ (by have : (0 : ℝ) ≤ D := by positivity
                                      linarith)
          nlinarith [Nat.zero_le k]
    have h2 := arith D k hD hk
    have h3 : ((k * D * (1 + 2 * D) ^ (6 * k * (D + 1) ^ k) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast h2.trans hnbig
    push_cast at h3
    calc (k : ℝ) * D * T ≤ k * D * (1 + 2 * (D : ℝ)) ^ (6 * k * (D + 1) ^ k) := by gcongr
      _ ≤ n := h3
  -- Bernoulli
  have hc : (D : ℝ) / n ≤ 1 := by
    rw [div_le_one hnR]; exact_mod_cast hDn.le
  have hbern : 1 + (k : ℝ) * (-((D : ℝ) / n)) ≤ (1 + -((D : ℝ) / n)) ^ k :=
    one_add_mul_le_pow (by linarith [show (0 : ℝ) ≤ (D : ℝ) / n by positivity]) k
  have hpow : ((n : ℝ) ^ 2 - n * D) ^ k = (n : ℝ) ^ (2 * k) * (1 + -((D : ℝ) / n)) ^ k := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
    ring
  rw [hpow]
  have hnk : (0 : ℝ) < (n : ℝ) ^ (2 * k) := by positivity
  have h4 : (k : ℝ) * D / n ≤ T⁻¹ := by
    rw [div_le_iff₀ hnR, inv_mul_eq_div, le_div_iff₀ hTpos]
    exact hkDT
  calc (n : ℝ) ^ (2 * k) - (n : ℝ) ^ (2 * k) * (1 + -((D : ℝ) / n)) ^ k
      ≤ (n : ℝ) ^ (2 * k) * ((k : ℝ) * D / n) := by
        have : (n : ℝ) ^ (2 * k) * (1 + (k : ℝ) * (-((D : ℝ) / n))) ≤
          (n : ℝ) ^ (2 * k) * (1 + -((D : ℝ) / n)) ^ k := by gcongr
        have e : (k : ℝ) * D / n = k * ((D : ℝ) / n) := by ring
        rw [e]; nlinarith
    _ ≤ (n : ℝ) ^ (2 * k) * T⁻¹ := by gcongr
    _ = T⁻¹ * (n : ℝ) ^ k * (n : ℝ) ^ k := by rw [two_mul, pow_add]; ring


lemma opn_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) (M : Matrix ι ι ℝ) : opn (c • M) = |c| * opn M := by
  simp [opn, map_smul, norm_smul]

lemma orComposition_false {k : ℕ} {x y : Fin k → Fin n} (h : orComposition k B x y = false) :
    ∀ i, B (x i) (y i) = false := by
  classical
  have hor : orComposition k B x y = decide (∃ i : Fin k, B (x i) (y i) = true) := by
    unfold orComposition; rfl
  rw [hor] at h
  have := of_decide_eq_false h
  push Not at this
  simpa using this

lemma witness (hD : 1 ≤ D) (hDn : D < n) (hk : 1 ≤ k)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D)
    (hcols : ∀ y, (∑ x, if B x y then (1 : ℕ) else 0) = D)
    (lam : ℝ) (hlam : lam = opn (ZB D B)) (hlam1 : 1 ≤ lam) (d : ℕ) (hd0 : 0 < d)
    (hdα : (d : ℝ) ≤ (1 + (D : ℝ) / lam) ^ k) :
    ∃ A : Matrix (Fin k → Fin n) (Fin k → Fin n) ℝ,
      (∀ x y, orComposition k B x y = false → A x y ≤ -1) ∧
      uniformAverage (fun x y => |A x y|) ≤ (1 + 2 * (D : ℝ) / lam) ^ k / d ∧
      ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤
        Real.sqrt ((Fintype.card (Fin k → Fin n) : ℝ) * (Fintype.card (Fin k → Fin n) : ℝ)) / d := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlam0 : 0 < lam := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  set Q : Matrix (Fin n) (Fin n) ℝ := fun a b => 1 / (n : ℝ) - ZB D B a b / lam with hQdef
  have hQ : opn Q ≤ 1 := by
    rw [hQdef, hlam]
    exact opn_Q_le (ZB D B) hn (ZB_row hn hrows) (ZB_col hn hcols) (by rw [← hlam]; exact hlam0)
  set Q' : Matrix (Fin k → Fin n) (Fin k → Fin n) ℝ := fun x y => ∏ i, Q (x i) (y i) with hQ'
  have hQ'1 : opn Q' ≤ 1 := by
    have := Dev.Tensor.opNorm_tensorPow k Q Q' (fun _ _ => rfl)
    exact this.trans (pow_le_one₀ (norm_nonneg _) hQ)
  set c : ℝ := (n : ℝ) ^ k / d with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨(-c) • Q', ?_, ?_, ?_⟩
  · intro x y hxy
    have hz := orComposition_false hxy
    have hQe : ∀ i, Q (x i) (y i) = (1 + (D : ℝ) / lam) / n := by
      intro i
      simp only [hQdef, ZB, bR, hz i]
      field_simp
      simp
    show -c * ∏ i, Q (x i) (y i) ≤ -1
    simp only [hQe, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hc]
    have : (-((n : ℝ) ^ k / d) * ((1 + (D : ℝ) / lam) / n) ^ k) = -((1 + (D : ℝ) / lam) ^ k / d) := by
      rw [div_pow]; field_simp
    rw [this, neg_le_neg_iff, le_div_iff₀ hdR]
    linarith
  · have hcard : (Fintype.card (Fin k → Fin n) : ℝ) = (n : ℝ) ^ k := by simp
    have habs : ∀ x y : Fin k → Fin n, |((-c) • Q') x y| = c * ∏ i, |Q (x i) (y i)| := by
      intro x y
      show |-c * ∏ i, Q (x i) (y i)| = _
      rw [abs_mul, abs_neg, abs_of_nonneg hc0, Finset.abs_prod]
    have hS : ∑ a, ∑ b, |Q a b| ≤ (n : ℝ) * (1 + 2 * (D : ℝ) / lam) := by
      have h1 : ∀ a b, |Q a b| ≤ 1 / (n : ℝ) + |ZB D B a b| / lam := by
        intro a b
        calc |Q a b| ≤ |1 / (n : ℝ)| + |ZB D B a b / lam| := abs_sub _ _
          _ = _ := by rw [abs_of_pos (by positivity), abs_div, abs_of_pos hlam0]
      calc ∑ a, ∑ b, |Q a b| ≤ ∑ a : Fin n, ∑ b : Fin n, (1 / (n : ℝ) + |ZB D B a b| / lam) :=
            Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => h1 a b))
        _ = n + (∑ a, ∑ b, |ZB D B a b|) / lam := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div]
            field_simp
        _ ≤ n + (2 * n * D) / lam := by
            gcongr
            exact ZB_abs hn hrows
        _ = _ := by field_simp
    have hS0 : 0 ≤ ∑ a, ∑ b, |Q a b| :=
      Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg _))
    unfold uniformAverage
    simp only [habs, ← Finset.mul_sum, sum_sum_prod k (fun a b => |Q a b|), hcard]
    have h2 : (∑ a, ∑ b, |Q a b|) ^ k ≤ ((n : ℝ) * (1 + 2 * (D : ℝ) / lam)) ^ k :=
      pow_le_pow_left₀ hS0 hS k
    rw [mul_pow] at h2
    rw [div_le_div_iff₀ (by positivity) hdR]
    have : c * (∑ a, ∑ b, |Q a b|) ^ k * d ≤
        c * ((n : ℝ) ^ k * (1 + 2 * (D : ℝ) / lam) ^ k) * d := by gcongr
    refine this.trans (le_of_eq ?_)
    simp only [hc]
    field_simp
  · have hcard : (Fintype.card (Fin k → Fin n) : ℝ) = (n : ℝ) ^ k := by simp
    rw [hcard, Real.sqrt_mul_self (by positivity)]
    show opn ((-c) • Q') ≤ _
    rw [opn_smul, abs_neg, abs_of_nonneg hc0]
    calc c * opn Q' ≤ c * 1 := by gcongr
      _ = _ := by rw [mul_one]


lemma signRank_pos {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (F : Matrix X Y Bool) : 1 ≤ signRank F := by
  classical
  have hex : ∃ r' : ℕ, ∃ H : Matrix X Y ℝ, StrictRealizes F H ∧ H.rank = r' :=
    ⟨(canonicalRealization F).rank, canonicalRealization F, by
      intro x y
      cases hF : F x y <;> norm_num [canonicalRealization, hF], rfl⟩
  have hsr : signRank F = Nat.find hex := rfl
  obtain ⟨H, hH, hrk⟩ := Nat.find_spec hex
  rw [← hsr] at hrk
  by_contra h0
  have h00 : signRank F = 0 := by omega
  rw [h00] at hrk
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hbot : LinearMap.range H.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 hrk
  have hmem : H.mulVecLin (Pi.single y 1) ∈ LinearMap.range H.mulVecLin := ⟨_, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have h1 := congrFun hmem x
  simp [Matrix.mulVec, dotProduct, Pi.single_apply] at h1
  have := hH x y
  split_ifs at this <;> linarith

lemma upper_bound (D k : ℕ) (hD : 1 ≤ D) (hk : 1 ≤ k) : 2 * (D + 1) ^ k - 1 ≤ (3 * D) ^ k := by
  rcases Nat.lt_or_ge D 2 with h | h
  · have hD1 : D = 1 := by omega
    subst hD1
    have : ∀ k : ℕ, 2 * 2 ^ k ≤ 3 ^ k + 1 := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
        rw [pow_succ, pow_succ]; omega
    have := this k
    have e1 : (1 + 1) ^ k = 2 ^ k := by norm_num
    have e2 : (3 * 1) ^ k = 3 ^ k := by norm_num
    rw [e1, e2]
    exact Nat.sub_le_of_le_add (by linarith)
  · have h1 : 2 * (D + 1) ≤ 3 * D := by omega
    have h2 : (2 * (D + 1)) ^ k ≤ (3 * D) ^ k := Nat.pow_le_pow_left h1 k
    have h3 : 2 * (D + 1) ^ k ≤ (2 * (D + 1)) ^ k := by
      rw [mul_pow]
      exact Nat.mul_le_mul_right _ (by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk)
    omega


lemma one_add_pow_ge (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    1 + x ^ k ≤ (1 + x) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    have : 0 ≤ x ^ k := pow_nonneg hx k
    nlinarith

theorem lower (hD : 1 ≤ D) (hDn : D < n) (hk : 1 ≤ k)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D)
    (hcols : ∀ y, (∑ x, if B x y then (1 : ℕ) else 0) = D)
    (hnbig : 2 ^ ((6 * D) ^ (k + 1)) ≤ n) :
    ((D : ℝ) / opn (ZB D B)) ^ k ≤ (signRank (orComposition k B) : ℝ) := by
  classical
  have hn : 0 < n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = opn (ZB D B) := ⟨_, rfl⟩
  rw [← hlam]
  have hlam1 : 1 ≤ lam := hlam ▸ one_le_opn_ZB hD hDn hrows hcols
  have hlam0 : 0 < lam := by linarith
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hxD : (D : ℝ) / lam ≤ D := div_le_self hD0 hlam1
  have hx0 : 0 ≤ (D : ℝ) / lam := by positivity
  by_cases hx : (D : ℝ) / lam < 1
  · have h1 : (1 : ℝ) ≤ signRank (orComposition k B) := by exact_mod_cast signRank_pos _
    exact (pow_le_one₀ hx0 hx.le).trans h1
  · push Not at hx
    set x : ℝ := (D : ℝ) / lam with hxdef
    have hα0 : 0 ≤ (1 + x) ^ k := by positivity
    set d : ℕ := ⌊(1 + x) ^ k⌋₊ with hd
    have hdα : (d : ℝ) ≤ (1 + x) ^ k := Nat.floor_le hα0
    have hd2 : 2 ≤ d := by
      apply Nat.le_floor
      have : (1 + x) ≤ (1 + x) ^ k := le_self_pow₀ (by linarith) (by omega)
      push_cast; linarith
    have hd0 : 0 < d := by omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hxd : x ^ k ≤ d := by
      have h1 := one_add_pow_ge x hx0 k hk
      have h2 : (1 + x) ^ k < d + 1 := Nat.lt_floor_add_one _
      linarith
    have hdD : d ≤ (D + 1) ^ k := by
      have : (d : ℝ) ≤ ((D : ℝ) + 1) ^ k :=
        hdα.trans (pow_le_pow_left₀ (by linarith) (by linarith) k)
      exact_mod_cast this
    set β : ℝ := 1 + 2 * (D : ℝ) / lam with hβ
    have hβ1 : 1 ≤ β := by
      have : 0 ≤ 2 * (D : ℝ) / lam := by positivity
      linarith
    have hβD : β ≤ 1 + 2 * D := by
      have : 2 * (D : ℝ) / lam ≤ 2 * D := div_le_self (by positivity) hlam1
      linarith
    have hdβ : (d : ℝ) ≤ β ^ k := by
      refine hdα.trans (pow_le_pow_left₀ (by linarith) ?_ k)
      have : (2 : ℝ) * D / lam = 2 * ((D : ℝ) / lam) := by ring
      rw [hβ, this]; linarith
    obtain ⟨A, hA1, hA2, hA3⟩ := witness hD hDn hk hrows hcols lam hlam hlam1 d hd0 hdα
    have hsp := sparse hD hDn hk hrows hnbig β hβ1 hβD d hdD
    have hdL : (d : ℝ) * (β ^ k / d) = β ^ k := by field_simp
    have : Nonempty (Fin k → Fin n) := ⟨fun _ => ⟨0, hn⟩⟩
    have key := lemma_13 (X := Fin k → Fin n) (Y := Fin k → Fin n) d hd2 (β ^ k / d)
      (by rw [le_div_iff₀ hdR]; linarith) (orComposition k B)
      (by
        rw [hdL]
        simpa using hsp)
      ⟨A, hA1, hA2, hA3⟩
    have : (d : ℝ) ≤ (signRank (orComposition k B) : ℝ) := by exact_mod_cast key
    exact hxd.trans this

end Count

end SignRankMargin.OREquality.Dev.T14

namespace SignRankMargin.OREquality.Supplement

theorem chk_theorem_14 (n D k : ℕ) (hD : 1 ≤ D) (hDn : D < n) (hk : 1 ≤ k)
    (B : Matrix (Fin n) (Fin n) Bool)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D)
    (hcols : ∀ y, (∑ x, if B x y then (1 : ℕ) else 0) = D) :
    signRank (orComposition k B) ≤ (3 * D) ^ k ∧
    (2 ^ ((6 * D) ^ (k + 1)) ≤ n →
      ((D : ℝ) / ‖(Matrix.toEuclideanLin
          (fun x y => (if B x y then (1 : ℝ) else 0) - (D : ℝ) / (n : ℝ))
          ).toContinuousLinearMap‖) ^ k ≤
        (signRank (orComposition k B) : ℝ)) := by
  refine ⟨?_, fun hnbig => ?_⟩
  · have h9 := (lemma_9 k D n n hk hD (by omega) (by omega) B (fun x => (hrows x).le)).1
    exact h9.trans (Dev.T14.upper_bound D k hD hk)
  · exact Dev.T14.lower hD hDn hk hrows hcols hnbig

end SignRankMargin.OREquality.Supplement
end

theorem solution : type_of% @SignRankMargin.OREquality.Supplement.chk_theorem_14 := @SignRankMargin.OREquality.Supplement.chk_theorem_14
