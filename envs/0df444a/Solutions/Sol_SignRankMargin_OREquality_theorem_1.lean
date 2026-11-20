-- Prove2me | solution 1 for SignRankMargin.OREquality.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:11:25.374463+00:00
-- url     : https://prove2.me/submissions/92407503-eea6-438e-af83-ae5429aa7988

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
namespace SignRankMargin.OREquality
namespace Dev.T1

theorem sum_prod_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (g : ι → ι → ℝ) :
    ∑ x : Fin k → ι, ∑ y : Fin k → ι, ∏ i, g (x i) (y i) = (∑ a, ∑ b, g a b) ^ k := by
  have h1 : ∀ x : Fin k → ι, ∑ y : Fin k → ι, ∏ i, g (x i) (y i) = ∏ i, ∑ b, g (x i) b :=
    fun x => (Fintype.prod_sum (fun i b => g (x i) b)).symm
  simp only [h1]
  exact (Fintype.sum_pow (fun a => ∑ b, g a b) k).symm

/-- The single factor `J - c Id`. -/
def single (ι : Type*) [DecidableEq ι] (c : ℝ) : Matrix ι ι ℝ :=
  fun a b => 1 - c * (if a = b then 1 else 0)

theorem bd_single {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ)
    (hc : (Fintype.card ι : ℝ) = 2 * c) : Tensor.Bd (single ι c) c := by
  intro w
  set S := ∑ y, w y with hS
  have e : ∀ x, ∑ y, single ι c x y * w y = S - c * w x := by
    intro x
    have : ∀ y, single ι c x y * w y = w y - if x = y then c * w x else 0 := by
      intro y
      by_cases h : x = y
      · subst h; simp [single]; ring
      · simp [single, h]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, hS]
  simp only [e]
  have : ∑ x, (S - c * w x) ^ 2 = (Fintype.card ι : ℝ) * S ^ 2 - 2 * c * S * S +
      c ^ 2 * ∑ x, w x ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp only [← Finset.mul_sum, mul_assoc]
    rw [← hS]
    ring
  rw [this, hc]; ring_nf; exact le_refl _

theorem arith (k n : ℕ) (hk : 1 ≤ k) (h : 10 * k * 2 ^ k ≤ n) :
    (k : ℝ) * (3 : ℝ) ^ (6 * (k * 2 ^ k)) ≤ 2 ^ n := by
  set m := k * 2 ^ k with hm
  have hkm : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hm2 : k * (k + 1) ≤ m := Nat.mul_le_mul_left _ hkm
  have h1 : (2 : ℝ) ^ (10 * m) ≤ 2 ^ n := by
    apply pow_le_pow_right₀ (by norm_num)
    calc 10 * m = 10 * k * 2 ^ k := by rw [hm]; ring
      _ ≤ n := h
  have h2 : (1 : ℝ) + m * (295 / 729) ≤ (1024 / 729) ^ m := by
    have := one_add_mul_le_pow (a := (295 / 729 : ℝ)) (by norm_num) m
    norm_num at this ⊢; linarith
  have hkR : (k : ℝ) * (k + 1) ≤ m := by exact_mod_cast hm2
  have h3 : (k : ℝ) ≤ (1024 / 729) ^ m := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have h729 : (3 : ℝ) ^ (6 * m) = 729 ^ m := by
    rw [pow_mul]; norm_num
  have h1024 : (2 : ℝ) ^ (10 * m) = 1024 ^ m := by
    rw [pow_mul]; norm_num
  have h4 : (1024 / 729 : ℝ) ^ m * 729 ^ m = 1024 ^ m := by
    rw [← mul_pow]; norm_num
  calc (k : ℝ) * 3 ^ (6 * m) = k * 729 ^ m := by rw [h729]
    _ ≤ (1024 / 729) ^ m * 729 ^ m :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 2 ^ (10 * m) := by rw [h4, h1024]
    _ ≤ 2 ^ n := h1

theorem norm_single_le (n : ℕ) :
    ‖(Matrix.toEuclideanLin (single (Fin (2 ^ n)) ((2 : ℝ) ^ n / 2))).toContinuousLinearMap‖ ≤
      (2 : ℝ) ^ n / 2 :=
  Tensor.opNorm_le_of_bd _ _ (by positivity)
    (bd_single _ (by rw [Fintype.card_fin]; push_cast; ring))

theorem oneCount_le (k n : ℕ) (hn : 1 ≤ n) :
    (oneCount (orEquality k n) : ℝ) ≤ (k / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ k * ((2 : ℝ) ^ n) ^ k := by
  set N : ℝ := (2 : ℝ) ^ n with hN
  have hN2 : (2 : ℝ) ≤ N := by
    rw [hN]; calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hNpos : 0 < N := by linarith
  let g : Fin (2 ^ n) → Fin (2 ^ n) → ℝ := fun a b => if a = b then 0 else 1
  have hpt : ∀ x y : Fin k → Fin (2 ^ n),
      (if orEquality k n x y then (1 : ℝ) else 0) = 1 - ∏ i, g (x i) (y i) := by
    intro x y
    by_cases h : ∃ i, x i = y i
    · obtain ⟨i, hi⟩ := h
      have hF : orEquality k n x y = true := by
        simp [orEquality, orComposition, equalityMatrix]
        exact ⟨i, hi⟩
      have : ∏ i, g (x i) (y i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g, hi])
      rw [hF, this]; simp
    · have h' : ∀ i, x i ≠ y i := fun i hi => h ⟨i, hi⟩
      have hF : orEquality k n x y = false := by
        simp [orEquality, orComposition, equalityMatrix]
        exact h'
      have : ∏ i, g (x i) (y i) = 1 :=
        Finset.prod_eq_one (fun i _ => by simp [g, h' i])
      rw [hF, this]; simp
  have hcount : (oneCount (orEquality k n) : ℝ) =
      ∑ x : Fin k → Fin (2 ^ n), ∑ y : Fin k → Fin (2 ^ n),
        (1 - ∏ i, g (x i) (y i)) := by
    unfold oneCount
    push_cast
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [← hpt]
  have hg : ∑ a : Fin (2 ^ n), ∑ b : Fin (2 ^ n), g a b = N * (N - 1) := by
    have : ∀ a : Fin (2 ^ n), ∑ b : Fin (2 ^ n), g a b = N - 1 := by
      intro a
      have : ∀ b : Fin (2 ^ n), g a b = 1 - if a = b then 1 else 0 := by
        intro b; by_cases h : a = b <;> simp [g, h]
      simp [this, Finset.sum_sub_distrib, hN]
    simp [this, hN]; ring
  have hcard : ∑ x : Fin k → Fin (2 ^ n), ∑ y : Fin k → Fin (2 ^ n), (1 : ℝ) = N ^ k * N ^ k := by
    have hc : (Fintype.card (Fin k → Fin (2 ^ n)) : ℝ) = N ^ k := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hc]
  rw [hcount]
  simp only [Finset.sum_sub_distrib]
  rw [sum_prod_pow k g, hg]
  have hb := one_add_mul_le_pow (a := -1 / N) (by
    rw [div_eq_mul_inv]
    have : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith) k
  have heq : N * (N - 1) = N ^ 2 * (1 + -1 / N) := by field_simp; ring
  have hP : 0 ≤ N ^ k * N ^ k := by positivity
  have h2 := mul_le_mul_of_nonneg_left hb hP
  have h3 : (N ^ 2) ^ k = N ^ k * N ^ k := by rw [← pow_mul, mul_comm, pow_mul, ← pow_two]
  rw [hcard, heq, mul_pow, h3]
  have e : k / N * N ^ k * N ^ k = N ^ k * N ^ k * (k * (-1 / N)) * (-1) := by ring
  rw [e]
  nlinarith

theorem avg_le (k n : ℕ) (hn : 1 ≤ n) :
    uniformAverage (fun (x y : Fin k → Fin (2 ^ n)) =>
      |-∏ i, single (Fin (2 ^ n)) ((2 : ℝ) ^ n / 2) (x i) (y i)|) ≤ (3 / 2) ^ k := by
  set N : ℝ := (2 : ℝ) ^ n with hN
  have hN2 : (2 : ℝ) ≤ N := by
    rw [hN]; calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hNpos : 0 < N := by linarith
  have habs : ∀ x y : Fin k → Fin (2 ^ n),
      |-∏ i, single (Fin (2 ^ n)) (N / 2) (x i) (y i)| =
        ∏ i, (fun a b : Fin (2 ^ n) => 1 + if a = b then N / 2 - 2 else 0) (x i) (y i) := by
    intro x y
    rw [abs_neg, Finset.abs_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases h : x i = y i
    · simp only [single, h, if_true]
      rw [abs_of_nonpos (by linarith)]; ring
    · simp [single, h]
  have hs : ∑ a : Fin (2 ^ n), ∑ b : Fin (2 ^ n),
      (fun a b : Fin (2 ^ n) => 1 + if a = b then N / 2 - 2 else 0) a b = N * (3 * N / 2 - 2) := by
    simp [Finset.sum_add_distrib, hN]
    ring
  have hc : (Fintype.card (Fin k → Fin (2 ^ n)) : ℝ) = N ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
  unfold uniformAverage
  simp only [habs, hc]
  have hsp := sum_prod_pow k (fun a b : Fin (2 ^ n) => 1 + if a = b then N / 2 - 2 else 0)
  beta_reduce at hsp hs
  rw [hsp, hs]
  have hP : 0 < N ^ k * N ^ k := by positivity
  rw [div_le_iff₀ hP]
  have h3 : (3 / 2 : ℝ) ^ k * (N ^ k * N ^ k) = ((3 / 2) * N ^ 2) ^ k := by
    rw [mul_pow, ← pow_mul, ← pow_mul]; ring
  rw [h3]
  apply pow_le_pow_left₀
  · have : 0 ≤ 3 * N / 2 - 2 := by linarith
    positivity
  · nlinarith

theorem norm_neg_euclid {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    ‖(Matrix.toEuclideanLin (-M)).toContinuousLinearMap‖ =
      ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ := by
  have : (Matrix.toEuclideanLin (-M)).toContinuousLinearMap =
      -(Matrix.toEuclideanLin M).toContinuousLinearMap := by
    ext v : 1
    simp
  rw [this, norm_neg]

end Dev.T1

open Dev.T1 in
theorem chk_theorem_1 (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    signRank (orEquality k n) < 2 ^ (k + 1) ∧
    (10 * k * 2 ^ k ≤ n → 2 ^ k ≤ signRank (orEquality k n)) := by
  constructor
  · have h := (lemma_9 k 1 1 1 hk le_rfl le_rfl le_rfl (fun _ _ => false) (by simp)).2 n hn
    have := Nat.two_pow_pos (k + 1)
    omega
  · intro h
    have hd : 2 ≤ 2 ^ k := calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have : NeZero (2 ^ n) := ⟨by positivity⟩
    set N : ℝ := (2 : ℝ) ^ n with hN
    have hN2 : (2 : ℝ) ≤ N := by
      rw [hN]; calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hNpos : 0 < N := by linarith
    have hc : (Fintype.card (Fin k → Fin (2 ^ n)) : ℝ) = N ^ k := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
    refine lemma_13 (X := Fin k → Fin (2 ^ n)) (Y := Fin k → Fin (2 ^ n)) (2 ^ k) hd
      ((3 / 2 : ℝ) ^ k) (one_le_pow₀ (by norm_num)) (orEquality k n) ?_ ?_
    · rw [hc]
      have h3 : (((2 ^ k : ℕ) : ℝ) * (3 / 2 : ℝ) ^ k) = 3 ^ k := by
        push_cast; rw [← mul_pow]; norm_num
      rw [h3]
      have h4 : ((3 : ℝ) ^ k) ^ (6 * 2 ^ k) = 3 ^ (6 * (k * 2 ^ k)) := by
        rw [← pow_mul]; congr 1; ring
      rw [h4]
      have hT : (0 : ℝ) < 3 ^ (6 * (k * 2 ^ k)) := by positivity
      have hk' : (k : ℝ) / N ≤ ((3 : ℝ) ^ (6 * (k * 2 ^ k)))⁻¹ := by
        rw [div_le_iff₀ hNpos, inv_mul_eq_div, le_div_iff₀ hT]
        have := arith k n hk h
        linarith
      have := oneCount_le k n hn
      calc (oneCount (orEquality k n) : ℝ) ≤ (k / N) * N ^ k * N ^ k := this
        _ ≤ ((3 : ℝ) ^ (6 * (k * 2 ^ k)))⁻¹ * N ^ k * N ^ k := by
            gcongr
    · refine ⟨fun x y => -∏ i, single (Fin (2 ^ n)) (N / 2) (x i) (y i), ?_, ?_, ?_⟩
      · intro x y hF
        have h' : ∀ i, x i ≠ y i := by
          intro i hi
          have : orEquality k n x y = true := by
            simp [orEquality, orComposition, equalityMatrix]
            exact ⟨i, hi⟩
          rw [this] at hF; exact absurd hF (by simp)
        have : ∏ i, single (Fin (2 ^ n)) (N / 2) (x i) (y i) = 1 :=
          Finset.prod_eq_one (fun i _ => by simp [single, h' i])
        show -(∏ i, single (Fin (2 ^ n)) (N / 2) (x i) (y i)) ≤ -1
        rw [this]
      · exact avg_le k n hn
      · rw [hc]
        let A' : Matrix (Fin k → Fin (2 ^ n)) (Fin k → Fin (2 ^ n)) ℝ := fun x y =>
          ∏ i, single (Fin (2 ^ n)) (N / 2) (x i) (y i)
        change ‖(Matrix.toEuclideanLin (-A')).toContinuousLinearMap‖ ≤ _
        rw [norm_neg_euclid]
        have h1 := Dev.Tensor.opNorm_tensorPow k (single (Fin (2 ^ n)) (N / 2))
          A' (fun _ _ => rfl)
        have h2 := pow_le_pow_left₀ (norm_nonneg _) (norm_single_le n) k
        refine h1.trans (h2.trans ?_)
        rw [Real.sqrt_mul_self (by positivity)]
        push_cast
        rw [div_pow, hN]

end SignRankMargin.OREquality
end

theorem solution : type_of% @SignRankMargin.OREquality.chk_theorem_1 := @SignRankMargin.OREquality.chk_theorem_1
