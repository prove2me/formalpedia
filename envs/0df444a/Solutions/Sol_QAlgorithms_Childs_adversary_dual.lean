-- Prove2me | solution 1 for QAlgorithms.Childs.adversary_dual
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:49:42.548765+00:00
-- url     : https://prove2.me/submissions/021861b7-4b81-4d9b-9691-45e37a7f8fd3

import Definitions.Def_QAlgorithms_Defs_Adversary

set_option autoImplicit false

open QAlgorithms
open scoped ComplexConjugate NNReal ENNReal Matrix BigOperators

namespace SolAdversaryDual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Part 1: Basic properties of `specNorm` and `maxMaskedNorm` -/

lemma specNorm_eq_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    specNorm A = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) A‖ :=
  rfl

lemma toEuclideanCLM_apply_ofLp {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (u : EuclideanSpace ℝ n) (x : n) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) M u).ofLp x = ∑ y : n, M x y * u.ofLp y :=
  rfl

lemma specNorm_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : 0 ≤ specNorm A := by
  rw [specNorm_eq_opNorm]
  exact norm_nonneg _

omit [DecidableEq ι] in
lemma specNorm_maskMatrix_le {D : Finset (ι → Bool)} (Γ : Matrix D D ℝ) (i : ι) :
    specNorm (maskMatrix Γ i) ≤ maxMaskedNorm Γ :=
  le_ciSup (f := fun j : ι => specNorm (maskMatrix Γ j)) (Finite.bddAbove_range _) i

omit [DecidableEq ι] in
lemma maxMaskedNorm_nonneg {D : Finset (ι → Bool)} (Γ : Matrix D D ℝ) :
    0 ≤ maxMaskedNorm Γ := by
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    exact le_trans (specNorm_nonneg _) (specNorm_maskMatrix_le Γ i₀)
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    unfold maxMaskedNorm
    simp

omit [DecidableEq ι] in
lemma sum_mul_matrix_mul_le_specNorm {D : Finset (ι → Bool)} (M : Matrix D D ℝ)
    (a b : D → ℝ) :
    ∑ x : D, ∑ y : D, a x * M x y * b y ≤
      specNorm M * Real.sqrt (∑ x : D, a x ^ 2) * Real.sqrt (∑ y : D, b y ^ 2) := by
  let ua : EuclideanSpace ℝ D := WithLp.toLp 2 a
  let ub : EuclideanSpace ℝ D := WithLp.toLp 2 b
  have hinner : ∑ x : D, ∑ y : D, a x * M x y * b y =
      inner ℝ ua (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) M ub) := by
    simp only [ua, ub, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct, toEuclideanCLM_apply_ofLp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => by ring
  have hna : ‖ua‖ = Real.sqrt (∑ x : D, a x ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [ua]
  have hnb : ‖ub‖ = Real.sqrt (∑ y : D, b y ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [ub]
  rw [hinner, specNorm_eq_opNorm, ← hna, ← hnb]
  calc inner ℝ ua (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) M ub)
    _ ≤ ‖inner ℝ ua (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) M ub)‖ := le_abs_self _
    _ ≤ ‖ua‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) M ub‖ := norm_inner_le_norm _ _
    _ ≤ ‖ua‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) M‖ * ‖ub‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) M‖ * ‖ua‖ * ‖ub‖ := by ring

omit [DecidableEq ι] in
lemma specNorm_pos_of_entry_ne_zero {D : Finset (ι → Bool)} (M : Matrix D D ℝ)
    (x₀ y₀ : D) (hne : M x₀ y₀ ≠ 0) : 0 < specNorm M := by
  let a : D → ℝ := fun x => if x = x₀ then (if 0 ≤ M x₀ y₀ then 1 else -1) else 0
  let b : D → ℝ := fun y => if y = y₀ then 1 else 0
  have h := sum_mul_matrix_mul_le_specNorm M a b
  have h1 : ∑ x : D, ∑ y : D, a x * M x y * b y = |M x₀ y₀| := by
    rw [Finset.sum_eq_single x₀, Finset.sum_eq_single y₀]
    · dsimp [a, b]
      simp only [↓reduceIte, mul_one]
      split_ifs with h0
      · rw [one_mul, abs_of_nonneg h0]
      · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h0)]
    · intro y _ hy
      dsimp [b]
      simp [hy]
    · intro hx₀
      exact False.elim (hx₀ (Finset.mem_univ y₀))
    · intro x _ hx
      refine Finset.sum_eq_zero fun y _ => ?_
      dsimp [a]
      simp [hx]
    · intro hx₀
      exact False.elim (hx₀ (Finset.mem_univ x₀))
  have h2 : ∑ x : D, a x ^ 2 = 1 := by
    rw [Finset.sum_eq_single x₀]
    · dsimp [a]
      simp only [↓reduceIte]
      split_ifs <;> ring
    · intro x _ hx
      dsimp [a]
      simp [hx]
    · intro hx₀
      exact False.elim (hx₀ (Finset.mem_univ x₀))
  have h3 : ∑ y : D, b y ^ 2 = 1 := by
    rw [Finset.sum_eq_single y₀]
    · dsimp [b]; simp
    · intro y _ hy
      dsimp [b]; simp [hy]
    · intro hy₀
      exact False.elim (hy₀ (Finset.mem_univ y₀))
  rw [h1, h2, h3, Real.sqrt_one, mul_one, mul_one] at h
  exact lt_of_lt_of_le (abs_pos.mpr hne) h

lemma maxMaskedNorm_pos_of_ne_zero (f : (ι → Bool) → Bool) (D : Finset (ι → Bool))
    (Γ : Matrix D D ℝ) (hΓ : IsAdversaryMatrix f D Γ) (hne : Γ ≠ 0) :
    0 < maxMaskedNorm Γ := by
  have hex : ∃ x y : D, Γ x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Matrix.ext h)
  rcases hex with ⟨x, y, hxy⟩
  have hfxy : f x ≠ f y := fun h => hxy (hΓ.2 x y h)
  have hval : (x : ι → Bool) ≠ (y : ι → Bool) := fun h => hfxy (congrArg f h)
  have hi : ∃ i : ι, (x : ι → Bool) i ≠ (y : ι → Bool) i := by
    by_contra h
    push Not at h
    exact hval (funext h)
  rcases hi with ⟨i₀, hi₀⟩
  have hm : maskMatrix Γ i₀ x y ≠ 0 := by
    simp [maskMatrix, hi₀, hxy]
  exact lt_of_lt_of_le (specNorm_pos_of_entry_ne_zero (maskMatrix Γ i₀) x y hm)
    (specNorm_maskMatrix_le Γ i₀)

lemma real_cs_sum {α : Type*} (s : Finset α) (f g : α → ℝ) :
    ∑ i ∈ s, f i * g i ≤
      Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) :=
  Real.sum_mul_le_sqrt_mul_sqrt s f g

lemma sum_xy_p_swap {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℝ) :
    ∑ a : α, ∑ b : β, ∑ c : γ, F a b c = ∑ c : γ, ∑ a : α, ∑ b : β, F a b c := by
  trans ∑ a : α, ∑ c : γ, ∑ b : β, F a b c
  · exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  · exact Finset.sum_comm

/-! ### Part 2: Weak Duality -/

omit [DecidableEq ι] in
lemma norm_sq_le_childsDualObjective (f : (ι → Bool) → Bool) (D : Finset (ι → Bool))
    {d : ℕ} (v : D → ι → EuclideanSpace ℂ (Fin d)) (x : D) :
    ∑ i : ι, ‖v x i‖ ^ 2 ≤ (childsDualObjective f D v : ℝ) := by
  have hx : x ∈ Finset.univ.filter (fun z : D => f z = f x) := by simp
  have hle : (∑ i : ι, ‖v x i‖₊ ^ 2 : ℝ≥0) ≤ childsBComplexity f D v (f x) :=
    Finset.le_sup (f := fun z : D => ∑ i : ι, ‖v z i‖₊ ^ 2) hx
  have hle2 : childsBComplexity f D v (f x) ≤ childsDualObjective f D v := by
    unfold childsDualObjective
    cases f x
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hle3 : ((∑ i : ι, ‖v x i‖₊ ^ 2 : ℝ≥0) : ℝ) ≤ (childsDualObjective f D v : ℝ) := by
    exact_mod_cast le_trans hle hle2
  simpa [NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm] using hle3

def dualComp {D : Finset (ι → Bool)} {d : ℕ}
    (v : D → ι → EuclideanSpace ℂ (Fin d)) (p : ι × Fin d × Bool) (x : D) : ℝ :=
  if p.2.2 then (v x p.1 p.2.1).im else (v x p.1 p.2.1).re

omit [Fintype ι] [DecidableEq ι] in
lemma sum_dualComp_mul {D : Finset (ι → Bool)} {d : ℕ}
    (v : D → ι → EuclideanSpace ℂ (Fin d)) (i : ι) (x y : D) :
    ∑ kb : Fin d × Bool, dualComp v (i, kb) x * dualComp v (i, kb) y =
      (inner ℂ (v x i) (v y i)).re := by
  rw [Fintype.sum_prod_type]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Complex.re_sum, Complex.mul_re]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fintype.sum_bool, dualComp, ↓reduceIte, Bool.false_eq_true, Pi.star_apply,
    RCLike.star_def, Complex.conj_re, Complex.conj_im]
  ring

omit [DecidableEq ι] in
lemma sum_dualComp_sq {D : Finset (ι → Bool)} {d : ℕ}
    (v : D → ι → EuclideanSpace ℂ (Fin d)) (x : D) :
    ∑ p : ι × Fin d × Bool, (dualComp v p x) ^ 2 = ∑ i : ι, ‖v x i‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fintype.sum_bool, dualComp, ↓reduceIte, Bool.false_eq_true]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

lemma weak_duality_bound (f : (ι → Bool) → Bool) (D : Finset (ι → Bool))
    {d : ℕ} (v : D → ι → EuclideanSpace ℂ (Fin d)) (hfeas : DualFeasibleChilds f D d v)
    (Γ : Matrix D D ℝ) (hΓ : IsAdversaryMatrix f D Γ) :
    specNorm Γ ≤ (childsDualObjective f D v : ℝ) * maxMaskedNorm Γ := by
  let C : ℝ := (childsDualObjective f D v : ℝ)
  have hC : 0 ≤ C := by positivity
  have hM : 0 ≤ maxMaskedNorm Γ := maxMaskedNorm_nonneg Γ
  rw [specNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hM) fun u => ?_
  let w : EuclideanSpace ℝ D := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) Γ u
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ≤ _
    rw [hw]
    positivity
  have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
  have hnorm_sq : ‖w‖ ^ 2 = ∑ x : D, ∑ y : D, w x * Γ x y * u y := by
    have h1 : ‖w‖ ^ 2 = inner ℝ w (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) Γ u) := by
      rw [real_inner_self_eq_norm_mul_norm, sq]
    rw [h1]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      toEuclideanCLM_apply_ofLp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => by ring
  have hentry : ∀ x y : D,
      Γ x y = ∑ p : ι × Fin d × Bool,
        maskMatrix Γ p.1 x y * (dualComp v p x * dualComp v p y) := by
    intro x y
    rw [Fintype.sum_prod_type]
    have hstep : ∀ i : ι,
        ∑ kb : Fin d × Bool, maskMatrix Γ i x y * (dualComp v (i, kb) x * dualComp v (i, kb) y) =
          maskMatrix Γ i x y * (inner ℂ (v x i) (v y i)).re := by
      intro i
      rw [← Finset.mul_sum, sum_dualComp_mul]
    simp_rw [hstep]
    by_cases hxy : f x = f y
    · have h0 : Γ x y = 0 := hΓ.2 x y hxy
      have hm0 : ∀ i : ι, maskMatrix Γ i x y = 0 := fun i => by simp [maskMatrix, h0]
      simp [h0, hm0]
    · have hne : x ≠ y := fun h => hxy (congrArg (fun z : D => f z) h)
      have hf := congrArg Complex.re (hfeas x y hne)
      rw [if_neg hxy, Complex.one_re, Complex.re_sum] at hf
      calc Γ x y
        _ = Γ x y * 1 := (mul_one _).symm
        _ = Γ x y * ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
              (inner ℂ (v x i) (v y i)).re := by rw [← hf]
        _ = ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
              Γ x y * (inner ℂ (v x i) (v y i)).re := Finset.mul_sum _ _ _
        _ = ∑ i : ι, (maskMatrix Γ i x y) * (inner ℂ (v x i) (v y i)).re := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun i : ι => (x : ι → Bool) i ≠ (y : ι → Bool) i)]
            have h2 : ∑ i ∈ Finset.univ.filter (fun i : ι => ¬(x : ι → Bool) i ≠ (y : ι → Bool) i),
                (maskMatrix Γ i x y) * (inner ℂ (v x i) (v y i)).re = 0 := by
              refine Finset.sum_eq_zero fun i hi => ?_
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
              simp [maskMatrix, hi]
            rw [h2, add_zero]
            refine Finset.sum_congr rfl fun i hi => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            simp [maskMatrix, hi]
  have hsum_eq : ‖w‖ ^ 2 =
      ∑ p : ι × Fin d × Bool, ∑ x : D, ∑ y : D,
        (w x * dualComp v p x) * maskMatrix Γ p.1 x y * (u y * dualComp v p y) := by
    rw [hnorm_sq, ← sum_xy_p_swap]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hentry x y, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => by ring
  let A (p : ι × Fin d × Bool) : ℝ := ∑ x : D, (w x * dualComp v p x) ^ 2
  let B (p : ι × Fin d × Bool) : ℝ := ∑ y : D, (u y * dualComp v p y) ^ 2
  have hA_nonneg : ∀ p, 0 ≤ A p := fun p => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB_nonneg : ∀ p, 0 ≤ B p := fun p => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hstep1 : ‖w‖ ^ 2 ≤
      maxMaskedNorm Γ * ∑ p : ι × Fin d × Bool, Real.sqrt (A p) * Real.sqrt (B p) := by
    rw [hsum_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    calc ∑ x : D, ∑ y : D, (w x * dualComp v p x) * maskMatrix Γ p.1 x y * (u y * dualComp v p y)
      _ ≤ specNorm (maskMatrix Γ p.1) * Real.sqrt (A p) * Real.sqrt (B p) :=
          sum_mul_matrix_mul_le_specNorm (maskMatrix Γ p.1)
            (fun x => w x * dualComp v p x) (fun y => u y * dualComp v p y)
      _ ≤ maxMaskedNorm Γ * Real.sqrt (A p) * Real.sqrt (B p) := by
          gcongr
          exact specNorm_maskMatrix_le Γ p.1
      _ = maxMaskedNorm Γ * (Real.sqrt (A p) * Real.sqrt (B p)) := by ring
  have hsumA : ∑ p : ι × Fin d × Bool, A p ≤ C * ‖w‖ ^ 2 := by
    dsimp [A]
    rw [Finset.sum_comm]
    calc ∑ x : D, ∑ p : ι × Fin d × Bool, (w x * dualComp v p x) ^ 2
      _ = ∑ x : D, w x ^ 2 * (∑ p : ι × Fin d × Bool, dualComp v p x ^ 2) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring
      _ = ∑ x : D, w x ^ 2 * (∑ i : ι, ‖v x i‖ ^ 2) := by
          refine Finset.sum_congr rfl fun x _ => by rw [sum_dualComp_sq]
      _ ≤ ∑ x : D, w x ^ 2 * C := by
          refine Finset.sum_le_sum fun x _ => ?_
          gcongr
          exact norm_sq_le_childsDualObjective f D v x
      _ = C * ‖w‖ ^ 2 := by
          rw [← Finset.sum_mul, mul_comm, EuclideanSpace.norm_eq,
            Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
          simp
  have hsumB : ∑ p : ι × Fin d × Bool, B p ≤ C * ‖u‖ ^ 2 := by
    dsimp [B]
    rw [Finset.sum_comm]
    calc ∑ y : D, ∑ p : ι × Fin d × Bool, (u y * dualComp v p y) ^ 2
      _ = ∑ y : D, u y ^ 2 * (∑ p : ι × Fin d × Bool, dualComp v p y ^ 2) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring
      _ = ∑ y : D, u y ^ 2 * (∑ i : ι, ‖v y i‖ ^ 2) := by
          refine Finset.sum_congr rfl fun y _ => by rw [sum_dualComp_sq]
      _ ≤ ∑ y : D, u y ^ 2 * C := by
          refine Finset.sum_le_sum fun y _ => ?_
          gcongr
          exact norm_sq_le_childsDualObjective f D v y
      _ = C * ‖u‖ ^ 2 := by
          rw [← Finset.sum_mul, mul_comm, EuclideanSpace.norm_eq,
            Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
          simp
  have hcs : ∑ p : ι × Fin d × Bool, Real.sqrt (A p) * Real.sqrt (B p) ≤
      C * ‖w‖ * ‖u‖ := by
    calc ∑ p : ι × Fin d × Bool, Real.sqrt (A p) * Real.sqrt (B p)
      _ ≤ Real.sqrt (∑ p : ι × Fin d × Bool, Real.sqrt (A p) ^ 2) *
            Real.sqrt (∑ p : ι × Fin d × Bool, Real.sqrt (B p) ^ 2) :=
          real_cs_sum Finset.univ (fun p => Real.sqrt (A p)) (fun p => Real.sqrt (B p))
      _ = Real.sqrt (∑ p : ι × Fin d × Bool, A p) *
            Real.sqrt (∑ p : ι × Fin d × Bool, B p) := by
          congr 2 <;> refine Finset.sum_congr rfl fun p _ => Real.sq_sqrt (by positivity)
      _ ≤ Real.sqrt (C * ‖w‖ ^ 2) * Real.sqrt (C * ‖u‖ ^ 2) := by
          gcongr
      _ = (Real.sqrt C * ‖w‖) * (Real.sqrt C * ‖u‖) := by
          rw [Real.sqrt_mul hC, Real.sqrt_mul hC,
            Real.sqrt_sq (norm_nonneg w), Real.sqrt_sq (norm_nonneg u)]
      _ = (Real.sqrt C * Real.sqrt C) * ‖w‖ * ‖u‖ := by ring
      _ = C * ‖w‖ * ‖u‖ := by rw [Real.mul_self_sqrt hC]
  have hquad : ‖w‖ ^ 2 ≤ (C * maxMaskedNorm Γ * ‖u‖) * ‖w‖ := by
    calc ‖w‖ ^ 2
      _ ≤ maxMaskedNorm Γ * (C * ‖w‖ * ‖u‖) := by
          exact le_trans hstep1 (mul_le_mul_of_nonneg_left hcs hM)
      _ = (C * maxMaskedNorm Γ * ‖u‖) * ‖w‖ := by ring
  have hdiv : ‖w‖ ≤ C * maxMaskedNorm Γ * ‖u‖ := by
    nlinarith
  exact hdiv

lemma advPm_le_dualObjective (f : (ι → Bool) → Bool) (D : Finset (ι → Bool))
    {d : ℕ} (v : D → ι → EuclideanSpace ℂ (Fin d)) (hfeas : DualFeasibleChilds f D d v) :
    advPm f D ≤ (childsDualObjective f D v : ℝ≥0∞) := by
  unfold advPm
  refine iSup₂_le fun Γ hΓ => ?_
  have hpos : 0 < maxMaskedNorm Γ := maxMaskedNorm_pos_of_ne_zero f D Γ hΓ.1 hΓ.2
  have hbound := weak_duality_bound f D v hfeas Γ hΓ.1
  have hdiv : specNorm Γ / maxMaskedNorm Γ ≤ (childsDualObjective f D v : ℝ) :=
    (div_le_iff₀ hpos).mpr hbound
  calc ENNReal.ofReal (specNorm Γ / maxMaskedNorm Γ)
    _ ≤ ENNReal.ofReal (childsDualObjective f D v : ℝ) := ENNReal.ofReal_le_ofReal hdiv
    _ = (childsDualObjective f D v : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-! ### Part 3: Parity-Block Construction of Complex Dual Vectors from Real Bipartite Vectors -/

lemma bool_xor_eq_of_ne {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    xor a c = xor b d := by
  revert hab hcd
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma bool_xor_ne_of_eq_of_ne {a b c d : Bool} (hab : a = b) (hcd : c ≠ d) :
    xor a c ≠ xor b d := by
  revert hab hcd
  cases a <;> cases b <;> cases c <;> cases d <;> decide

omit [DecidableEq ι] in
lemma dualFeasibleChilds_of_realBipartite (f : (ι → Bool) → Bool) (D : Finset (ι → Bool))
    {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (u : D → ι → τ → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hfeas : ∀ x y : D, f x = false → f y = true →
      ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
        ∑ t : τ, u x i t * u y i t = 1)
    (hnorm : ∀ z : D, ∑ i : ι, ∑ t : τ, (u z i t) ^ 2 ≤ α) :
    ∃ (d : ℕ) (v : D → ι → EuclideanSpace ℂ (Fin d)),
      0 < d ∧ DualFeasibleChilds f D d v ∧ (childsDualObjective f D v : ℝ) ≤ α := by
  let e : Bool × τ ≃ Fin (Fintype.card (Bool × τ)) := Fintype.equivFin (Bool × τ)
  let d : ℕ := Fintype.card (Bool × τ)
  have hd : 0 < d := Fintype.card_pos
  let v (z : D) (i : ι) : EuclideanSpace ℂ (Fin d) :=
    WithLp.toLp 2 fun k : Fin d =>
      if (e.symm k).1 = xor (f z) ((z : ι → Bool) i) then (u z i (e.symm k).2 : ℂ) else 0
  refine ⟨d, v, hd, ?_, ?_⟩
  · intro x y hne
    have hinner : ∀ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
        inner ℂ (v x i) (v y i) =
          if f x = f y then 0 else ∑ t : τ, (u x i t : ℂ) * (u y i t : ℂ) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [v, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
      have hcomp := e.symm.sum_comp (fun bt : Bool × τ =>
        (if bt.1 = xor (f y) ((y : ι → Bool) i) then (u y i bt.2 : ℂ) else 0) *
          star (if bt.1 = xor (f x) ((x : ι → Bool) i) then (u x i bt.2 : ℂ) else 0))
      rw [hcomp, Fintype.sum_prod_type]
      by_cases hxy : f x = f y
      · rw [if_pos hxy]
        have hxor : xor (f x) ((x : ι → Bool) i) ≠ xor (f y) ((y : ι → Bool) i) :=
          bool_xor_ne_of_eq_of_ne hxy hi
        refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun t _ => ?_
        by_cases hb : b = xor (f x) ((x : ι → Bool) i)
        · simp [hb, hxor]
        · simp [hb]
      · rw [if_neg hxy]
        have hxor : xor (f x) ((x : ι → Bool) i) = xor (f y) ((y : ι → Bool) i) :=
          bool_xor_eq_of_ne hxy hi
        rw [Finset.sum_eq_single (xor (f x) ((x : ι → Bool) i))]
        · refine Finset.sum_congr rfl fun t _ => ?_
          simp [← hxor, mul_comm]
        · intro b _ hb
          refine Finset.sum_eq_zero fun t _ => ?_
          simp [hb]
        · intro hmem
          exact False.elim (hmem (Finset.mem_univ _))
    rw [Finset.sum_congr rfl hinner]
    by_cases hxy : f x = f y
    · simp [hxy]
    · simp only [if_neg hxy]
      cases hfx : f x <;> cases hfy : f y
      · exact False.elim (hxy (hfx.trans hfy.symm))
      · have h1 := hfeas x y hfx hfy
        exact_mod_cast h1
      · have h1 := hfeas y x hfy hfx
        have h2 : ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
            ∑ t : τ, u x i t * u y i t =
            ∑ i ∈ Finset.univ.filter (fun i => (y : ι → Bool) i ≠ (x : ι → Bool) i),
            ∑ t : τ, u y i t * u x i t := by
          refine Finset.sum_bij (fun i _ => i) ?_ ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact Ne.symm hi
          · intro _ _ _ _ h; exact h
          · intro i hi
            refine ⟨i, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact Ne.symm hi
          · intro i _
            refine Finset.sum_congr rfl fun t _ => mul_comm _ _
        exact_mod_cast h2.trans h1
      · exact False.elim (hxy (hfx.trans hfy.symm))
  · have hnorm_z : ∀ z : D, ∑ i : ι, ‖v z i‖ ^ 2 ≤ α := by
      intro z
      have h_i : ∀ i : ι, ‖v z i‖ ^ 2 = ∑ t : τ, (u z i t) ^ 2 := by
        intro i
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        simp only [v]
        have hcomp := e.symm.sum_comp (fun bt : Bool × τ =>
          ‖if bt.1 = xor (f z) ((z : ι → Bool) i) then (u z i bt.2 : ℂ) else 0‖ ^ 2)
        rw [hcomp, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single (xor (f z) ((z : ι → Bool) i))]
        · refine Finset.sum_congr rfl fun t _ => ?_
          simp [Complex.norm_real, sq_abs]
        · intro b _ hb
          refine Finset.sum_eq_zero fun t _ => ?_
          simp [hb]
        · intro hmem
          exact False.elim (hmem (Finset.mem_univ _))
      simp_rw [h_i]
      exact hnorm z
    have h_nnreal : childsDualObjective f D v ≤ Real.toNNReal α := by
      unfold childsDualObjective childsBComplexity
      refine max_le ?_ ?_ <;> refine Finset.sup_le fun z _ => ?_
      · refine (Real.le_toNNReal_iff_coe_le hα).mpr ?_
        simpa [NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm] using hnorm_z z
      · refine (Real.le_toNNReal_iff_coe_le hα).mpr ?_
        simpa [NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm] using hnorm_z z
    have hcoe := NNReal.coe_le_coe.mpr h_nnreal
    rwa [Real.coe_toNNReal α hα] at hcoe

/-! ### Part 4: Existence of a Feasible Solution and Positivity on Non-Constant Domains -/

lemma exists_dualFeasible_of_nonconst (f : (ι → Bool) → Bool) (D : Finset (ι → Bool))
    (x₀ : D) :
    ∃ (d : ℕ) (v : D → ι → EuclideanSpace ℂ (Fin d)),
      0 < d ∧ DualFeasibleChilds f D d v := by
  have : Nonempty (D × D) := ⟨(x₀, x₀)⟩
  have hex_i : ∀ p : D × D, f p.1 = false ∧ f p.2 = true →
      ∃ i : ι, (p.1 : ι → Bool) i ≠ (p.2 : ι → Bool) i := by
    intro p hp
    by_contra h
    push Not at h
    have heq : (p.1 : ι → Bool) = (p.2 : ι → Bool) := funext h
    have hfeq : f p.1 = f p.2 := congrArg f heq
    rw [hp.1, hp.2] at hfeq
    exact Bool.false_ne_true hfeq
  let u (z : D) (i : ι) (p : D × D) : ℝ :=
    if h : f p.1 = false ∧ f p.2 = true then
      if i = Classical.choose (hex_i p h) ∧ (if f z then z = p.2 else z = p.1) then 1 else 0
    else 0
  let α : ℝ := ∑ z : D, ∑ i : ι, ∑ p : D × D, (u z i p) ^ 2
  have hα : 0 ≤ α := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfeas : ∀ x y : D, f x = false → f y = true →
      ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
        ∑ p : D × D, u x i p * u y i p = 1 := by
    intro x y hfx hfy
    have hxy : f (x, y).1 = false ∧ f (x, y).2 = true := ⟨hfx, hfy⟩
    let i₀ : ι := Classical.choose (hex_i (x, y) hxy)
    have hi₀ : (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀ := Classical.choose_spec (hex_i (x, y) hxy)
    rw [Finset.sum_eq_single i₀]
    · rw [Finset.sum_eq_single (x, y)]
      · simp [u, hfx, hfy, i₀]
      · intro p _ hp
        by_cases hp_cond : f p.1 = false ∧ f p.2 = true
        · have hne_p : ¬(x = p.1 ∧ y = p.2) := by
            rintro ⟨rfl, rfl⟩
            exact hp rfl
          simp only [u, dif_pos hp_cond, hfx, hfy, Bool.false_eq_true, ↓reduceIte]
          by_cases hx1 : i₀ = Classical.choose (hex_i p hp_cond) ∧ x = p.1
          · have hy2 : y ≠ p.2 := fun hy => hne_p ⟨hx1.2, hy⟩
            simp [hx1, hy2]
          · simp [hx1]
        · simp [u, dif_neg hp_cond]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
    · intro i _ hi
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : p = (x, y)
      · subst hp
        simp [u, hxy, i₀, hi]
      · by_cases hp_cond : f p.1 = false ∧ f p.2 = true
        · have hne_p : ¬(x = p.1 ∧ y = p.2) := by
            rintro ⟨rfl, rfl⟩
            exact hp rfl
          simp only [u, dif_pos hp_cond, hfx, hfy, Bool.false_eq_true, ↓reduceIte]
          by_cases hx1 : i = Classical.choose (hex_i p hp_cond) ∧ x = p.1
          · have hy2 : y ≠ p.2 := fun hy => hne_p ⟨hx1.2, hy⟩
            simp [hx1, hy2]
          · simp [hx1]
        · simp [u, dif_neg hp_cond]
    · intro hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact False.elim (hmem hi₀)
  have hnorm : ∀ z : D, ∑ i : ι, ∑ p : D × D, (u z i p) ^ 2 ≤ α := by
    intro z
    exact Finset.single_le_sum
      (fun z' _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ z)
  rcases dualFeasibleChilds_of_realBipartite f D u α hα hfeas hnorm with ⟨d, v, hd, hfv, _⟩
  exact ⟨d, v, hd, hfv⟩

lemma advPm_pos_of_false_true (f : (ι → Bool) → Bool) (D : Finset (ι → Bool))
    (x₀ y₀ : D) (hx₀ : f x₀ = false) (hy₀ : f y₀ = true) :
    0 < advPm f D := by
  let Γ₀ : Matrix D D ℝ := Matrix.of fun x y =>
    if (x = x₀ ∧ y = y₀) ∨ (x = y₀ ∧ y = x₀) then 1 else 0
  have hsymm : Γ₀.IsSymm := by
    ext x y
    simp only [Γ₀, Matrix.transpose_apply, Matrix.of_apply]
    by_cases h1 : (y = x₀ ∧ x = y₀) ∨ (y = y₀ ∧ x = x₀) <;>
      by_cases h2 : (x = x₀ ∧ y = y₀) ∨ (x = y₀ ∧ y = x₀)
    · rw [if_pos h1, if_pos h2]
    · exfalso; tauto
    · exfalso; tauto
    · rw [if_neg h1, if_neg h2]
  have hadv : IsAdversaryMatrix f D Γ₀ := by
    refine ⟨hsymm, fun x y hxy => ?_⟩
    simp only [Γ₀, Matrix.of_apply, ite_eq_right_iff]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [hx₀, hy₀] at hxy
      exact False.elim (Bool.false_ne_true hxy)
    · rw [hx₀, hy₀] at hxy
      exact False.elim (Bool.false_ne_true hxy.symm)
  have hentry : Γ₀ x₀ y₀ = 1 := by
    simp [Γ₀]
  have hne : Γ₀ ≠ 0 := by
    intro h0
    have : Γ₀ x₀ y₀ = 0 := by simp [h0]
    linarith
  have hspec : 0 < specNorm Γ₀ :=
    specNorm_pos_of_entry_ne_zero Γ₀ x₀ y₀ (by linarith)
  have hmask : 0 < maxMaskedNorm Γ₀ :=
    maxMaskedNorm_pos_of_ne_zero f D Γ₀ hadv hne
  have hdiv : 0 < ENNReal.ofReal (specNorm Γ₀ / maxMaskedNorm Γ₀) :=
    ENNReal.ofReal_pos.mpr (div_pos hspec hmask)
  exact lt_of_lt_of_le hdiv (le_iSup₂ (f := fun (Γ : Matrix D D ℝ)
    (_ : IsAdversaryMatrix f D Γ ∧ Γ ≠ 0) => ENNReal.ofReal (specNorm Γ / maxMaskedNorm Γ))
    Γ₀ ⟨hadv, hne⟩)

/-! ### Part 5: Compactness of Convex Hull in Finite Dimensions via Carathéodory -/

lemma isCompact_convexHull_of_isCompact {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsCompact S) (hne : S.Nonempty) :
    IsCompact (convexHull ℝ S) := by
  classical
  rcases hne with ⟨s₀, hs₀⟩
  let N : ℕ := Module.finrank ℝ E + 1
  let Φ : (Fin N → ℝ) × (Fin N → E) → E := fun cz => ∑ k : Fin N, cz.1 k • cz.2 k
  have hΦ_cont : Continuous Φ :=
    continuous_finsetSum _ fun k _ =>
      Continuous.smul ((continuous_apply k).comp continuous_fst)
        ((continuous_apply k).comp continuous_snd)
  have h_compact_dom : IsCompact (stdSimplex ℝ (Fin N) ×ˢ Set.pi Set.univ (fun _ : Fin N => S)) :=
    (isCompact_stdSimplex ℝ (Fin N)).prod (isCompact_univ_pi fun _ => hS)
  have h_eq : convexHull ℝ S = Φ '' (stdSimplex ℝ (Fin N) ×ˢ Set.pi Set.univ (fun _ : Fin N => S)) := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases eq_pos_convex_span_of_mem_convexHull hx with
        ⟨τ, hτ_fin, z, w, hz_sub, h_aff, hw_pos, hw_sum, hw_comb⟩
      letI : Fintype τ := hτ_fin
      have hcard : Fintype.card τ ≤ N := by
        calc Fintype.card τ
          _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 := h_aff.card_le_finrank_succ
          _ ≤ Module.finrank ℝ E + 1 := Nat.add_le_add_right (Submodule.finrank_le _) 1
      let e : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ
      let emb (t : τ) : Fin N := Fin.castLE hcard (e t)
      have hemb_inj : Function.Injective emb :=
        (Fin.castLE_injective hcard).comp e.injective
      let c' (k : Fin N) : ℝ := ∑ t : τ, if emb t = k then w t else 0
      let z' (k : Fin N) : E :=
        if h : ∃ t : τ, emb t = k then z (Classical.choose h) else s₀
      refine ⟨(c', z'), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro k
        refine Finset.sum_nonneg fun t _ => ?_
        split_ifs
        · exact le_of_lt (hw_pos t)
        · exact le_rfl
      · dsimp [c']
        rw [Finset.sum_comm]
        simp [hw_sum]
      · intro k _
        dsimp [z']
        split_ifs with h
        · exact hz_sub ⟨Classical.choose h, rfl⟩
        · exact hs₀
      · dsimp [Φ, c']
        simp_rw [Finset.sum_smul]
        rw [Finset.sum_comm]
        have h_term : ∀ t : τ,
            (∑ k : Fin N, (if emb t = k then w t else 0) • z' k) = w t • z t := by
          intro t
          rw [Finset.sum_eq_single (emb t)]
          · simp only [↓reduceIte]
            congr 1
            dsimp [z']
            have hex : ∃ t' : τ, emb t' = emb t := ⟨t, rfl⟩
            rw [dif_pos hex]
            have h_eq_t : Classical.choose hex = t :=
              hemb_inj (Classical.choose_spec hex)
            rw [h_eq_t]
          · intro k _ hk
            simp [Ne.symm hk]
          · intro hmem
            exact False.elim (hmem (Finset.mem_univ _))
        simp_rw [h_term]
        exact hw_comb
    · rintro x ⟨⟨c, z⟩, ⟨⟨hc_nonneg, hc_sum⟩, hz_mem⟩, rfl⟩
      exact (convex_convexHull ℝ S).sum_mem (fun k _ => hc_nonneg k) hc_sum
        (fun k _ => subset_convexHull ℝ S (hz_mem k (Set.mem_univ k)))
  rw [h_eq]
  exact h_compact_dom.image hΦ_cont

/-! ### Part 6: Strong Duality via Convex Hull Separation -/

lemma sq_le_imp_mem_Icc {x R : ℝ} (hR : 0 ≤ R) (h : x ^ 2 ≤ R) :
    x ∈ Set.Icc (-(R + 1)) (R + 1) := by
  have h1 : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
  have h2 : 0 ≤ (x + 1) ^ 2 := sq_nonneg (x + 1)
  constructor <;> nlinarith

omit [DecidableEq ι] in
lemma bipartite_opNorm_le_one {D : Finset (ι → Bool)} (f : (ι → Bool) → Bool)
    (q : D → ℝ) (hq : ∀ z : D, 0 < q z) (B : D → D → ℝ) (i₀ : ι)
    (hquad : ∀ a : D → ℝ,
      ∑ x : D, ∑ y : D,
        (if f x = false ∧ f y = true ∧ (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀ then B x y else 0) *
          a x * a y ≤ ∑ z : D, q z * (a z) ^ 2) :
    let Γ : Matrix D D ℝ := Matrix.of fun x y =>
      if f x = false ∧ f y = true then
        B x y / (2 * (Real.sqrt (q x) * Real.sqrt (q y)))
      else if f x = true ∧ f y = false then
        B y x / (2 * (Real.sqrt (q x) * Real.sqrt (q y)))
      else 0
    specNorm (maskMatrix Γ i₀) ≤ 1 := by
  intro Γ
  let M : Matrix D D ℝ := maskMatrix Γ i₀
  have hsq_pos : ∀ z : D, 0 < Real.sqrt (q z) := fun z => Real.sqrt_pos.mpr (hq z)
  have hsq_ne : ∀ z : D, Real.sqrt (q z) ≠ 0 := fun z => ne_of_gt (hsq_pos z)
  have hbilin : ∀ u v : D → ℝ,
      ∑ x : D, ∑ y : D, u x * M x y * v y ≤
        ((∑ z : D, u z ^ 2) + (∑ z : D, v z ^ 2)) / 2 := by
    intro u v
    let a₁ (z : D) : ℝ := (if f z then v z else u z) / Real.sqrt (q z)
    let a₂ (z : D) : ℝ := (if f z then u z else v z) / Real.sqrt (q z)
    have hq1 := hquad a₁
    have hq2 := hquad a₂
    have hq2_swap : ∑ x : D, ∑ y : D,
        (if f y = false ∧ f x = true ∧ (y : ι → Bool) i₀ ≠ (x : ι → Bool) i₀ then B y x else 0) *
          a₂ y * a₂ x ≤ ∑ z : D, q z * (a₂ z) ^ 2 := by
      rw [Finset.sum_comm]
      exact hq2
    have h_entry : ∀ x y : D,
        u x * M x y * v y =
          ((if f x = false ∧ f y = true ∧ (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀ then B x y else 0) *
            a₁ x * a₁ y +
           (if f y = false ∧ f x = true ∧ (y : ι → Bool) i₀ ≠ (x : ι → Bool) i₀ then B y x else 0) *
            a₂ y * a₂ x) / 2 := by
      intro x y
      have hsqx := hsq_ne x
      have hsqy := hsq_ne y
      dsimp [M, maskMatrix, Γ, a₁, a₂]
      cases hfx : f x <;> cases hfy : f y
      · simp
      · by_cases hi : (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀
        · simp [hi]
          field_simp [hsqx, hsqy]
        · have hi' : ¬(y : ι → Bool) i₀ ≠ (x : ι → Bool) i₀ := fun h => hi (Ne.symm h)
          simp [hi, hi']
      · by_cases hi : (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀
        · have hi' : (y : ι → Bool) i₀ ≠ (x : ι → Bool) i₀ := Ne.symm hi
          simp [hi, hi']
          field_simp [hsqx, hsqy]
        · have hi' : ¬(y : ι → Bool) i₀ ≠ (x : ι → Bool) i₀ := fun h => hi (Ne.symm h)
          simp [hi, hi']
      · simp
    have h_rhs : ∀ z : D,
        q z * (a₁ z) ^ 2 + q z * (a₂ z) ^ 2 = u z ^ 2 + v z ^ 2 := by
      intro z
      have hqz : Real.sqrt (q z) ^ 2 = q z := Real.sq_sqrt (le_of_lt (hq z))
      have hnez : q z ≠ 0 := ne_of_gt (hq z)
      dsimp [a₁, a₂]
      cases f z
      · simp only [Bool.false_eq_true, ↓reduceIte, div_pow, hqz, mul_div_cancel₀ _ hnez]
      · simp only [↓reduceIte, div_pow, hqz, mul_div_cancel₀ _ hnez]
        ring
    have hsum_lhs : ∑ x : D, ∑ y : D, u x * M x y * v y =
        ((∑ x : D, ∑ y : D,
          (if f x = false ∧ f y = true ∧ (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀ then B x y else 0) *
            a₁ x * a₁ y) +
         (∑ x : D, ∑ y : D,
          (if f y = false ∧ f x = true ∧ (y : ι → Bool) i₀ ≠ (x : ι → Bool) i₀ then B y x else 0) *
            a₂ y * a₂ x)) / 2 := by
      simp_rw [h_entry, ← Finset.sum_div, ← Finset.sum_add_distrib]
    have hsum_rhs : (∑ z : D, q z * (a₁ z) ^ 2) + (∑ z : D, q z * (a₂ z) ^ 2) =
        (∑ z : D, u z ^ 2) + (∑ z : D, v z ^ 2) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => h_rhs z
    linarith
  rw [specNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  let w : EuclideanSpace ℝ D := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) M v
  change ‖w‖ ≤ ‖v‖
  have h1 := hbilin (fun x => ‖v‖ * w x) (fun y => ‖w‖ * v y)
  have h_lhs : ∑ x : D, ∑ y : D, (‖v‖ * w x) * M x y * (‖w‖ * v y) = ‖v‖ * ‖w‖ ^ 3 := by
    have hnorm_sq : ‖w‖ ^ 2 = ∑ x : D, ∑ y : D, w x * M x y * v y := by
      have hw1 : ‖w‖ ^ 2 = inner ℝ w (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := D) M v) := by
        rw [real_inner_self_eq_norm_mul_norm, sq]
      rw [hw1]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
        toEuclideanCLM_apply_ofLp]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => by ring
    calc ∑ x : D, ∑ y : D, (‖v‖ * w x) * M x y * (‖w‖ * v y)
      _ = ‖v‖ * ‖w‖ * ∑ x : D, ∑ y : D, w x * M x y * v y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by ring
      _ = ‖v‖ * ‖w‖ * ‖w‖ ^ 2 := by rw [hnorm_sq]
      _ = ‖v‖ * ‖w‖ ^ 3 := by ring
  have h_rhs : ((∑ z : D, (‖v‖ * w z) ^ 2) + (∑ z : D, (‖w‖ * v z) ^ 2)) / 2 =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    have hw_sq : ∑ z : D, w z ^ 2 = ‖w‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp
    have hv_sq : ∑ z : D, v z ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp
    have h1' : ∑ z : D, (‖v‖ * w z) ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [← hw_sq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => by ring
    have h2' : ∑ z : D, (‖w‖ * v z) ^ 2 = ‖w‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [← hv_sq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => by ring
    rw [h1', h2']
    ring
  rw [h_lhs, h_rhs] at h1
  by_contra hlt
  push Not at hlt
  have hv_pos : 0 < ‖v‖ := by
    by_contra hv0
    have hv_eq : v = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp hv0) (norm_nonneg v))
    have hw_eq : w = 0 := by simp [w, hv_eq]
    rw [hv_eq, hw_eq, norm_zero] at hlt
    exact lt_irrefl 0 hlt
  have hw_pos : 0 < ‖w‖ := lt_trans hv_pos hlt
  have hprod : 0 < ‖v‖ * ‖w‖ ^ 2 * (‖w‖ - ‖v‖) := by positivity
  nlinarith

lemma strong_duality_attainable (f : (ι → Bool) → Bool) (D : Finset (ι → Bool))
    (x₀ y₀ : D) (hx₀ : f x₀ = false) (hy₀ : f y₀ = true) :
    ∃ (d : ℕ) (v : D → ι → EuclideanSpace ℂ (Fin d)),
      0 < d ∧ DualFeasibleChilds f D d v ∧
      advPm f D = (childsDualObjective f D v : ℝ≥0∞) := by
  have : Nonempty D := ⟨x₀⟩
  rcases exists_dualFeasible_of_nonconst f D x₀ with ⟨d_triv, v_triv, _, hfeas_triv⟩
  have h_ne_top : advPm f D ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (advPm_le_dualObjective f D v_triv hfeas_triv)
  have h_pos : 0 < advPm f D := advPm_pos_of_false_true f D x₀ y₀ hx₀ hy₀
  let α : ℝ := (advPm f D).toReal
  have hα_pos : 0 < α := ENNReal.toReal_pos (ne_of_gt h_pos) h_ne_top
  have hα_eq : advPm f D = ENNReal.ofReal α := (ENNReal.ofReal_toReal h_ne_top).symm
  have hcard_pos : (0 : ℝ) < (D.card : ℝ) := by
    have : 0 < D.card := Finset.card_pos.mpr ⟨x₀.1, x₀.2⟩
    exact_mod_cast this
  let R : ℝ := (D.card : ℝ) * α
  have hR_pos : 0 < R := mul_pos hcard_pos hα_pos
  let W := (ι × D) ⊕ D → ℝ
  let E := (D × D) ⊕ D → ℝ
  let box : Set W := Set.pi Set.univ fun _ => Set.Icc (-(R + 1)) (R + 1)
  let K : Set W := box ∩
    {w : W | (∀ z : D, 0 ≤ w (Sum.inr z)) ∧
      ∑ z : D, ((∑ i : ι, w (Sum.inl (i, z)) ^ 2) + w (Sum.inr z)) = R}
  have hK_compact : IsCompact K := by
    refine IsCompact.inter_right (isCompact_univ_pi fun _ => isCompact_Icc) ?_
    refine IsClosed.inter ?_ ?_
    · change IsClosed {w : W | ∀ z : D, 0 ≤ w (Sum.inr z)}
      have h_eq : {w : W | ∀ z : D, 0 ≤ w (Sum.inr z)} =
          ⋂ z : D, {w : W | 0 ≤ w (Sum.inr z)} := by
        ext w; simp
      rw [h_eq]
      exact isClosed_iInter fun z => isClosed_le continuous_const (continuous_apply _)
    · refine isClosed_eq ?_ continuous_const
      refine continuous_finsetSum _ fun z _ => Continuous.add ?_ (continuous_apply _)
      exact continuous_finsetSum _ fun i _ => Continuous.pow (continuous_apply _) 2
  have hw_base_mem : ∀ z₀ : D,
      (Sum.elim 0 (fun z : D => if z = z₀ then R else 0) : W) ∈ K := by
    intro z₀
    refine ⟨?_, ?_, ?_⟩
    · intro idx _
      cases idx with
      | inl _ =>
        dsimp
        constructor <;> linarith
      | inr z =>
        dsimp
        split_ifs <;> (constructor <;> linarith)
    · intro z
      dsimp
      split_ifs <;> linarith
    · simp
  let Ψ (w : W) : E := Sum.elim
    (fun p : D × D =>
      if f p.1 = false ∧ f p.2 = true then
        ∑ i ∈ Finset.univ.filter (fun i => (p.1 : ι → Bool) i ≠ (p.2 : ι → Bool) i),
          w (Sum.inl (i, p.1)) * w (Sum.inl (i, p.2))
      else 0)
    (fun z : D => (∑ i : ι, w (Sum.inl (i, z)) ^ 2) + w (Sum.inr z))
  have hΨ_cont : Continuous Ψ := by
    refine continuous_pi fun idx => ?_
    cases idx with
    | inl p =>
      dsimp [Ψ]
      split_ifs
      · exact continuous_finsetSum _ fun i _ =>
          Continuous.mul (continuous_apply _) (continuous_apply _)
      · exact continuous_const
    | inr z =>
      dsimp [Ψ]
      refine Continuous.add ?_ (continuous_apply _)
      exact continuous_finsetSum _ fun i _ => Continuous.pow (continuous_apply _) 2
  have hC_closed : IsClosed (convexHull ℝ (Ψ '' K)) :=
    (isCompact_convexHull_of_isCompact (hK_compact.image hΨ_cont)
      ⟨Ψ (Sum.elim 0 (fun z : D => if z = x₀ then R else 0)),
       Sum.elim 0 (fun z : D => if z = x₀ then R else 0), hw_base_mem x₀, rfl⟩).isClosed
  let p₀ : E := Sum.elim
    (fun p : D × D => if f p.1 = false ∧ f p.2 = true then 1 else 0)
    (fun _ : D => α)
  have hp₀_mem : p₀ ∈ convexHull ℝ (Ψ '' K) := by
    by_contra hp₀
    rcases geometric_hahn_banach_point_closed (convex_convexHull ℝ (Ψ '' K)) hC_closed hp₀ with
      ⟨L, u, hL_lt, hu_lt⟩
    let B (x y : D) : ℝ := -L (Pi.single (Sum.inl (x, y)) 1)
    let q₀ (z : D) : ℝ := L (Pi.single (Sum.inr z) 1)
    let q (z : D) : ℝ := q₀ z - u / R
    have hL_eval : ∀ p : E, ∑ z : D, p (Sum.inr z) = R →
        (∑ x : D, ∑ y : D, B x y * p (Sum.inl (x, y))) -
          (∑ z : D, q z * p (Sum.inr z)) = u - L p := by
      intro p hp_sum
      have hp_decomp : p = ∑ idx : (D × D) ⊕ D, p idx • Pi.single idx 1 := by
        ext idx
        simp [Finset.sum_apply, Pi.single_apply]
      have hL_p : L p = (∑ x : D, ∑ y : D, (-B x y) * p (Sum.inl (x, y))) +
          (∑ z : D, q₀ z * p (Sum.inr z)) := by
        conv_lhs => rw [hp_decomp]
        rw [map_sum, Fintype.sum_sum_type, Fintype.sum_prod_type]
        congr 1
        · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          simp only [map_smul, smul_eq_mul, B]
          ring
        · refine Finset.sum_congr rfl fun z _ => ?_
          simp only [map_smul, smul_eq_mul, q₀]
          ring
      have hB_neg : ∑ x : D, ∑ y : D, (-B x y) * p (Sum.inl (x, y)) =
          -(∑ x : D, ∑ y : D, B x y * p (Sum.inl (x, y))) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun y _ => by ring
      have hq_sum : ∑ z : D, q z * p (Sum.inr z) =
          (∑ z : D, q₀ z * p (Sum.inr z)) - u := by
        calc ∑ z : D, q z * p (Sum.inr z)
          _ = ∑ z : D, (q₀ z * p (Sum.inr z) - (u / R) * p (Sum.inr z)) := by
              refine Finset.sum_congr rfl fun z _ => by dsimp [q]; ring
          _ = (∑ z : D, q₀ z * p (Sum.inr z)) - (u / R) * (∑ z : D, p (Sum.inr z)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          _ = (∑ z : D, q₀ z * p (Sum.inr z)) - u := by
              rw [hp_sum, div_mul_cancel₀ u (ne_of_gt hR_pos)]
      linarith
    have hp₀_sum : ∑ z : D, p₀ (Sum.inr z) = R := by
      simp [p₀, R]
    have h_p₀_pos : 0 < (∑ x : D, ∑ y : D, if f x = false ∧ f y = true then B x y else 0) -
        α * ∑ z : D, q z := by
      have h1 := hL_eval p₀ hp₀_sum
      have h2 : ∑ x : D, ∑ y : D, B x y * p₀ (Sum.inl (x, y)) =
          ∑ x : D, ∑ y : D, if f x = false ∧ f y = true then B x y else 0 := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        dsimp [p₀]
        split_ifs <;> ring
      have h3 : ∑ z : D, q z * p₀ (Sum.inr z) = α * ∑ z : D, q z := by
        dsimp [p₀]
        rw [← Finset.sum_mul, mul_comm]
      linarith
    have h_Ψ_neg : ∀ w ∈ K,
        (∑ x : D, ∑ y : D, B x y * Ψ w (Sum.inl (x, y))) -
          (∑ z : D, q z * Ψ w (Sum.inr z)) < 0 := by
      intro w hw
      have hw_mem : Ψ w ∈ convexHull ℝ (Ψ '' K) :=
        subset_convexHull ℝ (Ψ '' K) ⟨w, hw, rfl⟩
      have hlt := hu_lt (Ψ w) hw_mem
      have h1 := hL_eval (Ψ w) hw.2.2
      linarith
    have hq_pos : ∀ z₀ : D, 0 < q z₀ := by
      intro z₀
      let w : W := Sum.elim 0 (fun z : D => if z = z₀ then R else 0)
      have hw_K : w ∈ K := hw_base_mem z₀
      have hneg := h_Ψ_neg w hw_K
      have h1 : ∑ x : D, ∑ y : D, B x y * Ψ w (Sum.inl (x, y)) = 0 := by
        refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
        dsimp [Ψ, w]
        split_ifs <;> simp
      have h2 : ∑ z : D, q z * Ψ w (Sum.inr z) = q z₀ * R := by
        rw [Finset.sum_eq_single z₀]
        · simp [Ψ, w]
        · intro z _ hz
          simp [Ψ, w, hz]
        · intro hz₀
          exact False.elim (hz₀ (Finset.mem_univ z₀))
      rw [h1, h2, zero_sub, neg_lt_zero] at hneg
      exact pos_of_mul_pos_left hneg (le_of_lt hR_pos)
    have hquad : ∀ (i₀ : ι) (a : D → ℝ),
        ∑ x : D, ∑ y : D,
          (if f x = false ∧ f y = true ∧ (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀ then B x y else 0) *
            a x * a y ≤ ∑ z : D, q z * (a z) ^ 2 := by
      intro i₀ a
      by_cases ha : ∀ z : D, a z = 0
      · simp [ha]
      · push Not at ha
        rcases ha with ⟨z₁, hz₁⟩
        let Sa : ℝ := ∑ z : D, (a z) ^ 2
        have hSa_pos : 0 < Sa := Finset.sum_pos' (fun _ _ => sq_nonneg _)
          ⟨z₁, Finset.mem_univ z₁, sq_pos_of_ne_zero hz₁⟩
        let s : ℝ := Real.sqrt (R / Sa)
        have hs_sq : s ^ 2 = R / Sa := Real.sq_sqrt (le_of_lt (div_pos hR_pos hSa_pos))
        have hs_sq_pos : 0 < s ^ 2 := by rw [hs_sq]; exact div_pos hR_pos hSa_pos
        let w : W := Sum.elim (fun p => if p.1 = i₀ then s * a p.2 else 0) 0
        have hw_sum_z : ∀ z : D, ∑ i : ι, w (Sum.inl (i, z)) ^ 2 = s ^ 2 * (a z) ^ 2 := by
          intro z
          rw [Finset.sum_eq_single i₀]
          · simp [w]; ring
          · intro i _ hi
            simp [w, hi]
          · intro hi₀; exact False.elim (hi₀ (Finset.mem_univ i₀))
        have hw_sum_all : ∑ z : D, ((∑ i : ι, w (Sum.inl (i, z)) ^ 2) + w (Sum.inr z)) = R := by
          simp_rw [hw_sum_z]
          dsimp [w]
          simp only [add_zero, ← Finset.mul_sum, hs_sq]
          exact div_mul_cancel₀ R (ne_of_gt hSa_pos)
        have hw_K : w ∈ K := by
          refine ⟨?_, fun _ => le_rfl, hw_sum_all⟩
          intro idx _
          cases idx with
          | inl p =>
            refine sq_le_imp_mem_Icc (le_of_lt hR_pos) ?_
            have hle1 : w (Sum.inl p) ^ 2 ≤ ∑ i : ι, w (Sum.inl (i, p.2)) ^ 2 :=
              Finset.single_le_sum (f := fun i : ι => w (Sum.inl (i, p.2)) ^ 2)
                (fun _ _ => sq_nonneg _) (Finset.mem_univ p.1)
            have hle2 : ∑ i : ι, w (Sum.inl (i, p.2)) ^ 2 ≤
                ∑ z : D, ((∑ i : ι, w (Sum.inl (i, z)) ^ 2) + w (Sum.inr z)) := by
              have : ∑ i : ι, w (Sum.inl (i, p.2)) ^ 2 =
                  (∑ i : ι, w (Sum.inl (i, p.2)) ^ 2) + w (Sum.inr p.2) := by
                dsimp [w]; ring
              rw [this]
              exact Finset.single_le_sum
                (f := fun z : D => (∑ i : ι, w (Sum.inl (i, z)) ^ 2) + w (Sum.inr z))
                (fun z _ => add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) le_rfl)
                (Finset.mem_univ p.2)
            exact le_trans hle1 (hle2.trans (le_of_eq hw_sum_all))
          | inr z =>
            dsimp [w]
            constructor <;> linarith
        have hneg := h_Ψ_neg w hw_K
        have h_lhs : ∑ x : D, ∑ y : D, B x y * Ψ w (Sum.inl (x, y)) =
            s ^ 2 * ∑ x : D, ∑ y : D,
              (if f x = false ∧ f y = true ∧ (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀ then B x y else 0) *
                a x * a y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          dsimp [Ψ, w]
          by_cases hxy : f x = false ∧ f y = true
          · rw [if_pos hxy]
            by_cases hi : (x : ι → Bool) i₀ ≠ (y : ι → Bool) i₀
            · rw [if_pos ⟨hxy.1, hxy.2, hi⟩]
              rw [Finset.sum_eq_single i₀]
              · simp only [↓reduceIte]; ring
              · intro i _ hne_i
                simp [hne_i]
              · intro hmem
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
                exact False.elim (hmem hi)
            · rw [if_neg (by tauto)]
              have hzero : ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
                  (if i = i₀ then s * a x else 0) * (if i = i₀ then s * a y else 0) = 0 := by
                refine Finset.sum_eq_zero fun i hi_mem => ?_
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem
                have hne_i : i ≠ i₀ := fun h => hi (h ▸ hi_mem)
                simp [hne_i]
              rw [hzero]
              ring
          · rw [if_neg hxy, if_neg (by tauto)]
            ring
        have h_rhs : ∑ z : D, q z * Ψ w (Sum.inr z) = s ^ 2 * ∑ z : D, q z * (a z) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          dsimp [Ψ]
          rw [hw_sum_z z]
          dsimp [w]
          ring
        rw [h_lhs, h_rhs] at hneg
        nlinarith
    let Γ : Matrix D D ℝ := Matrix.of fun x y =>
      if f x = false ∧ f y = true then
        B x y / (2 * (Real.sqrt (q x) * Real.sqrt (q y)))
      else if f x = true ∧ f y = false then
        B y x / (2 * (Real.sqrt (q x) * Real.sqrt (q y)))
      else 0
    have hΓ_symm : Γ.IsSymm := by
      ext x y
      dsimp [Γ]
      cases hfx : f x <;> cases hfy : f y <;> simp [mul_comm (Real.sqrt (q x)) (Real.sqrt (q y))]
    have hΓ_adv : IsAdversaryMatrix f D Γ := by
      refine ⟨hΓ_symm, fun x y hxy => ?_⟩
      dsimp [Γ]
      cases hfx : f x <;> cases hfy : f y
      · simp
      · rw [hfx, hfy] at hxy; exact False.elim (Bool.false_ne_true hxy)
      · rw [hfx, hfy] at hxy; exact False.elim (Bool.false_ne_true hxy.symm)
      · simp
    have hM_le_one : maxMaskedNorm Γ ≤ 1 := by
      unfold maxMaskedNorm
      by_cases hι : Nonempty ι
      · exact ciSup_le fun i₀ => bipartite_opNorm_le_one f q hq_pos B i₀ (hquad i₀)
      · have : IsEmpty ι := not_nonempty_iff.mp hι
        simp
    let vq (z : D) : ℝ := Real.sqrt (q z)
    have hvq_sq : ∑ z : D, vq z ^ 2 = ∑ z : D, q z := by
      refine Finset.sum_congr rfl fun z _ => Real.sq_sqrt (le_of_lt (hq_pos z))
    have hsum_q_pos : 0 < ∑ z : D, q z :=
      Finset.sum_pos (fun z _ => hq_pos z) ⟨x₀, Finset.mem_univ x₀⟩
    have hΓ_quad : ∑ x : D, ∑ y : D, vq x * Γ x y * vq y =
        ∑ x : D, ∑ y : D, if f x = false ∧ f y = true then B x y else 0 := by
      have h_term : ∀ x y : D, vq x * Γ x y * vq y =
          ((if f x = false ∧ f y = true then B x y else 0) +
           (if f y = false ∧ f x = true then B y x else 0)) / 2 := by
        intro x y
        have hsqx : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hq_pos x))
        have hsqy : Real.sqrt (q y) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hq_pos y))
        dsimp [vq, Γ]
        cases f x <;> cases f y
        · simp
        · simp only [Bool.false_eq_true, and_self, and_false, ↓reduceIte, add_zero]
          field_simp [hsqx, hsqy]
        · simp only [Bool.false_eq_true, and_self, and_false, ↓reduceIte, zero_add]
          field_simp [hsqx, hsqy]
        · simp
      have hsum1 : ∑ x : D, ∑ y : D, vq x * Γ x y * vq y =
          ((∑ x : D, ∑ y : D, if f x = false ∧ f y = true then B x y else 0) +
           (∑ x : D, ∑ y : D, if f y = false ∧ f x = true then B y x else 0)) / 2 := by
        simp_rw [h_term, ← Finset.sum_div, ← Finset.sum_add_distrib]
      have hswap : ∑ x : D, ∑ y : D, (if f y = false ∧ f x = true then B y x else 0) =
          ∑ x : D, ∑ y : D, (if f x = false ∧ f y = true then B x y else 0) :=
        Finset.sum_comm
      rw [hsum1, hswap]
      ring
    have hspec_bound := sum_mul_matrix_mul_le_specNorm Γ vq vq
    rw [hΓ_quad, hvq_sq, mul_assoc, Real.mul_self_sqrt (le_of_lt hsum_q_pos)] at hspec_bound
    have hspec_gt : α < specNorm Γ := by
      nlinarith
    have hΓ_ne : Γ ≠ 0 := by
      intro h0
      have : specNorm Γ = 0 := by
        rw [h0, specNorm_eq_opNorm, map_zero, norm_zero]
      linarith
    have hM_pos : 0 < maxMaskedNorm Γ := maxMaskedNorm_pos_of_ne_zero f D Γ hΓ_adv hΓ_ne
    have hdiv_gt : α < specNorm Γ / maxMaskedNorm Γ := by
      rw [lt_div_iff₀ hM_pos]
      nlinarith
    have hle_adv : ENNReal.ofReal (specNorm Γ / maxMaskedNorm Γ) ≤ advPm f D :=
      le_iSup₂ (f := fun (Γ' : Matrix D D ℝ)
        (_ : IsAdversaryMatrix f D Γ' ∧ Γ' ≠ 0) => ENNReal.ofReal (specNorm Γ' / maxMaskedNorm Γ'))
        Γ ⟨hΓ_adv, hΓ_ne⟩
    rw [hα_eq] at hle_adv
    have hle_real := (ENNReal.ofReal_le_ofReal_iff (le_of_lt hα_pos)).mp hle_adv
    linarith
  rw [mem_convexHull_iff_exists_fintype] at hp₀_mem
  rcases hp₀_mem with ⟨τ, _, c, y_pt, hc_nonneg, hc_sum, hy_mem, hy_comb⟩
  classical
  have h_w : ∀ t : τ, ∃ w ∈ K, Ψ w = y_pt t := fun t => hy_mem t
  choose w hw_K hw_eq using h_w
  have : Nonempty τ := by
    by_contra h_empty
    have : IsEmpty τ := not_nonempty_iff.mp h_empty
    simp at hc_sum
  have eval_sum_smul : ∀ idx : (D × D) ⊕ D,
      (∑ t : τ, c t • y_pt t) idx = ∑ t : τ, c t * y_pt t idx := by
    intro idx
    change (∑ t : τ, c t • y_pt t : (D × D) ⊕ D → ℝ) idx = _
    simp only [Finset.sum_apply]
    rfl
  let u (z : D) (i : ι) (t : τ) : ℝ := Real.sqrt (c t) * w t (Sum.inl (i, z))
  have hfeas : ∀ x y : D, f x = false → f y = true →
      ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
        ∑ t : τ, u x i t * u y i t = 1 := by
    intro x y hfx hfy
    rw [Finset.sum_comm]
    calc ∑ t : τ, ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
          u x i t * u y i t
      _ = ∑ t : τ, c t * Ψ (w t) (Sum.inl (x, y)) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          dsimp [u, Ψ]
          rw [if_pos ⟨hfx, hfy⟩, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hcsq : Real.sqrt (c t) * Real.sqrt (c t) = c t :=
            Real.mul_self_sqrt (hc_nonneg t)
          calc (Real.sqrt (c t) * w t (Sum.inl (i, x))) * (Real.sqrt (c t) * w t (Sum.inl (i, y)))
            _ = (Real.sqrt (c t) * Real.sqrt (c t)) * (w t (Sum.inl (i, x)) * w t (Sum.inl (i, y))) := by ring
            _ = c t * (w t (Sum.inl (i, x)) * w t (Sum.inl (i, y))) := by rw [hcsq]
      _ = (∑ t : τ, c t • y_pt t) (Sum.inl (x, y)) := by
          simp_rw [hw_eq]
          exact (eval_sum_smul (Sum.inl (x, y))).symm
      _ = p₀ (Sum.inl (x, y)) := by rw [hy_comb]
      _ = 1 := by simp [p₀, hfx, hfy]
  have hnorm : ∀ z : D, ∑ i : ι, ∑ t : τ, (u z i t) ^ 2 ≤ α := by
    intro z
    rw [Finset.sum_comm]
    calc ∑ t : τ, ∑ i : ι, (u z i t) ^ 2
      _ = ∑ t : τ, c t * (∑ i : ι, w t (Sum.inl (i, z)) ^ 2) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          dsimp [u]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_pow, Real.sq_sqrt (hc_nonneg t)]
      _ ≤ ∑ t : τ, c t * Ψ (w t) (Sum.inr z) := by
          refine Finset.sum_le_sum fun t _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hc_nonneg t)
          dsimp [Ψ]
          linarith [(hw_K t).2.1 z]
      _ = (∑ t : τ, c t • y_pt t) (Sum.inr z) := by
          simp_rw [hw_eq]
          exact (eval_sum_smul (Sum.inr z)).symm
      _ = p₀ (Sum.inr z) := by rw [hy_comb]
      _ = α := rfl
  rcases dualFeasibleChilds_of_realBipartite f D u α (le_of_lt hα_pos) hfeas hnorm with
    ⟨d, v, hd, hfv, hobj⟩
  refine ⟨d, v, hd, hfv, le_antisymm (advPm_le_dualObjective f D v hfv) ?_⟩
  rw [hα_eq, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hobj

end SolAdversaryDual

open SolAdversaryDual

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool)
    (D : Finset (ι → Bool)) :
    IsLeast {r : ℝ≥0∞ | ∃ (d : ℕ) (v : D → ι → EuclideanSpace ℂ (Fin d)), 0 < d ∧
        DualFeasibleChilds f D d v ∧ r = (childsDualObjective f D v : ℝ≥0∞)}
      (advPm f D) := by
  refine ⟨?_, ?_⟩
  · by_cases hconst : ∀ x y : D, f x = f y
    · have hadv0 : advPm f D = 0 := by
        refine le_antisymm (iSup₂_le fun Γ hΓ => ?_) bot_le
        exfalso
        exact hΓ.2 (Matrix.ext fun x y => hΓ.1.2 x y (hconst x y))
      refine ⟨1, 0, Nat.one_pos, ?_, ?_⟩
      · intro x y _
        rw [if_pos (hconst x y)]
        simp
      · rw [hadv0]
        symm
        simp [childsDualObjective, childsBComplexity]
    · push Not at hconst
      rcases hconst with ⟨x, y, hxy⟩
      cases hfx : f x <;> cases hfy : f y
      · exact False.elim (hxy (hfx.trans hfy.symm))
      · rcases strong_duality_attainable f D x y hfx hfy with ⟨d, v, hd, hfv, heq⟩
        exact ⟨d, v, hd, hfv, heq⟩
      · rcases strong_duality_attainable f D y x hfy hfx with ⟨d, v, hd, hfv, heq⟩
        exact ⟨d, v, hd, hfv, heq⟩
      · exact False.elim (hxy (hfx.trans hfy.symm))
  · rintro r ⟨d, v, _, hfv, rfl⟩
    exact advPm_le_dualObjective f D v hfv
