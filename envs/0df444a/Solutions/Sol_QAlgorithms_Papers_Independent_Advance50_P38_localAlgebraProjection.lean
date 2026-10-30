-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.localAlgebraProjection
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:31:20.592582+00:00
-- url     : https://prove2.me/submissions/b711210e-3d16-4744-9f49-eda448ead24d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

lemma sp_apply (a : Fin 3) (i j : Fin 2) : skewPauli a i j =
    if a = 0 then Complex.I * QAlgorithms.pauliX (decide (i.val = 1)) (decide (j.val = 1))
    else if a = 1 then (-Complex.I) * QAlgorithms.pauliY (decide (i.val = 1)) (decide (j.val = 1))
    else Complex.I * QAlgorithms.pauliZ (decide (i.val = 1)) (decide (j.val = 1)) := by
  unfold skewPauli
  split_ifs <;> rfl

lemma sp_tr (a : Fin 3) : ∑ x : Fin 2, skewPauli a x x = 0 := by
  fin_cases a <;> simp [sp_apply, Fin.sum_univ_two, Matrix.diagonal_apply, QAlgorithms.pauliX, QAlgorithms.pauliY,
    QAlgorithms.pauliZ]

lemma sp_ip (a a' : Fin 3) :
    ∑ x : Fin 2, ∑ y : Fin 2, star (skewPauli a x y) * skewPauli a' x y = if a = a' then 2 else 0 := by
  fin_cases a <;> fin_cases a' <;> simp [sp_apply, Fin.sum_univ_two, Matrix.diagonal_apply, QAlgorithms.pauliX,
    QAlgorithms.pauliY, QAlgorithms.pauliZ] <;> norm_num

lemma sum_pi_prod {n : ℕ} (f : Fin n → Fin 2 → ℂ) :
    ∑ x : Fin n → Fin 2, ∏ l, f l (x l) = ∏ l, ∑ a : Fin 2, f l a := by
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ]


lemma sum_pi_prod2 {n : ℕ} (h : Fin n → Fin 2 → Fin 2 → ℂ) :
    ∑ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2, ∏ l, h l (x l) (y l) =
      ∏ l, ∑ b : Fin 2, ∑ c : Fin 2, h l b c := by
  have : ∀ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2, ∏ l, h l (x l) (y l) =
      ∏ l, ∑ c : Fin 2, h l (x l) c := fun x => sum_pi_prod (fun l c => h l (x l) c)
  simp only [this]
  exact sum_pi_prod (fun l b => ∑ c : Fin 2, h l b c)

lemma gen_tr {n : ℕ} (k k' : Fin n) (a a' : Fin 3) :
    Matrix.trace ((localGenerator k a).conjTranspose * localGenerator k' a') =
      if k = k' ∧ a = a' then (2 : ℂ) ^ n else 0 := by
  have step : Matrix.trace ((localGenerator k a).conjTranspose * localGenerator k' a') =
      ∏ l : Fin n, ∑ b : Fin 2, ∑ c : Fin 2,
        star ((if l = k then skewPauli a b c else if b = c then 1 else 0) : ℂ) *
          (if l = k' then skewPauli a' b c else if b = c then 1 else 0) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      localGenerator]
    rw [Finset.sum_comm]
    simp only [star_prod, ← Finset.prod_mul_distrib]
    exact sum_pi_prod2 (fun l b c => star (if l = k then skewPauli a b c else if b = c then 1 else 0) *
      (if l = k' then skewPauli a' b c else if b = c then 1 else 0))
  rw [step]
  have fac : ∀ l : Fin n, (∑ b : Fin 2, ∑ c : Fin 2,
        star ((if l = k then skewPauli a b c else if b = c then 1 else 0) : ℂ) *
          (if l = k' then skewPauli a' b c else if b = c then 1 else 0)) =
      if l = k then (if l = k' then (if a = a' then 2 else 0) else 0)
      else (if l = k' then 0 else 2) := by
    intro l
    by_cases h1 : l = k <;> by_cases h2 : l = k'
    · simp only [if_pos h1, if_pos h2]; exact sp_ip a a'
    · simp only [if_pos h1, if_neg h2]
      have : ∑ b : Fin 2, star (skewPauli a b b) = 0 := by rw [← star_sum, sp_tr, star_zero]
      simpa [mul_ite, Finset.sum_ite_eq] using this
    · simp only [if_neg h1, if_pos h2]
      simpa [ite_mul, Finset.sum_ite_eq, sp_tr] using sp_tr a'
    · simp only [if_neg h1, if_neg h2]
      simp [Fin.sum_univ_two]
  simp only [fac]
  by_cases hk : k = k' ∧ a = a'
  · obtain ⟨rfl, rfl⟩ := hk
    have e : ∀ x : Fin n, (if x = k then (if x = k then (if a = a then (2 : ℂ) else 0) else 0)
        else (if x = k then 0 else 2)) = 2 := by
      intro x; by_cases h : x = k <;> simp [h]
    rw [Finset.prod_congr rfl (fun x _ => e x)]
    simp
  · rw [if_neg hk]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases h : k = k'
    · have : a ≠ a' := fun e => hk ⟨h, e⟩
      simp [h, this]
    · simp [h]


lemma pair_add_right {ι : Type*} [Fintype ι] (A B C : Matrix ι ι ℂ) :
    realHSPairing A (B + C) = realHSPairing A B + realHSPairing A C := by
  unfold realHSPairing; rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

lemma pair_smul_right {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (r : ℝ) :
    realHSPairing A (r • B) = r * realHSPairing A B := by
  unfold realHSPairing; rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]; simp

lemma pair_sub_left {ι : Type*} [Fintype ι] (A B C : Matrix ι ι ℂ) :
    realHSPairing (A - B) C = realHSPairing A C - realHSPairing B C := by
  unfold realHSPairing; rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]

lemma pair_comm {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) : realHSPairing A B = realHSPairing B A := by
  unfold realHSPairing
  have : (A.conjTranspose * B).conjTranspose = B.conjTranspose * A := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [← this, Matrix.trace_conjTranspose]; simp

lemma pair_self_eq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : realHSPairing A A = frobSq A := by
  unfold realHSPairing
  have : Matrix.trace (A.conjTranspose * A) = (frobSq A : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, frobSq]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp
  rw [this]; simp

lemma frobSq_eq_zero' {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (h : frobSq A = 0) : A = 0 := by
  unfold frobSq at h
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun i => ∑ j, Complex.normSq (A i j))
    (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).mp h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun j => Complex.normSq (A i j)) (fun j _ => Complex.normSq_nonneg _)).mp
    (h' i (Finset.mem_univ i)) j (Finset.mem_univ j)
  simpa using h1

def Lf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℝ] ℝ where
  toFun B := realHSPairing A B
  map_add' B C := pair_add_right A B C
  map_smul' r B := by simp only [RingHom.id_apply, smul_eq_mul]; exact pair_smul_right A B r

lemma pair_self_zero {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (h : realHSPairing A A = 0) : A = 0 := by
  rw [pair_self_eq] at h; exact frobSq_eq_zero' A h

lemma uniq {ι : Type*} [Fintype ι] (T : Set (Matrix ι ι ℂ)) (hsub : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ T) (g p q : Matrix ι ι ℂ)
    (hp : IsHSProjection T g p) (hq : IsHSProjection T g q) : p = q := by
  have h1 := hp.2 _ (hsub p hp.1 q hq.1)
  have h2 := hq.2 _ (hsub p hp.1 q hq.1)
  have : realHSPairing (p - q) (p - q) = 0 := by
    have e : p - q = (g - q) - (g - p) := by abel
    have h3 : realHSPairing (p - q) (p - q) = realHSPairing ((g - q) - (g - p)) (p - q) :=
      congrArg (fun x => realHSPairing x (p - q)) e
    rw [h3, pair_sub_left]
    linarith
  exact sub_eq_zero.mp (pair_self_zero _ this)



lemma gkey {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (G : κ → Matrix ι ι ℂ) (N : ℝ) (hN : 0 < N)
    (horth : ∀ i j, realHSPairing (G i) (G j) = if i = j then N else 0) (g : Matrix ι ι ℂ) :
    ∀ h ∈ (Submodule.span ℝ (Set.range G) : Set (Matrix ι ι ℂ)),
      realHSPairing (g - N⁻¹ • ∑ j, realHSPairing g (G j) • G j) h = 0 := by
  intro h hh
  have hh' : h ∈ Submodule.span ℝ (Set.range G) := hh
  rw [Submodule.mem_span_range_iff_exists_fun] at hh'
  obtain ⟨c, rfl⟩ := hh'
  have hb : ∀ i, realHSPairing (G i) (g - N⁻¹ • ∑ j, realHSPairing g (G j) • G j) = 0 := by
    intro i
    have e1 : realHSPairing (G i) (g - N⁻¹ • ∑ j, realHSPairing g (G j) • G j) =
        Lf (G i) g - Lf (G i) (N⁻¹ • ∑ j, realHSPairing g (G j) • G j) := by
      show Lf (G i) (g - _) = _
      exact map_sub (Lf (G i)) g _
    have e2 : Lf (G i) (N⁻¹ • ∑ j, realHSPairing g (G j) • G j) = realHSPairing (G i) g := by
      rw [map_smul, map_sum]
      have : ∀ j, Lf (G i) (realHSPairing g (G j) • G j) =
          realHSPairing g (G j) * (if i = j then N else 0) := by
        intro j
        rw [map_smul, smul_eq_mul, show Lf (G i) (G j) = realHSPairing (G i) (G j) from rfl, horth]
      simp only [this, smul_eq_mul]
      rw [pair_comm (G i) g]
      simp [Finset.sum_ite_eq]
      field_simp
    rw [e1, e2]; show realHSPairing (G i) g - realHSPairing (G i) g = 0; ring
  show Lf (g - N⁻¹ • ∑ j, realHSPairing g (G j) • G j) (Finset.univ.sum fun i => c i • G i) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, smul_eq_mul, show Lf (g - N⁻¹ • ∑ j, realHSPairing g (G j) • G j) (G i) =
    realHSPairing (g - N⁻¹ • ∑ j, realHSPairing g (G j) • G j) (G i) from rfl, pair_comm, hb i, mul_zero]


lemma gen_pair {n : ℕ} (i j : Fin n × Fin 3) :
    realHSPairing (localGenerator i.1 i.2) (localGenerator j.1 j.2) =
      if i = j then (2 : ℝ) ^ n else 0 := by
  unfold realHSPairing
  rw [gen_tr]
  by_cases h : i = j
  · obtain ⟨a, b⟩ := i
    obtain ⟨c, d⟩ := j
    simp only [Prod.mk.injEq] at h
    simp only [h.1, h.2, and_self, if_true, if_pos]
    rw [show ((2 : ℂ) ^ n) = (((2 : ℝ) ^ n : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  · have : ¬ (i.1 = j.1 ∧ i.2 = j.2) := fun e => h (Prod.ext e.1 e.2)
    simp [h, this]

lemma loc_proj {n : ℕ} (hn : 0 < n) (g : Matrix (LocalQubitIndex n) (LocalQubitIndex n) ℂ) :
    IsHSProjection (localAlgebra n : Set _) g (localProjection g) := by
  have hN : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have key := gkey (fun ka : Fin n × Fin 3 => localGenerator ka.1 ka.2) ((2 : ℝ) ^ n) hN
    gen_pair g
  have hp : localProjection g = ((2 : ℝ) ^ n)⁻¹ • ∑ j : Fin n × Fin 3,
      realHSPairing g (localGenerator j.1 j.2) • localGenerator j.1 j.2 := by
    unfold localProjection
    rw [Fintype.sum_prod_type]
  refine ⟨?_, ?_⟩
  · rw [hp]
    show _ ∈ localAlgebra n
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  · rw [hp]; exact key

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38 in
theorem solution {n : ℕ} (hn : 0 < n)
    (g : Matrix (LocalQubitIndex n) (LocalQubitIndex n) ℂ) :
    (∃! p, IsHSProjection (localAlgebra n : Set _) g p) ∧
    IsHSProjection (localAlgebra n : Set _) g (localProjection g) :=
  ⟨⟨_, loc_proj hn g, fun q hq => uniq _
    (fun a ha c hc => Submodule.sub_mem _ ha hc) g q _ hq (loc_proj hn g)⟩, loc_proj hn g⟩
