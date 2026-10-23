-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.no_perfect_majority
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:32:35.964884+00:00
-- url     : https://prove2.me/submissions/63033ec8-cedd-4cb3-b887-84b48cca3c5b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace X7NPM

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P23
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

lemma X7_tp_mul (n : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorPower n A * tensorPower n B = tensorPower n (A * B) := by
  ext x z
  simp only [Matrix.mul_apply, tensorPower]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma X7_tp_one (n : ℕ) : tensorPower n (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext x y
  simp only [tensorPower, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

def X7_tau (K : ℕ) : Fin 3 ⊕ (Fin K × Fin 2) ≃ Fin (3 + K * 2) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def X7_uC {K : ℕ} (y : Fin (3 + K * 2) → Fin 2) (i : Fin 3) : Fin 2 := y (X7_tau K (Sum.inl i))

def X7_vC {K : ℕ} (y : Fin (3 + K * 2) → Fin 2) (t : Fin K) : Fin 2 × Fin 2 :=
  (y (X7_tau K (Sum.inr (t, 0))), y (X7_tau K (Sum.inr (t, 1))))

def X7_E (K : ℕ) : (Fin (3 + K * 2) → Fin 2) ≃ (Fin 3 → Fin 2) × (Fin K → Fin 2 × Fin 2) :=
  (Equiv.arrowCongr (X7_tau K).symm (Equiv.refl _)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _)
        ((Equiv.curry _ _ _).trans (Equiv.arrowCongr (Equiv.refl _) (piFinTwoEquiv fun _ => Fin 2)))))

lemma X7_E_apply {K : ℕ} (y : Fin (3 + K * 2) → Fin 2) : X7_E K y = (X7_uC y, X7_vC y) := by
  rfl

lemma X7_sum {K : ℕ} (F : (Fin 3 → Fin 2) → (Fin K → Fin 2 × Fin 2) → ℂ) :
    ∑ y : Fin (3 + K * 2) → Fin 2, F (X7_uC y) (X7_vC y) = ∑ u, ∑ v, F u v := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (X7_E K) _ _ (fun y => by rw [X7_E_apply])

lemma X7_prod {K : ℕ} {M : Type*} [CommMonoid M] (h : Fin 2 → Fin 2 → M)
    (x y : Fin (3 + K * 2) → Fin 2) :
    ∏ j, h (x j) (y j) = (∏ i, h (X7_uC x i) (X7_uC y i)) *
      ∏ t, (h (X7_vC x t).1 (X7_vC y t).1 * h (X7_vC x t).2 (X7_vC y t).2) := by
  rw [← (X7_tau K).prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp [Fin.prod_univ_two, X7_uC, X7_vC]

lemma X7_sumw {K : ℕ} {M : Type*} [AddCommMonoid M] (h : Fin 2 → M)
    (x : Fin (3 + K * 2) → Fin 2) :
    ∑ j, h (x j) = (∑ i, h (X7_uC x i)) + ∑ t, (h (X7_vC x t).1 + h (X7_vC x t).2) := by
  rw [← (X7_tau K).sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, X7_uC, X7_vC]

def X7_P {K : ℕ} (f : Fin 3 → Fin 2 → ℂ) (g : Fin 2 → Fin 2 → ℂ) :
    (Fin (3 + K * 2) → Fin 2) → ℂ :=
  fun y => (∏ i, f i (X7_uC y i)) * ∏ t, g (X7_vC y t).1 (X7_vC y t).2

lemma X7_tp_P {K : ℕ} (A : Matrix (Fin 2) (Fin 2) ℂ) (f : Fin 3 → Fin 2 → ℂ)
    (g : Fin 2 → Fin 2 → ℂ) :
    (tensorPower (3 + K * 2) A).mulVec (X7_P (K := K) f g) =
      X7_P (fun i a => ∑ b, A a b * f i b) (fun a a' => ∑ b, ∑ b', A a b * A a' b' * g b b') := by
  funext x
  simp only [Matrix.mulVec, dotProduct, tensorPower, X7_P]
  simp_rw [X7_prod (fun a b => A a b) x]
  rw [X7_sum (fun u v => ((∏ i, A (X7_uC x i) (u i)) *
      ∏ t, (A (X7_vC x t).1 (v t).1 * A (X7_vC x t).2 (v t).2)) *
      ((∏ i, f i (u i)) * ∏ t, g (v t).1 (v t).2))]
  have : ∀ u : Fin 3 → Fin 2, ∀ v : Fin K → Fin 2 × Fin 2,
      ((∏ i, A (X7_uC x i) (u i)) *
        ∏ t, (A (X7_vC x t).1 (v t).1 * A (X7_vC x t).2 (v t).2)) *
        ((∏ i, f i (u i)) * ∏ t, g (v t).1 (v t).2) =
      (∏ i, (A (X7_uC x i) (u i) * f i (u i))) *
        ∏ t, (A (X7_vC x t).1 (v t).1 * A (X7_vC x t).2 (v t).2 * g (v t).1 (v t).2) := by
    intro u v
    simp only [Finset.prod_mul_distrib]
    ring
  simp_rw [this, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Fintype.prod_sum (fun i b => A (X7_uC x i) b * f i b),
    ← Fintype.prod_sum (fun t (q : Fin 2 × Fin 2) =>
      A (X7_vC x t).1 q.1 * A (X7_vC x t).2 q.2 * g q.1 q.2)]
  simp_rw [Fintype.sum_prod_type]

lemma X7_P_ne {K : ℕ} {f : Fin 3 → Fin 2 → ℂ} {g : Fin 2 → Fin 2 → ℂ}
    {y : Fin (3 + K * 2) → Fin 2} (h : X7_P f g y ≠ 0) :
    (∀ i, f i (X7_uC y i) ≠ 0) ∧ ∀ t, g (X7_vC y t).1 (X7_vC y t).2 ≠ 0 := by
  simp only [X7_P] at h
  rcases mul_ne_zero_iff.mp h with ⟨h1, h2⟩
  exact ⟨fun i => (Finset.prod_ne_zero_iff.mp h1) i (Finset.mem_univ _),
    fun t => (Finset.prod_ne_zero_iff.mp h2) t (Finset.mem_univ _)⟩

lemma X7_weight {K : ℕ} (y : Fin (3 + K * 2) → Fin 2)
    (hy : ∀ t, (X7_vC y t).1 ≠ (X7_vC y t).2) :
    booleanWordWeight y = (∑ i, if X7_uC y i = 1 then 1 else 0) + K := by
  unfold booleanWordWeight
  rw [Finset.card_filter, X7_sumw (fun a : Fin 2 => if a = 1 then 1 else 0) y]
  congr 1
  have : ∀ t, ((if (X7_vC y t).1 = 1 then 1 else 0) + if (X7_vC y t).2 = 1 then 1 else 0) = 1 := by
    intro t
    have := hy t
    generalize (X7_vC y t).1 = p at this
    generalize (X7_vC y t).2 = q at this
    fin_cases p <;> fin_cases q <;> simp_all
  simp [this]

def X7_sg : Fin 2 → Fin 2 → ℂ := fun p q =>
  if p = 0 ∧ q = 1 then 1 else if p = 1 ∧ q = 0 then -1 else 0

def X7_dl (c : Fin 2) : Fin 2 → ℂ := fun a => if a = c then 1 else 0

def X7_sgn : Fin 2 → ℂ := fun a => if a = 0 then 1 else -1

def X7_phi (K : ℕ) (a b : Fin 2) : (Fin (3 + K * 2) → Fin 2) → ℂ :=
  X7_P ![X7_dl a, X7_dl b, X7_dl 0] X7_sg

def X7_psiP (K : ℕ) : (Fin (3 + K * 2) → Fin 2) → ℂ :=
  X7_P ![fun _ => 1, fun _ => 1, X7_dl 0] X7_sg

def X7_psiM (K : ℕ) : (Fin (3 + K * 2) → Fin 2) → ℂ :=
  X7_P ![X7_sgn, X7_sgn, X7_dl 0] X7_sg

lemma X7_psiP_eq (K : ℕ) : X7_psiP K =
    X7_phi K 0 0 + X7_phi K 0 1 + X7_phi K 1 0 + X7_phi K 1 1 := by
  funext y
  simp only [X7_psiP, X7_phi, X7_P, Fin.prod_univ_three, Pi.add_apply]
  generalize X7_uC y 0 = a
  generalize X7_uC y 1 = b
  fin_cases a <;> fin_cases b <;> simp [X7_dl]

lemma X7_psiM_eq (K : ℕ) : X7_psiM K =
    X7_phi K 0 0 - X7_phi K 0 1 - X7_phi K 1 0 + X7_phi K 1 1 := by
  funext y
  simp only [X7_psiM, X7_phi, X7_P, Fin.prod_univ_three, Pi.add_apply, Pi.sub_apply]
  generalize X7_uC y 0 = a
  generalize X7_uC y 1 = b
  fin_cases a <;> fin_cases b <;> simp [X7_dl, X7_sgn] <;> split_ifs <;> simp

lemma X7_sg_ne {p q : Fin 2} (h : X7_sg p q ≠ 0) : p ≠ q := by
  fin_cases p <;> fin_cases q <;> simp_all [X7_sg]

lemma X7_entry {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix (Fin 2) W ℂ)
    (V : Matrix W W ℂ) (x : W) (a a' : Fin 2) :
    ((A * (V * (Matrix.single x x 1 : Matrix W W ℂ) * Vᴴ) * Aᴴ : Matrix (Fin 2) (Fin 2) ℂ)) a a' =
      (A.mulVec (fun y => V y x)) a * conj ((A.mulVec (fun y => V y x)) a') := by
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
    dotProduct, RCLike.star_def, map_sum, map_mul]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  simp [Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc, ite_and,
    Finset.sum_ite_eq]

lemma X7_entryU (U : Matrix (Fin 2) (Fin 2) ℂ) (b a a' : Fin 2) :
    ((U * (Matrix.single b b 1 : Matrix (Fin 2) (Fin 2) ℂ) * Uᴴ : Matrix (Fin 2) (Fin 2) ℂ)) a a' =
      U a b * conj (U a' b) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]
  fin_cases b <;> simp

lemma X7_q (zb X : Fin 2 → ℂ) :
    ∑ a, ∑ a', zb a * (X a * conj (X a')) * conj (zb a') =
      (∑ a, zb a * X a) * conj (∑ a, zb a * X a) := by
  simp only [Fin.sum_univ_two, map_add, map_mul]
  ring

lemma X7_orth {W : Type*} [Fintype W] [DecidableEq W] {m : ℕ}
    (E : Fin m → Matrix (Fin 2) W ℂ) (V : Matrix W W ℂ) (x : W)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 2) (zb : Fin 2 → ℂ)
    (h : ∑ j, E j * (V * (Matrix.single x x 1 : Matrix W W ℂ) * Vᴴ) * (E j)ᴴ =
      U * (Matrix.single b b 1 : Matrix (Fin 2) (Fin 2) ℂ) * Uᴴ)
    (hz : ∑ a, zb a * U a b = 0) (j : Fin m) :
    ∑ a, zb a * ((E j).mulVec (fun y => V y x)) a = 0 := by
  set w : Fin m → Fin 2 → ℂ := fun j => (E j).mulVec (fun y => V y x) with hw
  set c : Fin m → ℂ := fun j => ∑ a, zb a * w j a with hc
  have e1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      ∑ a, ∑ a', zb a * M a a' * conj (zb a')) h
  simp only [Matrix.sum_apply, X7_entry, X7_entryU] at e1
  rw [X7_q zb (fun a => U a b), hz, zero_mul] at e1
  have key : ∑ j, c j * conj (c j) = 0 := by
    rw [← e1]
    simp only [hc, ← X7_q]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
  have hns : ∀ j, c j * conj (c j) = ((Complex.normSq (c j) : ℝ) : ℂ) := fun j => Complex.mul_conj _
  simp only [hns] at key
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)] at key
  exact Complex.normSq_eq_zero.mp (key j (Finset.mem_univ _))

lemma X7_lin {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix (Fin 2) W ℂ) (V : Matrix W W ℂ) (zb : Fin 2 → ℂ) (c : W → ℂ) :
    ∑ a, zb a * (A.mulVec (V.mulVec c)) a =
      ∑ x, c x * ∑ a, zb a * (A.mulVec (fun y => V y x)) a := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  ring

def X7_s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

lemma X7_s_sq : X7_s * X7_s = 1 / 2 := by
  simp only [X7_s]
  rw [← Complex.ofReal_mul]
  have : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [this]
  push_cast
  ring

def X7_H : Matrix (Fin 2) (Fin 2) ℂ := !![X7_s, X7_s; X7_s, -X7_s]

lemma X7_HH : X7_H * X7_H = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X7_H, Matrix.mul_apply, Fin.sum_univ_two, X7_s_sq] <;> norm_num

lemma X7_H_mem : X7_H ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have : star X7_H = X7_H := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X7_H, X7_s, Matrix.star_apply]
  rw [this, X7_HH]

lemma X7_phi_supp (K : ℕ) (a b : Fin 2) (y : Fin (3 + K * 2) → Fin 2)
    (h : X7_phi K a b y ≠ 0) :
    majority (3 + K * 2) y = if a = 1 ∧ b = 1 then 1 else 0 := by
  obtain ⟨hf, hg⟩ := X7_P_ne h
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  simp only [X7_dl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] at h0 h1 h2
  have hw := X7_weight y (fun t => X7_sg_ne (hg t))
  rw [Fin.sum_univ_three, h0, h1, h2] at hw
  unfold majority
  rw [hw]
  fin_cases a <;> fin_cases b <;> simp <;> omega

lemma X7_g'_ne {p q : Fin 2}
    (h : (∑ b, ∑ b', X7_H p b * X7_H q b' * X7_sg b b') ≠ 0) : p ≠ q := by
  intro hpq
  subst hpq
  apply h
  fin_cases p <;> simp [Fin.sum_univ_two, X7_H, X7_sg] <;> ring

lemma X7_chiP_supp (K : ℕ) (x : Fin (3 + K * 2) → Fin 2)
    (h : ((tensorPower (3 + K * 2) X7_H).mulVec (X7_psiP K)) x ≠ 0) :
    majority (3 + K * 2) x = 0 := by
  rw [X7_psiP, X7_tp_P] at h
  obtain ⟨hf, hg⟩ := X7_P_ne h
  have h0 := hf 0
  have h1 := hf 1
  have e : ∀ c : Fin 2, (∑ b, X7_H c b * (1 : ℂ)) ≠ 0 → c = 0 := by
    intro c hc
    fin_cases c
    · rfl
    · exfalso; apply hc; simp [Fin.sum_univ_two, X7_H]
  have h0' := e _ (by simpa using h0)
  have h1' := e _ (by simpa using h1)
  have hw := X7_weight x (fun t => X7_g'_ne (hg t))
  rw [Fin.sum_univ_three, h0', h1'] at hw
  unfold majority
  rw [hw]
  split_ifs <;> simp at * <;> omega

lemma X7_chiM_supp (K : ℕ) (x : Fin (3 + K * 2) → Fin 2)
    (h : ((tensorPower (3 + K * 2) X7_H).mulVec (X7_psiM K)) x ≠ 0) :
    majority (3 + K * 2) x = 1 := by
  rw [X7_psiM, X7_tp_P] at h
  obtain ⟨hf, hg⟩ := X7_P_ne h
  have h0 := hf 0
  have h1 := hf 1
  have e : ∀ c : Fin 2, (∑ b, X7_H c b * X7_sgn b) ≠ 0 → c = 1 := by
    intro c hc
    fin_cases c
    · exfalso; apply hc; simp [Fin.sum_univ_two, X7_H, X7_sgn]
    · rfl
  have h0' := e _ (by simpa using h0)
  have h1' := e _ (by simpa using h1)
  have hw := X7_weight x (fun t => X7_g'_ne (hg t))
  rw [Fin.sum_univ_three, h0', h1'] at hw
  unfold majority
  rw [hw]
  split_ifs <;> simp at * <;> omega

theorem X7_main (K : ℕ) (Phi : Superop (Word (3 + K * 2) 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hcon : ∀ (x : Word (3 + K * 2) 2) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      Phi (encodedInput U.val x) = targetDensity U.val (majority (3 + K * 2) x)) : False := by
  obtain ⟨m, E, hE, hΦ⟩ := hPhi
  have key : ∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (b : Fin 2) (zb : Fin 2 → ℂ),
      ∑ a, zb a * U.val a b = 0 →
      ∀ c : (Fin (3 + K * 2) → Fin 2) → ℂ, (∀ x, c x ≠ 0 → majority (3 + K * 2) x = b) →
      ∀ j, ∑ a, zb a * ((E j).mulVec ((tensorPower (3 + K * 2) U.val).mulVec c)) a = 0 := by
    intro U b zb hz c hc j
    rw [X7_lin]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hx : c x = 0
    · simp [hx]
    · have h1 := hcon x U
      rw [hΦ, hc x hx] at h1
      simp only [krausApply, encodedInput, conjSuperop, targetDensity] at h1
      rw [X7_orth E (tensorPower _ U.val) x U.val b zb h1 hz j, mul_zero]
  let U1 : Matrix.unitaryGroup (Fin 2) ℂ := 1
  have hU1 : U1.val = 1 := rfl
  let UH : Matrix.unitaryGroup (Fin 2) ℂ := ⟨X7_H, X7_H_mem⟩
  have hUH : UH.val = X7_H := rfl
  have comp : ∀ (a b : Fin 2) (zb : Fin 2 → ℂ),
      ∑ c, zb c * (1 : Matrix (Fin 2) (Fin 2) ℂ) c (if a = 1 ∧ b = 1 then 1 else 0) = 0 →
      ∀ j, ∑ c, zb c * ((E j).mulVec (X7_phi K a b)) c = 0 := by
    intro a b zb hz j
    have := key U1 _ zb (by rw [hU1]; exact hz) (X7_phi K a b) (X7_phi_supp K a b) j
    rwa [hU1, X7_tp_one, Matrix.one_mulVec] at this
  have hzero : ∀ j, (E j).mulVec (X7_phi K 0 0) = 0 := by
    intro j
    have B00 := comp 0 0 ![0, 1] (by simp [Fin.sum_univ_two]) j
    have B01 := comp 0 1 ![0, 1] (by simp [Fin.sum_univ_two]) j
    have B10 := comp 1 0 ![0, 1] (by simp [Fin.sum_univ_two]) j
    have A11 := comp 1 1 ![1, 0] (by simp [Fin.sum_univ_two]) j
    have HP := key UH 0 ![1, -1] (by simp [hUH, Fin.sum_univ_two, X7_H])
      ((tensorPower (3 + K * 2) X7_H).mulVec (X7_psiP K)) (X7_chiP_supp K) j
    have HM := key UH 1 ![1, 1] (by simp [hUH, Fin.sum_univ_two, X7_H])
      ((tensorPower (3 + K * 2) X7_H).mulVec (X7_psiM K)) (X7_chiM_supp K) j
    rw [hUH, Matrix.mulVec_mulVec (X7_psiP K) (tensorPower (3 + K * 2) X7_H)
      (tensorPower (3 + K * 2) X7_H), X7_tp_mul, X7_HH, X7_tp_one, Matrix.one_mulVec,
      X7_psiP_eq] at HP
    rw [hUH, Matrix.mulVec_mulVec (X7_psiM K) (tensorPower (3 + K * 2) X7_H)
      (tensorPower (3 + K * 2) X7_H), X7_tp_mul, X7_HH, X7_tp_one, Matrix.one_mulVec,
      X7_psiM_eq] at HM
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      zero_mul, one_mul, zero_add, add_zero, neg_mul] at B00 B01 B10 A11 HP HM
    funext c
    fin_cases c
    · simp only [Fin.zero_eta, Pi.zero_apply]
      linear_combination (HP + HM) / 2 - A11 + B01 + B10
    · simpa using B00
  have hsum := congrArg (fun M : Matrix (Fin (3 + K * 2) → Fin 2) (Fin (3 + K * 2) → Fin 2) ℂ =>
    M.mulVec (X7_phi K 0 0)) hE
  simp only [Matrix.sum_mulVec, Matrix.one_mulVec] at hsum
  have hz2 : ∀ j, ((E j)ᴴ * E j).mulVec (X7_phi K 0 0) = 0 := by
    intro j
    rw [← Matrix.mulVec_mulVec, hzero j, Matrix.mulVec_zero]
  simp only [hz2, Finset.sum_const_zero] at hsum
  let y0 : Fin (3 + K * 2) → Fin 2 := (X7_E K).symm (fun _ => 0, fun _ => (0, 1))
  have hy : X7_E K y0 = (fun _ => 0, fun _ => (0, 1)) := Equiv.apply_symm_apply _ _
  rw [X7_E_apply] at hy
  have hv := congrFun hsum y0
  simp only [X7_phi, X7_P, Pi.zero_apply] at hv
  rw [(Prod.mk.inj hy).1, (Prod.mk.inj hy).2] at hv
  simp [X7_dl, X7_sg, Fin.prod_univ_three] at hv

end X7NPM

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P23 X7NPM in
open QAlgorithms.Papers.Independent.Information100.P58 (Word) in
open QAlgorithms.Papers.Independent.Information100.P21 (Op) in
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower) in
theorem solution (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n)
    (Phi : Superop (Word n 2) (Fin 2)) (hPhi : IsChannel Phi) :
    ∃ x : Word n 2, ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      Phi (encodedInput U.val x) ≠ targetDensity U.val (majority n x) := by
  refine Classical.byContradiction fun hcon => ?_
  have h2 : ∀ (x : Word n 2) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      Phi (encodedInput U.val x) = targetDensity U.val (majority n x) :=
    fun x U => Classical.byContradiction fun h => hcon ⟨x, U, h⟩
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨K, rfl⟩ : ∃ K, n = 3 + K * 2 := ⟨k - 1, by omega⟩
  exact X7_main K Phi hPhi h2

end
