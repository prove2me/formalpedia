-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P05.random_unitary_choi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:59:17.643385+00:00
-- url     : https://prove2.me/submissions/0f940824-a714-417c-8f1b-19da7c4cb96f

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

lemma X7V_uu {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (U : Matrix J I ℂ) (h : UnitaryBetween U) (i j : J) :
    ∑ k, U i k * conj (U j k) = if i = j then 1 else 0 := by
  have := congrFun (congrFun h.2 i) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
  simpa [RCLike.star_def] using this

lemma X7V_uu' {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (U : Matrix J I ℂ) (h : UnitaryBetween U) (i j : I) :
    ∑ k, U k i * conj (U k j) = if i = j then 1 else 0 := by
  have := congrFun (congrFun h.1 j) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
  rw [show (if i = j then (1:ℂ) else 0) = if j = i then 1 else 0 by simp [eq_comm], ← this]
  simp only [RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma X7V_sand_apply {A B : System} (P : Matrix (In A) (In B) ℂ)
    (Q : Matrix (Out B) (Out A) ℂ) (X : Mat (ChoiRegister A)) (b b' : ChoiRegister B) :
    sandwich P Q X b b' = ∑ a, ∑ a', (P a.1 b.1 * Q b.2 a.2) * X a a' *
      conj (P a'.1 b'.1 * Q b'.2 a'.2) := by
  let W : Matrix (ChoiRegister B) (ChoiRegister A) ℂ := Matrix.of fun b a => P a.1 b.1 * Q b.2 a.2
  show (W * X * Wᴴ) b b' = _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.of_apply, Finset.sum_mul,
    RCLike.star_def]
  rw [Finset.sum_comm]

lemma X7V_superChoi {A B : System} (T : Supermap A B) (D : RandomUnitaryData A B)
    (hD : ∀ X, T X = ∑ x, (D.weight x : ℂ) • sandwich (D.pre x) (D.post x) X)
    (p q : ChoiRegister A × ChoiRegister B) :
    superChoi T p q = ∑ x, (D.weight x : ℂ) *
      ((D.pre x p.1.1 p.2.1 * D.post x p.2.2 p.1.2) *
        conj (D.pre x q.1.1 q.2.1 * D.post x q.2.2 q.1.2)) := by
  simp only [superChoi, hD, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, X7V_sand_apply,
    Matrix.single_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp [ite_and]

lemma X7V_F2 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (w : γ → ℂ) (f : γ → α → ℂ) (g : γ → β → ℂ) :
    ∑ a, ∑ b, ∑ x, w x * (f x a * g x b) = ∑ x, w x * ((∑ a, f x a) * (∑ b, g x b)) := by
  calc ∑ a, ∑ b, ∑ x, w x * (f x a * g x b)
      = ∑ a, ∑ x, ∑ b, w x * (f x a * g x b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ b, w x * (f x a * g x b) := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

lemma X7V_F1 {α γ : Type} [Fintype α] [Fintype γ]
    (w : γ → ℂ) (c : γ → ℂ) (f : γ → α → ℂ) :
    ∑ a, ∑ x, w x * (c x * f x a) = ∑ x, w x * (c x * ∑ a, f x a) := by
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

lemma X7V_F3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (w : γ → ℂ) (c : γ → ℂ) (h : γ → α → β → ℂ) :
    ∑ a, ∑ b, ∑ x, w x * (c x * h x a b) = ∑ x, w x * (c x * ∑ a, ∑ b, h x a b) := by
  calc ∑ a, ∑ b, ∑ x, w x * (c x * h x a b)
      = ∑ a, ∑ x, ∑ b, w x * (c x * h x a b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ b, w x * (c x * h x a b) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

section
variable {A B : System} (T : Supermap A B) (D : RandomUnitaryData A B)
    (hD : ∀ X, T X = ∑ x, (D.weight x : ℂ) • sandwich (D.pre x) (D.post x) X)
include hD

lemma X7V_wsum : ∑ x, (D.weight x : ℂ) = 1 := by
  have := D.weight_sum
  exact_mod_cast this

lemma X7V_jA0B0 (u v : In A × In B) :
    jA0B0 T u v = ∑ x, (D.weight x : ℂ) *
      ((D.pre x u.1 u.2 * conj (D.pre x v.1 v.2)) * (A.output : ℂ)) := by
  simp only [jA0B0, X7V_superChoi T D hD]
  refine Eq.trans (Eq.trans ?_ (X7V_F3 (fun x => (D.weight x : ℂ))
    (fun x => D.pre x u.1 u.2 * conj (D.pre x v.1 v.2))
    (fun x a1 b1 => D.post x b1 a1 * conj (D.post x b1 a1)))) ?_
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    simp only [X7V_uu' (D.post x) (D.post_unitary x), if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma X7V_jA1B1 (u v : Out A × Out B) :
    jA1B1 T u v = ∑ x, (D.weight x : ℂ) *
      ((D.post x u.2 u.1 * conj (D.post x v.2 v.1)) * (A.input : ℂ)) := by
  simp only [jA1B1, X7V_superChoi T D hD]
  refine Eq.trans (Eq.trans ?_ (X7V_F3 (fun x => (D.weight x : ℂ))
    (fun x => D.post x u.2 u.1 * conj (D.post x v.2 v.1))
    (fun x a0 b0 => D.pre x a0 b0 * conj (D.pre x a0 b0)))) ?_
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    simp only [X7V_uu (D.pre x) (D.pre_unitary x), if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma X7V_jA0B1 : jA0B1 T = 1 := by
  ext p q
  simp only [jA0B1, X7V_superChoi T D hD]
  refine Eq.trans (Eq.trans ?_ (X7V_F2 (fun x => (D.weight x : ℂ))
    (fun x a1 => D.post x p.2 a1 * conj (D.post x q.2 a1))
    (fun x b0 => D.pre x p.1 b0 * conj (D.pre x q.1 b0)))) ?_
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  · simp only [X7V_uu (D.post _) (D.post_unitary _), X7V_uu (D.pre _) (D.pre_unitary _)]
    rw [← Finset.sum_mul, X7V_wsum T D hD, one_mul, Matrix.one_apply]
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> simp [h1, h2]

lemma X7V_jA1B0 : jA1B0 T = 1 := by
  ext p q
  simp only [jA1B0, X7V_superChoi T D hD]
  refine Eq.trans (Eq.trans ?_ (X7V_F2 (fun x => (D.weight x : ℂ))
    (fun x a0 => D.pre x a0 p.2 * conj (D.pre x a0 q.2))
    (fun x b1 => D.post x b1 p.1 * conj (D.post x b1 q.1)))) ?_
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  · simp only [X7V_uu' (D.post _) (D.post_unitary _), X7V_uu' (D.pre _) (D.pre_unitary _)]
    rw [← Finset.sum_mul, X7V_wsum T D hD, one_mul, Matrix.one_apply]
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> simp [h1, h2]

lemma X7V_jAB0 : jAB0 T = (fun p q => jA0B0 T (p.1.1, p.2) (q.1.1, q.2) *
      uniformDensity (Out A) p.1.2 q.1.2) := by
  funext p q
  simp only [jAB0, X7V_superChoi T D hD, X7V_jA0B0 T D hD]
  refine Eq.trans (Eq.trans ?_ (X7V_F1 (fun x => (D.weight x : ℂ))
    (fun x => D.pre x p.1.1 p.2 * conj (D.pre x q.1.1 q.2))
    (fun x b1 => D.post x b1 p.1.2 * conj (D.post x b1 q.1.2)))) ?_
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  · have hA : (A.output : ℂ) ≠ 0 := by exact_mod_cast A.output_pos.ne'
    simp only [X7V_uu' (D.post _) (D.post_unitary _), uniformDensity, Matrix.smul_apply,
      Matrix.one_apply, Fintype.card_fin, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> field_simp

lemma X7V_unifFact (hout : A.output = B.output) : UniformFactorization T := by
  unfold UniformFactorization
  funext p q
  simp only [jA0B, X7V_superChoi T D hD, X7V_jA0B0 T D hD]
  refine Eq.trans (Eq.trans ?_ (X7V_F1 (fun x => (D.weight x : ℂ))
    (fun x => D.pre x p.1 p.2.1 * conj (D.pre x q.1 q.2.1))
    (fun x a1 => D.post x p.2.2 a1 * conj (D.post x q.2.2 a1)))) ?_
  · refine Finset.sum_congr rfl fun _ _ => ?_
    refine Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  · have hA : (A.output : ℂ) ≠ 0 := by exact_mod_cast A.output_pos.ne'
    simp only [X7V_uu (D.post _) (D.post_unitary _), uniformDensity, Matrix.smul_apply,
      Matrix.one_apply, Fintype.card_fin, smul_eq_mul, Finset.sum_mul, ← hout]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> field_simp

lemma X7V_unitalFact : UnitalFactorization T := by
  unfold UnitalFactorization
  funext p q
  simp only [jAB1, X7V_superChoi T D hD, X7V_jA1B1 T D hD]
  refine Eq.trans (Eq.trans ?_ (X7V_F1 (fun x => (D.weight x : ℂ))
    (fun x => D.post x p.2 p.1.2 * conj (D.post x q.2 q.1.2))
    (fun x b0 => D.pre x p.1.1 b0 * conj (D.pre x q.1.1 b0)))) ?_
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  · have hA : (A.input : ℂ) ≠ 0 := by exact_mod_cast A.input_pos.ne'
    simp only [X7V_uu (D.pre _) (D.pre_unitary _), uniformDensity, Matrix.smul_apply,
      Matrix.one_apply, Fintype.card_fin, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> field_simp

lemma X7V_otherRandom (hin : A.input = B.input) : OtherRandomMarginal T := by
  unfold OtherRandomMarginal
  funext p q
  simp only [jA1B, X7V_superChoi T D hD, X7V_jA1B1 T D hD]
  refine Eq.trans (Eq.trans ?_ (X7V_F1 (fun x => (D.weight x : ℂ))
    (fun x => D.post x p.2.2 p.1 * conj (D.post x q.2.2 q.1))
    (fun x a0 => D.pre x a0 p.2.1 * conj (D.pre x a0 q.2.1)))) ?_
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  · have hA : (A.input : ℂ) ≠ 0 := by exact_mod_cast A.input_pos.ne'
    simp only [X7V_uu' (D.pre _) (D.pre_unitary _), uniformDensity, Matrix.smul_apply,
      Matrix.one_apply, Fintype.card_fin, smul_eq_mul, Finset.mul_sum, ← hin]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> field_simp

lemma X7V_psd : (superChoi T).PosSemidef := by
  have e : superChoi T = ∑ x, (D.weight x : ℂ) • Matrix.vecMulVec
      (fun p : ChoiRegister A × ChoiRegister B => D.pre x p.1.1 p.2.1 * D.post x p.2.2 p.1.2)
      (star (fun p : ChoiRegister A × ChoiRegister B => D.pre x p.1.1 p.2.1 * D.post x p.2.2 p.1.2)) := by
    ext p q
    rw [X7V_superChoi T D hD, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Matrix.vecMulVec_apply, Pi.star_apply]
  rw [e]
  refine Matrix.posSemidef_sum _ fun x _ => ?_
  refine (Matrix.posSemidef_vecMulVec_self_star _).smul ?_
  exact_mod_cast D.weight_nonneg x

end

end QAlgorithms.Papers.Independent.Dependency50.P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P05 in
theorem solution {A B : System} (hin : A.input = B.input)
    (hout : A.output = B.output) (T : Supermap A B) (hT : IsRandomUnitary T) :
    (∃ D : RandomUnitaryData A B,
      (∀ X, T X = ∑ x, (D.weight x : ℂ) • sandwich (D.pre x) (D.post x) X) ∧
      superChoi T = (fun p q => ∑ x, (D.weight x : ℂ) *
        ketProjector (preUnitaryKet (D.pre x)) (p.1.1, p.2.1) (q.1.1, q.2.1) *
        ketProjector (postUnitaryKet (D.post x)) (p.1.2, p.2.2) (q.1.2, q.2.2))) ∧
    OtherRandomMarginal T ∧ UnitalFactorization T ∧ UniformFactorization T ∧
    StandardMarginals T ∧ jA0B1 T = 1 := by
  obtain ⟨D, hD⟩ := hT
  refine ⟨⟨D, hD, ?_⟩, X7V_otherRandom T D hD hin, X7V_unitalFact T D hD,
    X7V_unifFact T D hD hout, ⟨X7V_psd T D hD, X7V_jA1B0 T D hD, X7V_jAB0 T D hD⟩,
    X7V_jA0B1 T D hD⟩
  funext p q
  rw [X7V_superChoi T D hD]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ketProjector, QAlgorithms.pureDensity, preUnitaryKet, postUnitaryKet,
    Matrix.of_apply, map_mul]
  ring

end
