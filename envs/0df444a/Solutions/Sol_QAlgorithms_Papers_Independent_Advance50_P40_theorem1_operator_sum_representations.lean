-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P40.theorem1_operator_sum_representations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:26:06.254991+00:00
-- url     : https://prove2.me/submissions/542031ea-b8cb-4be9-b698-11b1b78c225a

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

theorem s110_87_reindex {n m : ℕ} {ι : Type} [Fintype ι]
    (Phi : SystemMatrix n → SystemMatrix m) (E Eright : ι → Matrix (Fin m) (Fin n) ℂ)
    (h : ∀ X, Phi X = ∑ a, E a * X * (Eright a).conjTranspose) :
    ∃ (r : ℕ) (E Eright : Fin r → Matrix (Fin m) (Fin n) ℂ),
        ∀ X, Phi X = ∑ a, E a * X * (Eright a).conjTranspose := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun a => E (e.symm a), fun a => Eright (e.symm a), fun X => ?_⟩
  rw [h X]
  exact (Fintype.sum_equiv e _ _ (fun a => by simp)).trans rfl

theorem s110_87_reindex2 {n m : ℕ} {ι : Type} [Fintype ι]
    (Phi : SystemMatrix n → SystemMatrix m) (c : ι → ℝ) (E : ι → Matrix (Fin m) (Fin n) ℂ)
    (h : ∀ X, Phi X = ∑ a, (c a : ℂ) • (E a * X * (E a).conjTranspose)) :
    ∃ (r : ℕ) (c : Fin r → ℝ) (E : Fin r → Matrix (Fin m) (Fin n) ℂ),
          ∀ X, Phi X = ∑ a, (c a : ℂ) • (E a * X * (E a).conjTranspose) := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun a => c (e.symm a), fun a => E (e.symm a), fun X => ?_⟩
  rw [h X]
  exact (Fintype.sum_equiv e _ _ (fun a => by simp)).trans rfl

theorem s110_87_fwd {n m : ℕ} (L : SystemMatrix n →ₗ[ℂ] SystemMatrix m) :
    ∃ (r : ℕ) (E Eright : Fin r → Matrix (Fin m) (Fin n) ℂ),
        ∀ X, L X = ∑ a, E a * X * (Eright a).conjTranspose := by
  classical
  apply s110_87_reindex (ι := Fin m × Fin n × Fin n × Fin m) (fun X => L X)
    (fun t => Matrix.single t.1 t.2.1 (L (Matrix.single t.2.1 t.2.2.1 1) t.1 t.2.2.2))
    (fun t => Matrix.single t.2.2.2 t.2.2.1 1)
  intro X
  have hX : X = ∑ k : Fin n, ∑ l : Fin n, X k l • Matrix.single k l (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, Matrix.conjTranspose_single, star_one,
    Matrix.single_mul_mul_single, mul_one]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq', ite_and, mul_comm]

end QAlgorithms.Papers.Independent.Advance50.P40

open QAlgorithms.Papers.Independent.Advance50.P40

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (Phi : SystemMatrix n → SystemMatrix m) :
    ((∃ L : SystemMatrix n →ₗ[ℂ] SystemMatrix m, ∀ X, L X = Phi X) ↔
      ∃ (r : ℕ) (E Eright : Fin r → Matrix (Fin m) (Fin n) ℂ),
        ∀ X, Phi X = ∑ a, E a * X * (Eright a).conjTranspose) ∧
    ((∃ L : SystemMatrix n →ₗ[ℂ] SystemMatrix m, ∀ X, L X = Phi X) →
      ((∀ X, X.IsHermitian → (Phi X).IsHermitian) ↔
        ∃ (r : ℕ) (c : Fin r → ℝ) (E : Fin r → Matrix (Fin m) (Fin n) ℂ),
          ∀ X, Phi X = ∑ a, (c a : ℂ) • (E a * X * (E a).conjTranspose))) := by
  refine ⟨⟨fun ⟨L, hL⟩ => ?_, fun ⟨r, E, Er, h⟩ => ?_⟩, fun ⟨L, hL⟩ => ⟨fun hH => ?_, fun ⟨r, c, E, h⟩ => ?_⟩⟩
  · obtain ⟨r, E, Er, h⟩ := s110_87_fwd L
    exact ⟨r, E, Er, fun X => (hL X).symm.trans (h X)⟩
  · refine ⟨{ toFun := fun X => ∑ a, E a * X * (Er a).conjTranspose,
               map_add' := ?_, map_smul' := ?_ }, fun X => (h X).symm⟩
    · intro X Y
      simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
    · intro c X
      simp [Finset.smul_sum]
  · obtain ⟨r, A, B, h⟩ := s110_87_fwd L
    have hstar : ∀ X, Phi X.conjTranspose = (Phi X).conjTranspose := by
      intro X
      set H : SystemMatrix n := (1/2 : ℂ) • (X + X.conjTranspose) with hHdef
      set K : SystemMatrix n := (-Complex.I/2 : ℂ) • (X - X.conjTranspose) with hKdef
      have hHh : H.IsHermitian := by
        show H.conjTranspose = H
        simp only [hHdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
          Matrix.conjTranspose_conjTranspose]
        rw [add_comm]; congr 1; simp
      have hKh : K.IsHermitian := by
        show K.conjTranspose = K
        simp only [hKdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
          Matrix.conjTranspose_conjTranspose]
        have : star (-Complex.I / 2) = -(-Complex.I/2) := by
          simp [Complex.ext_iff]; norm_num
        rw [this, neg_smul, ← smul_neg, neg_sub]
      have e1 : X = H + Complex.I • K := by
        simp only [hHdef, hKdef, smul_smul]
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        ring_nf; simp [Complex.I_sq]; ring
      have e2 : X.conjTranspose = H - Complex.I • K := by
        simp only [hHdef, hKdef, smul_smul]
        ext i j
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring_nf; simp [Complex.I_sq]; ring
      clear_value H K
      have hLH : (L H).conjTranspose = L H := by rw [hL]; exact hH H hHh
      have hLK : (L K).conjTranspose = L K := by rw [hL]; exact hH K hKh
      rw [← hL, ← hL, e2, e1, map_sub, map_add, map_smul,
        Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hLH, hLK]
      simp [sub_eq_add_neg]
    have hsym : ∀ X, Phi X = ∑ a, B a * X * (A a).conjTranspose := by
      intro X
      rw [← Matrix.conjTranspose_conjTranspose (Phi X), ← hstar, ← hL, h]
      simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have h1 : ∀ X, Phi X = ∑ a, A a * X * (B a).conjTranspose := fun X => (hL X).symm.trans (h X)
    apply s110_87_reindex2 (ι := Fin r ⊕ Fin r) Phi
      (Sum.elim (fun _ => 1/4) (fun _ => -1/4)) (Sum.elim (fun a => A a + B a) (fun a => A a - B a))
    intro X
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib]
    have key : ∀ a, (((1/4:ℝ)):ℂ) • ((A a + B a) * X * (A a + B a).conjTranspose) +
        (((-1/4:ℝ)):ℂ) • ((A a - B a) * X * (A a - B a).conjTranspose) =
        (1/2:ℂ) • (A a * X * (B a).conjTranspose + B a * X * (A a).conjTranspose) := by
      intro a
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.add_mul,
        Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
      push_cast
      module
    simp_rw [key]
    rw [← Finset.smul_sum, Finset.sum_add_distrib, ← h1, ← hsym, ← two_smul ℂ, smul_smul]
    norm_num
  · intro X hX
    show (Phi X).conjTranspose = Phi X
    rw [h X]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      hX.eq, Matrix.mul_assoc]

end
