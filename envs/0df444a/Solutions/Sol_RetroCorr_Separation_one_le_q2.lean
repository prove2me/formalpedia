-- Prove2me | solution 1 for RetroCorr.Separation.one_le_q2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:55:13.579985+00:00
-- url     : https://prove2.me/submissions/35f0ddef-f449-4fba-bb4e-91db60a75828

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel
import Definitions.Def_RetroCorr_Separation_TwoWay

open RetroCorr.Separation MeasureTheory

namespace M14Q2

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

def s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

lemma s_star : (starRingEnd ℂ) s = s := by simp [s]

lemma s_inv_mul : s⁻¹ * s⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, s, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  simp

lemma T_eq (W : Matrix.unitaryGroup (Fin 2) ℂ) (j r r' : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    QAlgorithms.traceLeft (Matrix.kronecker (basisProj W j) (1 : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.of fun ι ι' : Fin 2 × Fin 2 => if r = ι.1 ∧ r' = ι'.1 then (2 : ℂ)⁻¹ * M ι.2 ι'.2 else 0)
      = ((2 : ℂ)⁻¹ * basisProj W j r' r) • M := by
  ext x x'
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_two]
  fin_cases r <;> fin_cases r' <;> fin_cases x <;> simp <;> ring

lemma inner (W : Matrix.unitaryGroup (Fin 2) ℂ) (i j : Fin 2) :
    ∑ r, ∑ r', (W : Matrix (Fin 2) (Fin 2) ℂ) r i * basisProj W j r' r *
      star ((W : Matrix (Fin 2) (Fin 2) ℂ) r' i) = if j = i then 1 else 0 := by
  have hU : star (W : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp W.2
  set M : Matrix (Fin 2) (Fin 2) ℂ := (W : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have h1 : ∀ a b, ∑ r, star (M r a) * M r b = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hU a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  calc _ = (∑ r, star (M r j) * M r i) * (∑ r', star (M r' i) * M r' j) := by
        simp only [basisProj, Matrix.of_apply, Fin.sum_univ_two, ← hM]; ring
    _ = _ := by rw [h1, h1]; split_ifs <;> simp_all

lemma core (W : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) (G : Fin 2 → ℂ) :
    ∑ R, ∑ R', (W : Matrix (Fin 2) (Fin 2) ℂ) R i *
      (∑ j, (2 : ℂ)⁻¹ * basisProj W j R' R * G j) * star ((W : Matrix (Fin 2) (Fin 2) ℂ) R' i)
      = (2 : ℂ)⁻¹ * G i := by
  have h0 := inner W i 0
  have h1 := inner W i 1
  simp only [Fin.sum_univ_two] at h0 h1 ⊢
  fin_cases i <;> simp at h0 h1 ⊢ <;>
    linear_combination (2⁻¹ * G 0) * h0 + (2⁻¹ * G 1) * h1

instance haarProb (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

instance flagProb : IsProbabilityMeasure (flagLaw 2 2) := by
  unfold flagLaw; infer_instance

/-! ### one round -/

section Round

variable {a a'' b b' : ℕ} (eA : Fin a ≃ Fin 2 × Fin a'') (fB : Fin b' ≃ Fin 2 × Fin b)

def eR (a'' : ℕ) : Fin (2 * a'') ≃ Fin 2 × Fin a'' := finProdFinEquiv.symm

def eS (a'' : ℕ) : Fin (2 * a'' * (2 * 2)) ≃ Fin (2 * a'') × (Fin 2 × Fin 2) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

def Jb : Matrix (Fin (2 * a'' * (2 * 2))) (Fin a) ℂ := Matrix.of fun p q =>
  if (eR a'' (eS a'' p).1).1 = (eS a'' p).2.1 ∧ (eS a'' p).2.2 = (eA q).1 ∧
    (eR a'' (eS a'' p).1).2 = (eA q).2 then s⁻¹ else 0

lemma Jb_apply (R C x x0 : Fin 2) (α α0 : Fin a'') :
    Jb eA ((eS a'').symm ((eR a'').symm (R, α), (C, x))) (eA.symm (x0, α0)) =
      if R = C ∧ x = x0 ∧ α = α0 then s⁻¹ else 0 := by
  simp [Jb]

lemma Jb_kraus : QAlgorithms.IsKrausFamily (fun _ : Fin 1 => Jb eA) := by
  unfold QAlgorithms.IsKrausFamily
  rw [Fin.sum_univ_one]
  ext q q'
  rw [← eA.symm_apply_apply q, ← eA.symm_apply_apply q']
  generalize eA q = u
  generalize eA q' = u'
  obtain ⟨x0, α0⟩ := u
  obtain ⟨x0', α0'⟩ := u'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← (eS a'').symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [← (eR a'').symm.sum_comp]
  simp only [Fintype.sum_prod_type, Jb_apply]
  simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  simp [ite_and]
  by_cases h1 : x0' = x0 <;> by_cases h2 : α0' = α0 <;> simp [h1, h2, eq_comm, s_star, s_inv_mul] <;>
    first | exact fun h => h2 h.symm | exact fun h => h1 h.symm | exact fun h => absurd h.symm h1

lemma S1 (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    aliceBranch (b := b) (Jb eA) X = Matrix.of fun u u' =>
      if (eR a'' (eS a'' u.1).1).1 = (eS a'' u.1).2.1 ∧
          (eR a'' (eS a'' u'.1).1).1 = (eS a'' u'.1).2.1 then
        (2 : ℂ)⁻¹ * X (eA.symm ((eS a'' u.1).2.2, (eR a'' (eS a'' u.1).1).2), u.2)
          (eA.symm ((eS a'' u'.1).2.2, (eR a'' (eS a'' u'.1).1).2), u'.2) else 0 := by
  ext ⟨p, β⟩ ⟨p', β'⟩
  rw [← (eS a'').symm_apply_apply p, ← (eS a'').symm_apply_apply p']
  generalize eS a'' p = u
  generalize eS a'' p' = u'
  obtain ⟨P, C, x⟩ := u
  obtain ⟨P', C', x'⟩ := u'
  rw [← (eR a'').symm_apply_apply P, ← (eR a'').symm_apply_apply P']
  generalize eR a'' P = v
  generalize eR a'' P' = v'
  obtain ⟨R, α⟩ := v
  obtain ⟨R', α'⟩ := v'
  simp only [aliceBranch, QAlgorithms.conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Matrix.of_apply, Equiv.apply_symm_apply]
  simp only [← eA.symm.sum_comp (fun q => _), Fintype.sum_prod_type]
  simp only [Jb_apply]
  by_cases h1 : R = C <;> by_cases h2 : R' = C' <;> simp [h1, h2]
  fin_cases x <;> fin_cases x' <;>
    simp [s_star, apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] <;>
    rw [← s_inv_mul] <;> ring

def Mx (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (α : Fin a'') (p : Fin b') (α' : Fin a'')
    (p' : Fin b') : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun x x' => X (eA.symm (x, α), (fB p).2) (eA.symm (x', α'), (fB p').2)

lemma S2 (k : Flag 2 2) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    sendVia (eS a'') fB (retroBranch 2 2 k) (aliceBranch (b := b) (Jb eA) X) =
      Matrix.of fun u u' => ∑ j, ((2 : ℂ)⁻¹ * basisProj k.1 j (eR a'' u'.1).1 (eR a'' u.1).1) *
        ((k.2 j : Matrix (Fin 2) (Fin 2) ℂ) * Mx eA fB X (eR a'' u.1).2 u.2 (eR a'' u'.1).2 u'.2 *
          (k.2 j : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (fB u.2).1 (fB u'.2).1 := by
  ext ⟨P, p⟩ ⟨P', p'⟩
  rw [S1]
  simp only [sendVia]
  have hY : (Matrix.of fun ι ι' : Fin 2 × Fin 2 =>
      (Matrix.of fun u u' : Fin (2 * a'' * (2 * 2)) × Fin b =>
        if (eR a'' (eS a'' u.1).1).1 = (eS a'' u.1).2.1 ∧
          (eR a'' (eS a'' u'.1).1).1 = (eS a'' u'.1).2.1 then
        (2 : ℂ)⁻¹ * X (eA.symm ((eS a'' u.1).2.2, (eR a'' (eS a'' u.1).1).2), u.2)
          (eA.symm ((eS a'' u'.1).2.2, (eR a'' (eS a'' u'.1).1).2), u'.2) else 0)
        ((eS a'').symm (P, ι), (fB p).2) ((eS a'').symm (P', ι'), (fB p').2)) =
      Matrix.of fun ι ι' : Fin 2 × Fin 2 => if (eR a'' P).1 = ι.1 ∧ (eR a'' P').1 = ι'.1 then
        (2 : ℂ)⁻¹ * Mx eA fB X (eR a'' P).2 p (eR a'' P').2 p' ι.2 ι'.2 else 0 := by
    ext ι ι'
    simp [Mx]
  rw [hY]
  simp only [retroBranch, T_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]

def Eb (a'' : ℕ) (W : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) : Matrix (Fin a'') (Fin (2 * a'')) ℂ :=
  Matrix.of fun α P => if α = (eR a'' P).2 then (W : Matrix (Fin 2) (Fin 2) ℂ) (eR a'' P).1 i else 0

lemma Eb_kraus (W : Matrix.unitaryGroup (Fin 2) ℂ) : QAlgorithms.IsKrausFamily (Eb a'' W) := by
  have hU : (W : Matrix (Fin 2) (Fin 2) ℂ) * star (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp W.2
  unfold QAlgorithms.IsKrausFamily
  ext P P'
  rw [← (eR a'').symm_apply_apply P, ← (eR a'').symm_apply_apply P']
  generalize eR a'' P = u
  generalize eR a'' P' = u'
  obtain ⟨R, α⟩ := u
  obtain ⟨R', α'⟩ := u'
  have := congrFun (congrFun hU R') R
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at this
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Eb, Matrix.of_apply,
    Equiv.apply_symm_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : α' = α
  · subst h
    simp only [if_true, and_true]
    rw [show (∑ x, star ((W : Matrix (Fin 2) (Fin 2) ℂ) R x) * (W : Matrix (Fin 2) (Fin 2) ℂ) R' x)
        = ∑ j, (W : Matrix (Fin 2) (Fin 2) ℂ) R' j * star ((W : Matrix (Fin 2) (Fin 2) ℂ) R j) from
        Finset.sum_congr rfl fun _ _ => mul_comm _ _, this]
    simp [eq_comm]
  · simp [h, Ne.symm h]

lemma S3 (W : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2)
    (G : Fin a'' → Fin b' → Fin a'' → Fin b' → Fin 2 → ℂ) :
    aliceBranch (b := b') (Eb a'' W i) (Matrix.of fun u u' : Fin (2 * a'') × Fin b' =>
      ∑ j, ((2 : ℂ)⁻¹ * basisProj W j (eR a'' u'.1).1 (eR a'' u.1).1) *
        G (eR a'' u.1).2 u.2 (eR a'' u'.1).2 u'.2 j) =
      Matrix.of fun u u' => (2 : ℂ)⁻¹ * G u.1 u.2 u'.1 u'.2 i := by
  ext ⟨α, p⟩ ⟨α', p'⟩
  simp only [aliceBranch, QAlgorithms.conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Matrix.of_apply]
  simp only [← (eR a'').symm.sum_comp (fun q => _), Fintype.sum_prod_type]
  simp only [Eb, Matrix.of_apply, Equiv.apply_symm_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one, star_mul', apply_ite star,
    star_zero, star_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact core W i (fun j => G α p α' p' j)

def Ub (U : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin b') (Fin b') ℂ :=
  Matrix.of fun p p' => if (fB p).2 = (fB p').2 then
    ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (fB p).1 (fB p').1 else 0

lemma Ub_kraus (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    QAlgorithms.IsKrausFamily (fun _ : Fin 1 => Ub fB U) := by
  have hU : (U : Matrix (Fin 2) (Fin 2) ℂ) * star (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  unfold QAlgorithms.IsKrausFamily
  rw [Fin.sum_univ_one]
  ext q q'
  rw [← fB.symm_apply_apply q, ← fB.symm_apply_apply q']
  generalize fB q = u
  generalize fB q' = u'
  obtain ⟨y, β⟩ := u
  obtain ⟨y', β'⟩ := u'
  have := congrFun (congrFun hU y) y'
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← fB.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Ub, Matrix.of_apply, Equiv.apply_symm_apply,
    Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, Matrix.conjTranspose_apply]
  simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true, star_star]
  by_cases h : β = β'
  · subst h
    simp only [if_true, and_true]
    rw [show (∑ x, (U : Matrix (Fin 2) (Fin 2) ℂ) y x * star ((U : Matrix (Fin 2) (Fin 2) ℂ) y' x))
        = ∑ j, (U : Matrix (Fin 2) (Fin 2) ℂ) y j * star ((U : Matrix (Fin 2) (Fin 2) ℂ) y' j) from rfl]
    exact this
  · simp [h, Ne.symm h]

lemma S4 (U : Matrix.unitaryGroup (Fin 2) ℂ) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    bobBranch (a := a'') (Ub fB U) (Matrix.of fun u u' : Fin a'' × Fin b' => (2 : ℂ)⁻¹ *
      ((U : Matrix (Fin 2) (Fin 2) ℂ) * Mx eA fB X u.1 u.2 u'.1 u'.2 *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (fB u.2).1 (fB u'.2).1) =
      Matrix.of fun u u' => (2 : ℂ)⁻¹ * X (eA.symm ((fB u.2).1, u.1), (fB u.2).2)
        (eA.symm ((fB u'.2).1, u'.1), (fB u'.2).2) := by
  have hU : star (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  ext ⟨α, p⟩ ⟨α', p'⟩
  rw [← fB.symm_apply_apply p, ← fB.symm_apply_apply p']
  generalize fB p = u
  generalize fB p' = u'
  obtain ⟨y, β⟩ := u
  obtain ⟨y', β'⟩ := u'
  simp only [bobBranch, QAlgorithms.conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Matrix.of_apply]
  simp only [← fB.symm.sum_comp (fun q => _), Fintype.sum_prod_type]
  simp only [Ub, Matrix.of_apply, Equiv.apply_symm_apply, Mx]
  simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, one_mul, mul_one,
    star_one, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, star_star, Matrix.conjTranspose_apply]
  set M : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun x x' => X (eA.symm (x, α), β) (eA.symm (x', α'), β') with hM
  have key : star (U : Matrix (Fin 2) (Fin 2) ℂ) * ((U : Matrix (Fin 2) (Fin 2) ℂ) * M *
      star (U : Matrix (Fin 2) (Fin 2) ℂ)) * (U : Matrix (Fin 2) (Fin 2) ℂ) = M := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have key' := congrFun (congrFun key y) y'
  simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, hM, Matrix.of_apply] at key'
  simp only [Fin.sum_univ_two]
  linear_combination (2 : ℂ)⁻¹ * key'

def gEq : Fin a'' × Fin b' ≃ Fin a × Fin b where
  toFun u := (eA.symm ((fB u.2).1, u.1), (fB u.2).2)
  invFun v := ((eA v.1).2, fB.symm ((eA v.1).1, v.2))
  left_inv u := by simp
  right_inv v := by simp

variable {m : ℕ}

def roundRun (run' : QAlgorithms.Superop (Fin a'' × Fin b') (QAlgorithms.Qubits m)) :
    QAlgorithms.Superop (Fin a × Fin b) (QAlgorithms.Qubits m) :=
  fun X => ∑ _l : Fin 1, (fun Y => ∫ k, (fun Z => ∑ i, (fun Z' => ∑ _l2 : Fin 1,
      run' (bobBranch (a := a'') (Ub fB (k.2 i)) Z'))
        (aliceBranch (b := b') (Eb a'' k.1 i) Z))
      (sendVia (eS a'') fB (retroBranch 2 2 k) Y) ∂(flagLaw 2 2))
    (aliceBranch (b := b) (Jb eA) X)

lemma roundValid {t : ℕ} (run' : QAlgorithms.Superop (Fin a'' × Fin b') (QAlgorithms.Qubits m))
    (h : Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := t) run') :
    Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := t + 1) (roundRun eA fB run') := by
  have hb : ∀ (k : Flag 2 2) (i : Fin 2), Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := t)
      (fun Z' => ∑ _l2 : Fin 1, run' (bobBranch (a := a'') (Ub fB (k.2 i)) Z')) := fun k i =>
    Adaptive.bob (n := t) (a := a'') (b := b') (h := b') (r := 1) (fun _ => Ub fB (k.2 i))
      (Ub_kraus fB _) (fun _ => run') (fun _ => h)
  have ha : ∀ k : Flag 2 2, Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := t)
      (fun Z => ∑ i, (fun Z' => ∑ _l2 : Fin 1, run' (bobBranch (a := a'') (Ub fB (k.2 i)) Z'))
        (aliceBranch (b := b') (Eb a'' k.1 i) Z)) := fun k =>
    Adaptive.alice (n := t) (a := 2 * a'') (b := b') (h := a'') (r := 2) (Eb a'' k.1) (Eb_kraus k.1)
      (fun i Z' => ∑ _l2 : Fin 1, run' (bobBranch (a := a'') (Ub fB (k.2 i)) Z')) (hb k)
  have hs := Adaptive.send (μ := flagLaw 2 2) (N := retroBranch 2 2) (m := m) (n := t)
      (a := 2 * a'' * (2 * 2)) (a' := 2 * a'') (b := b) (b' := b') (eS a'') fB _ ha
  exact Adaptive.alice (n := t + 1) (a := a) (b := b) (h := 2 * a'' * (2 * 2)) (r := 1)
    (fun _ => Jb eA) (Jb_kraus eA) _ (fun _ => hs)

lemma round_k (run' : QAlgorithms.Superop (Fin a'' × Fin b') (QAlgorithms.Qubits m))
    (τ : QAlgorithms.Qubits m ≃ Fin a'' × Fin b') (hrun : ∀ X, run' X = X.submatrix τ τ)
    (k : Flag 2 2) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    ∑ i, ∑ _l2 : Fin 1, run' (bobBranch (a := a'') (Ub fB (k.2 i))
      (aliceBranch (b := b') (Eb a'' k.1 i)
        (sendVia (eS a'') fB (retroBranch 2 2 k) (aliceBranch (b := b) (Jb eA) X)))) =
      X.submatrix (τ.trans (gEq eA fB)) (τ.trans (gEq eA fB)) := by
  rw [S2]
  have h3 : ∀ i, aliceBranch (b := b') (Eb a'' k.1 i) (Matrix.of fun u u' : Fin (2 * a'') × Fin b' =>
      ∑ j, ((2 : ℂ)⁻¹ * basisProj k.1 j (eR a'' u'.1).1 (eR a'' u.1).1) *
        ((k.2 j : Matrix (Fin 2) (Fin 2) ℂ) * Mx eA fB X (eR a'' u.1).2 u.2 (eR a'' u'.1).2 u'.2 *
          (k.2 j : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (fB u.2).1 (fB u'.2).1) =
      Matrix.of fun u u' : Fin a'' × Fin b' => (2 : ℂ)⁻¹ *
      ((k.2 i : Matrix (Fin 2) (Fin 2) ℂ) * Mx eA fB X u.1 u.2 u'.1 u'.2 *
        (k.2 i : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (fB u.2).1 (fB u'.2).1 := fun i =>
    S3 k.1 i (fun α p α' p' j => ((k.2 j : Matrix (Fin 2) (Fin 2) ℂ) * Mx eA fB X α p α' p' *
          (k.2 j : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (fB p).1 (fB p').1)
  simp only [h3, S4, hrun]
  ext q q'
  simp only [Fin.sum_univ_two, Fin.sum_univ_one, Matrix.add_apply, Matrix.submatrix_apply,
    Matrix.of_apply, Equiv.trans_apply, gEq, Equiv.coe_fn_mk]
  ring

lemma roundSem (run' : QAlgorithms.Superop (Fin a'' × Fin b') (QAlgorithms.Qubits m))
    (τ : QAlgorithms.Qubits m ≃ Fin a'' × Fin b') (hrun : ∀ X, run' X = X.submatrix τ τ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    roundRun eA fB run' X = X.submatrix (τ.trans (gEq eA fB)) (τ.trans (gEq eA fB)) := by
  rw [roundRun, Fin.sum_univ_one]
  simp only [round_k eA fB run' τ hrun]
  simp

end Round


/-! ### relabelling channels -/

def Pm {ι κ : Type*} [DecidableEq ι] (ε : κ ≃ ι) : Matrix κ ι ℂ :=
  Matrix.of fun k i => if ε k = i then 1 else 0

lemma relabel_channel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ε : κ ≃ ι) : QAlgorithms.IsChannel (fun ρ : Matrix ι ι ℂ => ρ.submatrix ε ε) := by
  refine ⟨1, fun _ => Pm ε, ?_, fun ρ => ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [Fin.sum_univ_one]
    ext i i'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Pm, Matrix.of_apply, Matrix.one_apply]
    rw [← ε.symm.sum_comp]
    simp [eq_comm]
  · ext k k'
    simp only [QAlgorithms.krausApply, Fin.sum_univ_one, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Pm, Matrix.of_apply, Matrix.submatrix_apply]
    simp [apply_ite star]

/-! ### induction -/

lemma exists_prot (m : ℕ) : ∀ t b : ℕ, 2 ^ t * b = 2 ^ m →
    ∃ run : QAlgorithms.Superop (Fin (2 ^ t) × Fin b) (QAlgorithms.Qubits m),
    ∃ τ : QAlgorithms.Qubits m ≃ Fin (2 ^ t) × Fin b,
      Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := t) run ∧ ∀ X, run X = X.submatrix τ τ
  | 0, b, h => by
    have hb : Fintype.card (QAlgorithms.Qubits m) = Fintype.card (Fin b) := by
      simp at h; simp [h]
    let τ0 : QAlgorithms.Qubits m ≃ Fin b := Fintype.equivOfCardEq hb
    let u0 : Fin (2 ^ 0) := ⟨0, by simp⟩
    have hu : ∀ u : Fin (2 ^ 0), u = u0 := fun u => Fin.ext (by have := u.2; simp at this; simp [u0, this])
    let τ : QAlgorithms.Qubits m ≃ Fin (2 ^ 0) × Fin b :=
      { toFun := fun q => (u0, τ0 q)
        invFun := fun v => τ0.symm v.2
        left_inv := fun q => by simp
        right_inv := fun v => by
          obtain ⟨u, β⟩ := v
          simp [hu u] }
    refine ⟨fun X => (fun Y : Matrix (Fin b) (Fin b) ℂ => Y.submatrix τ0 τ0) (QAlgorithms.traceLeft X),
      τ, Adaptive.finish _ (relabel_channel τ0), fun X => ?_⟩
    ext q q'
    simp only [QAlgorithms.traceLeft, Matrix.submatrix_apply, Matrix.of_apply]
    rw [Fintype.sum_eq_single u0 (fun u hu' => absurd (hu u) hu')]
    rfl
  | t + 1, b, h => by
    obtain ⟨run', τ, hv, hs⟩ := exists_prot m t (2 * b) (by rw [pow_succ] at h; linarith)
    let eA : Fin (2 ^ (t + 1)) ≃ Fin 2 × Fin (2 ^ t) :=
      Fintype.equivOfCardEq (by simp [pow_succ, mul_comm])
    let fB : Fin (2 * b) ≃ Fin 2 × Fin b := finProdFinEquiv.symm
    exact ⟨roundRun eA fB run', τ.trans (gEq eA fB), roundValid eA fB run' hv,
      roundSem eA fB run' τ hs⟩


lemma exists_code (m : ℕ) : ∃ P : TwoWayCode (flagLaw 2 2) (retroBranch 2 2) m m,
    ∀ ρ, P.output ρ = ρ := by
  obtain ⟨run, τ, hv, hs⟩ := exists_prot m m 1 (by simp)
  let ε : Fin (2 ^ m) ≃ QAlgorithms.Qubits m :=
    (Equiv.prodUnique (Fin (2 ^ m)) (Fin 1)).symm.trans τ.symm
  refine ⟨⟨2 ^ m, fun ρ => ρ.submatrix ε ε, relabel_channel ε, run, hv⟩, fun ρ => ?_⟩
  simp only [TwoWayCode.output, hs]
  ext q q'
  have hq : ∀ q, ε (τ q).1 = q := fun q => by
    simp only [ε, Equiv.trans_apply, Equiv.prodUnique_symm_apply]
    rw [show ((τ q).1, (default : Fin 1)) = τ q from Prod.ext rfl (Subsingleton.elim _ _)]
    simp
  simp only [Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, hq]
  rw [Subsingleton.elim (τ q).2 (τ q').2, Matrix.one_apply_eq, mul_one]

lemma fidelity_one {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) (hψ : QAlgorithms.IsState ψ) :
    QAlgorithms.effectProb (QAlgorithms.pureDensity ψ) (QAlgorithms.pureDensity ψ) = 1 := by
  have h1 : ∑ a, ψ a * conj (ψ a) = 1 := by
    have h2 := EuclideanSpace.norm_sq_eq ψ
    rw [show ‖ψ‖ = 1 from hψ] at h2
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← Complex.ofReal_sum, ← h2]
    simp
  have h3 : (QAlgorithms.pureDensity ψ * QAlgorithms.pureDensity ψ).trace =
      (∑ a, ψ a * conj (ψ a)) * (∑ b, ψ b * conj (ψ b)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, QAlgorithms.pureDensity, Matrix.of_apply,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [QAlgorithms.effectProb, h3, h1]
  simp

lemma achievable : TwoWayAchievable (flagLaw 2 2) (retroBranch 2 2) 1 := by
  intro η hη
  refine ⟨0, fun n _ => ⟨n, by simp, ?_⟩⟩
  obtain ⟨P, hP⟩ := exists_code n
  refine ⟨P, fun ψ hψ => ?_⟩
  rw [hP, fidelity_one ψ hψ]
  linarith

end

end M14Q2

theorem solution :
    1 ≤ twoWayQuantumCapacity (flagLaw 2 2) (retroBranch 2 2) :=
  le_sSup ⟨1, zero_le_one, M14Q2.achievable, by simp⟩
