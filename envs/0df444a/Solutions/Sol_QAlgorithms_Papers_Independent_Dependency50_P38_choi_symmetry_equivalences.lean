-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P38.choi_symmetry_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T17:41:55.182017+00:00
-- url     : https://prove2.me/submissions/16e03328-b500-4851-8158-78cd1fb2458c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P38

set_option autoImplicit false

noncomputable section

namespace P588Aux

open QAlgorithms
open scoped Matrix ComplexConjugate Kronecker

section Generic

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

lemma kraus_add {K : Type*} [Fintype K] (E : K → Matrix O I ℂ) (A B : Matrix I I ℂ) :
    krausApply E (A + B) = krausApply E A + krausApply E B := by
  simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma kraus_smul {K : Type*} [Fintype K] (E : K → Matrix O I ℂ) (c : ℂ) (A : Matrix I I ℂ) :
    krausApply E (c • A) = c • krausApply E A := by
  simp [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

def krausLin {K : Type*} [Fintype K] (E : K → Matrix O I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun := krausApply E
  map_add' := kraus_add E
  map_smul' := kraus_smul E

lemma kraus_expand {K : Type*} [Fintype K] (E : K → Matrix O I ℂ) (A : Matrix I I ℂ) :
    krausApply E A = ∑ i, ∑ j, A i j • krausApply E (Matrix.single i j 1) := by
  have hs : ∀ i j, Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) := by
    intro i j
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have h := congrArg (krausLin E) (Matrix.matrix_eq_sum_single A)
  simp only [hs, map_sum, map_smul] at h
  exact h

lemma kraus_eq_of_choi {K K' : Type*} [Fintype K] [Fintype K'] (E : K → Matrix O I ℂ)
    (F : K' → Matrix O I ℂ)
    (h : QAlgorithms.Papers.Independent.Information100.P34.choi (krausApply E) =
      QAlgorithms.Papers.Independent.Information100.P34.choi (krausApply F))
    (A : Matrix I I ℂ) : krausApply E A = krausApply F A := by
  have hs : ∀ i j, krausApply E (Matrix.single i j 1) = krausApply F (Matrix.single i j 1) := by
    intro i j
    ext b b'
    exact congrFun (congrFun h (i, b)) (j, b')
  rw [kraus_expand E, kraus_expand F]
  simp only [hs]

lemma choi_kraus {K : Type*} [Fintype K] (E : K → Matrix O I ℂ) :
    QAlgorithms.Papers.Independent.Information100.P34.choi (krausApply E) =
      ∑ k, Matrix.vecMulVec (Matrix.vec (E k)) (star (Matrix.vec (E k))) := by
  ext p q
  simp [QAlgorithms.Papers.Independent.Information100.P34.choi, krausApply,
    Matrix.vecMulVec_apply, Matrix.vec, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma mul_vecMulVec_mul {ι : Type*} [Fintype ι] (Z : Matrix ι ι ℂ) (u : ι → ℂ) :
    Z * Matrix.vecMulVec u (star u) * Zᴴ = Matrix.vecMulVec (Z *ᵥ u) (star (Z *ᵥ u)) := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Pi.star_apply, star_sum, star_mul', Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma conj_choi {K : Type*} [Fintype K] (E : K → Matrix O I ℂ) (X : Matrix I I ℂ)
    (Y : Matrix O O ℂ) :
    Matrix.kronecker (X.map (starRingEnd ℂ)) Y *
        QAlgorithms.Papers.Independent.Information100.P34.choi (krausApply E) *
        (Matrix.kronecker (X.map (starRingEnd ℂ)) Y)ᴴ =
      QAlgorithms.Papers.Independent.Information100.P34.choi
        (krausApply (fun k => Y * E k * Xᴴ)) := by
  rw [choi_kraus, choi_kraus, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_vecMulVec_mul]
  have hT : (X.map (starRingEnd ℂ))ᵀ = Xᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h1 : Matrix.kronecker (X.map (starRingEnd ℂ)) Y *ᵥ Matrix.vec (E k) =
      Matrix.vec (Y * E k * Xᴴ) := by
    have := Matrix.kronecker_mulVec_vec Y (E k) (X.map (starRingEnd ℂ))
    rw [hT] at this
    exact this
  rw [h1]

lemma kraus_conj {K : Type*} [Fintype K] (E : K → Matrix O I ℂ) (X : Matrix I I ℂ)
    (Y : Matrix O O ℂ) (A : Matrix I I ℂ) :
    krausApply (fun k => Y * E k * Xᴴ) A = Y * krausApply E (Xᴴ * A * X) * Yᴴ := by
  simp only [krausApply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]

lemma commute_iff_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (Z C : Matrix ι ι ℂ)
    (h1 : Zᴴ * Z = 1) (h2 : Z * Zᴴ = 1) :
    Commute Z C ↔ Z * C * Zᴴ = C := by
  constructor
  · intro h
    rw [h.eq, Matrix.mul_assoc, h2, Matrix.mul_one]
  · intro h
    show Z * C = C * Z
    calc Z * C = Z * C * (Zᴴ * Z) := by rw [h1, Matrix.mul_one]
      _ = (Z * C * Zᴴ) * Z := by simp only [Matrix.mul_assoc]
      _ = C * Z := by rw [h]

lemma kron_unit (X : Matrix I I ℂ) (Y : Matrix O O ℂ) (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1) :
    (Matrix.kronecker (X.map (starRingEnd ℂ)) Y)ᴴ *
      Matrix.kronecker (X.map (starRingEnd ℂ)) Y = 1 := by
  have hc : (X.map (starRingEnd ℂ))ᴴ * X.map (starRingEnd ℂ) = 1 := by
    have e : (X.map (starRingEnd ℂ))ᴴ = (Xᴴ).map (starRingEnd ℂ) := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [e, ← Matrix.map_mul, hX]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hk : (Matrix.kronecker (X.map (starRingEnd ℂ)) Y)ᴴ =
      Matrix.kronecker (X.map (starRingEnd ℂ))ᴴ Yᴴ := by
    ext ⟨a, b⟩ ⟨c, e⟩
    simp [Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [hk]
  show (X.map (starRingEnd ℂ))ᴴ ⊗ₖ Yᴴ * (X.map (starRingEnd ℂ) ⊗ₖ Y) = 1
  rw [← Matrix.mul_kronecker_mul, hc, hY, Matrix.one_kronecker_one]

theorem key (Phi : Superop I O) (hPhi : IsChannel Phi) (X : Matrix I I ℂ) (Y : Matrix O O ℂ)
    (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1) :
    Commute (Matrix.kronecker (X.map (starRingEnd ℂ)) Y)
        (QAlgorithms.Papers.Independent.Information100.P34.choi Phi) ↔
      ∀ A, Y * Phi (Xᴴ * A * X) * Yᴴ = Phi A := by
  obtain ⟨r, E, -, hE⟩ := hPhi
  have hfun : Phi = krausApply E := funext hE
  subst hfun
  have hu := kron_unit X Y hX hY
  rw [commute_iff_conj _ _ hu (mul_eq_one_comm.mp hu), conj_choi]
  constructor
  · intro h A
    rw [← kraus_conj]
    exact kraus_eq_of_choi _ _ h A
  · intro h
    congr 1
    funext A
    rw [kraus_conj, h]

lemma sandwich {ι : Type*} [Fintype ι] [DecidableEq ι] (P A : Matrix ι ι ℂ) (h : P * Pᴴ = 1) :
    P * (Pᴴ * A * P) * Pᴴ = A := by
  calc P * (Pᴴ * A * P) * Pᴴ = (P * Pᴴ) * A * (P * Pᴴ) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [h, Matrix.one_mul, Matrix.mul_one]

end Generic

lemma piKron_conjTranspose {ι : Type*} [Fintype ι] (k : ℕ) (M : Matrix ι ι ℂ) :
    (piKron k M)ᴴ = piKron k Mᴴ := by
  ext x y
  simp [piKron, Matrix.conjTranspose_apply, star_prod]

lemma piKron_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (M N : Matrix ι ι ℂ) :
    piKron k M * piKron k N = piKron k (M * N) := by
  ext x z
  simp only [piKron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [Finset.prod_mul_distrib]

lemma piKron_one {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    piKron k (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc
      exact h (funext fun i => by
        by_contra hi
        exact hc ⟨i, hi⟩)
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma piKron_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (U : Matrix ι ι ℂ)
    (hU : Uᴴ * U = 1) : (piKron k U)ᴴ * piKron k U = 1 := by
  rw [piKron_conjTranspose, piKron_mul, hU, piKron_one]

lemma su_unit (d : ℕ) (U : Matrix.specialUnitaryGroup (Fin d) ℂ) :
    (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * (U : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  rw [Matrix.mem_unitaryGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h

lemma tp_map (d k : ℕ) (s : Equiv.Perm (Fin k)) :
    (Schur.tensorPermutation d k s).map (starRingEnd ℂ) = Schur.tensorPermutation d k s := by
  ext y x
  simp only [Schur.tensorPermutation, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

lemma tp_one (d k : ℕ) : Schur.tensorPermutation d k 1 = 1 := by
  ext y x
  rfl

lemma tp_unit (d k : ℕ) (s : Equiv.Perm (Fin k)) :
    (Schur.tensorPermutation d k s)ᴴ * Schur.tensorPermutation d k s = 1 := by
  have hinj : ∀ x x' : Fin k → Fin d, x ∘ s.symm = x' ∘ s.symm ↔ x = x' := by
    intro x x'
    constructor
    · intro h
      funext i
      simpa using congrFun h (s i)
    · intro h
      rw [h]
  ext x x'
  simp [Schur.tensorPermutation, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    hinj]
  by_cases h : x = x'
  · subst h
    simp
  · simp [h, Ne.symm h]

end P588Aux

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P38 Matrix ComplexConjugate in
theorem solution (d m n : ℕ) (hd : 0 < d)
    (Phi : Superop (Fin m → Fin d) (Fin n → Fin d)) (hPhi : IsChannel Phi) :
    ((∀ (U : Matrix.specialUnitaryGroup (Fin d) ℂ)
        (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ),
        Phi (piKron m (U : Matrix (Fin d) (Fin d) ℂ) * A *
          (piKron m (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) =
        piKron n (U : Matrix (Fin d) (Fin d) ℂ) * Phi A *
          (piKron n (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) ↔
      ∀ U : Matrix.specialUnitaryGroup (Fin d) ℂ,
        Commute
          (Matrix.kronecker
            ((piKron m (U : Matrix (Fin d) (Fin d) ℂ)).map (starRingEnd ℂ))
            (piKron n (U : Matrix (Fin d) (Fin d) ℂ)))
          (QAlgorithms.Papers.Independent.Information100.P34.choi Phi)) ∧
    ((∀ (sigma : Equiv.Perm (Fin m)) (tau : Equiv.Perm (Fin n))
        (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ),
        Phi (Schur.tensorPermutation d m sigma * A *
          (Schur.tensorPermutation d m sigma)ᴴ) = Phi A ∧
        Schur.tensorPermutation d n tau * Phi A *
          (Schur.tensorPermutation d n tau)ᴴ = Phi A) ↔
      ∀ (sigma : Equiv.Perm (Fin m)) (tau : Equiv.Perm (Fin n)),
        Commute
          (Matrix.kronecker
            ((Schur.tensorPermutation d m sigma).map (starRingEnd ℂ))
            (Schur.tensorPermutation d n tau))
          (QAlgorithms.Papers.Independent.Information100.P34.choi Phi)) := by
  constructor
  · constructor
    · intro h U
      have hW := P588Aux.piKron_unit m _ (P588Aux.su_unit d U)
      have hV := P588Aux.piKron_unit n _ (P588Aux.su_unit d U)
      rw [P588Aux.key Phi hPhi _ _ hW hV]
      intro A
      have hW2 := mul_eq_one_comm.mp hW
      have h1 := h U ((piKron m (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * A *
        piKron m (U : Matrix (Fin d) (Fin d) ℂ))
      rw [P588Aux.sandwich _ _ hW2] at h1
      exact h1.symm
    · intro h U A
      have hW := P588Aux.piKron_unit m _ (P588Aux.su_unit d U)
      have hV := P588Aux.piKron_unit n _ (P588Aux.su_unit d U)
      have hW2 := mul_eq_one_comm.mp hW
      have h' := (P588Aux.key Phi hPhi _ _ hW hV).mp (h U)
        (piKron m (U : Matrix (Fin d) (Fin d) ℂ) * A *
          (piKron m (U : Matrix (Fin d) (Fin d) ℂ))ᴴ)
      have hc : (piKron m (U : Matrix (Fin d) (Fin d) ℂ))ᴴ *
          (piKron m (U : Matrix (Fin d) (Fin d) ℂ) * A *
            (piKron m (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) *
          piKron m (U : Matrix (Fin d) (Fin d) ℂ) = A := by
        have := P588Aux.sandwich ((piKron m (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) A
          (by rw [Matrix.conjTranspose_conjTranspose]; exact hW)
        rwa [Matrix.conjTranspose_conjTranspose] at this
      rw [hc] at h'
      exact h'.symm
  · have H : ∀ (sigma : Equiv.Perm (Fin m)) (tau : Equiv.Perm (Fin n)),
        Commute
          (Matrix.kronecker
            ((Schur.tensorPermutation d m sigma).map (starRingEnd ℂ))
            (Schur.tensorPermutation d n tau))
          (QAlgorithms.Papers.Independent.Information100.P34.choi Phi) ↔
        ∀ A, Schur.tensorPermutation d n tau *
            Phi ((Schur.tensorPermutation d m sigma)ᴴ * A * Schur.tensorPermutation d m sigma) *
            (Schur.tensorPermutation d n tau)ᴴ = Phi A := by
      intro sigma tau
      have hk := P588Aux.key Phi hPhi (Schur.tensorPermutation d m sigma)
        (Schur.tensorPermutation d n tau) (P588Aux.tp_unit d m sigma) (P588Aux.tp_unit d n tau)
      exact hk
    simp only [H]
    constructor
    · intro h sigma tau A
      have hP2 := mul_eq_one_comm.mp (P588Aux.tp_unit d m sigma)
      obtain ⟨h1, -⟩ := h sigma tau
        ((Schur.tensorPermutation d m sigma)ᴴ * A * Schur.tensorPermutation d m sigma)
      obtain ⟨-, h2⟩ := h sigma tau A
      rw [P588Aux.sandwich _ _ hP2] at h1
      rw [← h1]
      exact h2
    · intro h sigma tau A
      constructor
      · have h1 := h sigma 1 (Schur.tensorPermutation d m sigma * A *
          (Schur.tensorPermutation d m sigma)ᴴ)
        have hc : (Schur.tensorPermutation d m sigma)ᴴ *
            (Schur.tensorPermutation d m sigma * A * (Schur.tensorPermutation d m sigma)ᴴ) *
            Schur.tensorPermutation d m sigma = A := by
          have := P588Aux.sandwich ((Schur.tensorPermutation d m sigma)ᴴ) A
            (by rw [Matrix.conjTranspose_conjTranspose]; exact P588Aux.tp_unit d m sigma)
          rwa [Matrix.conjTranspose_conjTranspose] at this
        rw [hc, P588Aux.tp_one] at h1
        simpa using h1.symm
      · have h1 := h 1 tau A
        rw [P588Aux.tp_one] at h1
        simpa using h1
