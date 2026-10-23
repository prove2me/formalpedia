-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P07.lu_polynomialTest
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:05:46.043355+00:00
-- url     : https://prove2.me/submissions/be8e10fd-1b1d-49c8-bdd6-000611f7a157

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

lemma X7_kron_conj_mul (U V : Local) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (Matrix.kronecker U V)ᴴ * Matrix.kronecker U V = 1 := by
  change (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one]

lemma X7_kron_mul_conj (U V : Local) (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) :
    Matrix.kronecker U V * (Matrix.kronecker U V)ᴴ = 1 := by
  change (U ⊗ₖ V) * (U ⊗ₖ V)ᴴ = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one]

lemma X7_lu_iff (C D : Joint) : LU C D ↔ ∃ U V : Local, Intertwining C D U V := by
  constructor
  · rintro ⟨U, V, hD⟩
    have hU : (U : Local)ᴴ * U = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').mp U.2; simpa [Matrix.star_eq_conjTranspose] using this
    have hV : (V : Local)ᴴ * V = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').mp V.2; simpa [Matrix.star_eq_conjTranspose] using this
    refine ⟨U, V, hU, hV, ?_⟩
    rw [hD, Matrix.mul_assoc _ _ (Matrix.kronecker _ _), X7_kron_conj_mul _ _ hU hV, Matrix.mul_one]
  · rintro ⟨U, V, hU, hV, hW⟩
    have hU' : U ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
      (Matrix.mem_unitaryGroup_iff').mpr (by simpa [Matrix.star_eq_conjTranspose] using hU)
    have hV' : V ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
      (Matrix.mem_unitaryGroup_iff').mpr (by simpa [Matrix.star_eq_conjTranspose] using hV)
    have hU2 : U * Uᴴ = 1 := by
      have := (Matrix.mem_unitaryGroup_iff).mp hU'; simpa [Matrix.star_eq_conjTranspose] using this
    have hV2 : V * Vᴴ = 1 := by
      have := (Matrix.mem_unitaryGroup_iff).mp hV'; simpa [Matrix.star_eq_conjTranspose] using this
    refine ⟨⟨U, hU'⟩, ⟨V, hV'⟩, ?_⟩
    change D = Matrix.kronecker U V * C * (Matrix.kronecker U V)ᴴ
    rw [hW, Matrix.mul_assoc, X7_kron_mul_conj _ _ hU2 hV2, Matrix.mul_one]


abbrev X7_P := MvPolynomial RealVariables ℝ

def X7_ev (x : RealVariables → ℝ) (p : X7_P × X7_P) : ℂ :=
  (MvPolynomial.eval x p.1 : ℂ) + Complex.I * (MvPolynomial.eval x p.2 : ℂ)

def X7_cmul (a b : X7_P × X7_P) : X7_P × X7_P :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def X7_cconst (z : ℂ) : X7_P × X7_P := (MvPolynomial.C z.re, MvPolynomial.C z.im)

lemma X7_ev_cmul (x : RealVariables → ℝ) (a b : X7_P × X7_P) :
    X7_ev x (X7_cmul a b) = X7_ev x a * X7_ev x b := by
  simp only [X7_ev, X7_cmul, map_mul, map_sub, map_add]
  push_cast
  linear_combination (-(MvPolynomial.eval x a.2 : ℂ) * (MvPolynomial.eval x b.2 : ℂ)) * Complex.I_sq

lemma X7_ev_cconst (x : RealVariables → ℝ) (z : ℂ) : X7_ev x (X7_cconst z) = z := by
  simp only [X7_ev, X7_cconst, MvPolynomial.eval_C]
  rw [mul_comm]; exact Complex.re_add_im z

lemma X7_ev_add (x : RealVariables → ℝ) (a b : X7_P × X7_P) :
    X7_ev x (a + b) = X7_ev x a + X7_ev x b := by
  simp only [X7_ev, Prod.fst_add, Prod.snd_add, map_add]; push_cast; ring

lemma X7_ev_sub (x : RealVariables → ℝ) (a b : X7_P × X7_P) :
    X7_ev x (a - b) = X7_ev x a - X7_ev x b := by
  simp only [X7_ev, Prod.fst_sub, Prod.snd_sub, map_sub]; push_cast; ring

lemma X7_ev_sum {ι : Type*} (x : RealVariables → ℝ) (s : Finset ι) (f : ι → X7_P × X7_P) :
    X7_ev x (∑ i ∈ s, f i) = ∑ i ∈ s, X7_ev x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [X7_ev]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, X7_ev_add, ih]

lemma X7_ev_eq_zero (x : RealVariables → ℝ) (p : X7_P × X7_P) :
    X7_ev x p = 0 ↔ MvPolynomial.eval x p.1 = 0 ∧ MvPolynomial.eval x p.2 = 0 := by
  simp only [X7_ev, Complex.ext_iff]
  simp

/-- entries of the local matrices -/
def X7_U (s : Fin 2) (i j : Fin 3) : X7_P × X7_P :=
  (MvPolynomial.X (s, 0, i, j), MvPolynomial.X (s, 1, i, j))

def X7_Uh (s : Fin 2) (i j : Fin 3) : X7_P × X7_P :=
  (MvPolynomial.X (s, 0, j, i), -MvPolynomial.X (s, 1, j, i))

lemma X7_ev_U (x : RealVariables → ℝ) (s : Fin 2) (i j : Fin 3) :
    X7_ev x (X7_U s i j) = decodeMatrix x s i j := by
  simp [X7_ev, X7_U, decodeMatrix]

lemma X7_ev_Uh (x : RealVariables → ℝ) (s : Fin 2) (i j : Fin 3) :
    X7_ev x (X7_Uh s i j) = (decodeMatrix x s)ᴴ i j := by
  simp [X7_ev, X7_Uh, decodeMatrix, Matrix.conjTranspose_apply]

def X7_E1 (s : Fin 2) (a b : Fin 3) : X7_P × X7_P :=
  ∑ k : Fin 3, X7_cmul (X7_Uh s a k) (X7_U s k b) - X7_cconst (if a = b then 1 else 0)

lemma X7_ev_E1 (x : RealVariables → ℝ) (s : Fin 2) (a b : Fin 3) :
    X7_ev x (X7_E1 s a b) = ((decodeMatrix x s)ᴴ * decodeMatrix x s - 1) a b := by
  simp only [X7_E1, X7_ev_sub, X7_ev_sum, X7_ev_cmul, X7_ev_U, X7_ev_Uh, X7_ev_cconst,
    Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply]

def X7_E3 (C D : Joint) (p q : Fin 3 × Fin 3) : X7_P × X7_P :=
  ∑ r : Fin 3 × Fin 3, X7_cmul (X7_cmul (X7_U 0 p.1 r.1) (X7_U 1 p.2 r.2)) (X7_cconst (C r q)) -
  ∑ r : Fin 3 × Fin 3, X7_cmul (X7_cconst (D p r)) (X7_cmul (X7_U 0 r.1 q.1) (X7_U 1 r.2 q.2))

lemma X7_ev_E3 (x : RealVariables → ℝ) (C D : Joint) (p q : Fin 3 × Fin 3) :
    X7_ev x (X7_E3 C D p q) =
      (Matrix.kronecker (decodeMatrix x 0) (decodeMatrix x 1) * C -
        D * Matrix.kronecker (decodeMatrix x 0) (decodeMatrix x 1)) p q := by
  simp only [X7_E3, X7_ev_sub, X7_ev_sum, X7_ev_cmul, X7_ev_U, X7_ev_cconst,
    Matrix.sub_apply, Matrix.mul_apply]
  rfl

def X7_g (C D : Joint) (j : Fin 3 × (Fin 3 × Fin 3) × (Fin 3 × Fin 3)) : X7_P × X7_P :=
  if j.1 = 0 then X7_E1 0 j.2.1.1 j.2.2.1
  else if j.1 = 1 then X7_E1 1 j.2.1.1 j.2.2.1
  else X7_E3 C D j.2.1 j.2.2

lemma X7_g_iff (C D : Joint) (x : RealVariables → ℝ) :
    (∀ j, X7_ev x (X7_g C D j) = 0) ↔ Intertwining C D (decodeMatrix x 0) (decodeMatrix x 1) := by
  unfold Intertwining
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · ext a b
      have := h (0, (a, 0), (b, 0))
      simp only [X7_g, if_true] at this
      rw [X7_ev_E1, Matrix.sub_apply] at this
      exact sub_eq_zero.mp this
    · ext a b
      have := h (1, (a, 0), (b, 0))
      simp only [X7_g, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true] at this
      rw [X7_ev_E1, Matrix.sub_apply] at this
      exact sub_eq_zero.mp this
    · ext p q
      have := h (2, p, q)
      simp only [X7_g, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false,
        X7_ev_E3, Matrix.sub_apply] at this
      exact sub_eq_zero.mp this
  · rintro ⟨h1, h2, h3⟩ ⟨k, a, b⟩
    simp only [X7_g]
    split_ifs
    · rw [X7_ev_E1, h1, sub_self, Matrix.zero_apply]
    · rw [X7_ev_E1, h2, sub_self, Matrix.zero_apply]
    · rw [X7_ev_E3, h3, sub_self, Matrix.zero_apply]

lemma X7_poly (C D : Joint) :
    ∃ m : ℕ, ∃ f : Fin m → MvPolynomial RealVariables ℝ, ∀ x : RealVariables → ℝ,
      (∀ i, MvPolynomial.eval x (f i) = 0) ↔
        Intertwining C D (decodeMatrix x 0) (decodeMatrix x 1) := by
  let ι := Fin 2 × Fin 3 × (Fin 3 × Fin 3) × (Fin 3 × Fin 3)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k =>
    if (e.symm k).1 = 0 then (X7_g C D (e.symm k).2).1 else (X7_g C D (e.symm k).2).2, ?_⟩
  intro x
  rw [← X7_g_iff]
  constructor
  · intro h j
    rw [X7_ev_eq_zero]
    constructor
    · have := h (e (0, j)); simpa using this
    · have := h (e (1, j)); simpa using this
  · intro h k
    obtain ⟨hA, hB⟩ := (X7_ev_eq_zero x _).mp (h (e.symm k).2)
    dsimp only
    split_ifs
    · exact hA
    · exact hB

end QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P07 in
theorem solution (C D : Joint) (hC : C.PosSemidef) (hD : D.PosSemidef) :
    (LU C D ↔ ∃ U V : Local, Intertwining C D U V) ∧
    ∃ m : ℕ, ∃ f : Fin m → MvPolynomial RealVariables ℝ, ∀ x : RealVariables → ℝ,
      (∀ i, MvPolynomial.eval x (f i) = 0) ↔ Intertwining C D (decodeMatrix x 0) (decodeMatrix x 1) :=
  ⟨X7_lu_iff C D, X7_poly C D⟩

end
