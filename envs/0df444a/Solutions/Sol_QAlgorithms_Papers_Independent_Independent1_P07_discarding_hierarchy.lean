-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.discarding_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:59:42.841625+00:00
-- url     : https://prove2.me/submissions/eacd083a-46df-4750-aca3-7488bfc3fde4

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder MatrixOrder

lemma g53_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g53_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma g53_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : U * star U = 1)
    (hD : star U * (A - B) * U = Matrix.diagonal (RCLike.ofReal ∘ lam)) :
    ∑ i, max (lam i) 0 ≤ A.trace.re := by
  have hA' := hA.conjTranspose_mul_mul_same U
  have hB' := hB.conjTranspose_mul_mul_same U
  have htr : A.trace = (Uᴴ * A * U).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hU, one_mul]
  rw [htr, Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : (Uᴴ * A * U) i i - (Uᴴ * B * U) i i = ((lam i : ℝ) : ℂ) := by
    have := congrArg (fun M => M i i) hD
    rw [Matrix.mul_sub, Matrix.sub_mul] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have ha' : 0 ≤ ((Uᴴ * A * U) i i).re := (Complex.nonneg_iff.mp (hA'.diag_nonneg (i := i))).1
  have hb' : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.nonneg_iff.mp (hB'.diag_nonneg (i := i))).1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  simp only [Matrix.diag]
  exact max_le (by linarith) ha'

lemma g53_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g53_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g53_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [g53_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := g53_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact g53_posPart_aux lam hA hB hu hD

lemma g53_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

lemma g53_negPart_eq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma g53_traceNorm_add_le {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (X + Y) ≤ QAlgorithms.traceNorm X + QAlgorithms.traceNorm Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  rw [g53_traceNorm_herm hXY, g53_traceNorm_herm hX, g53_traceNorm_herm hY]
  have pX := g53_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := g53_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have pY := g53_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := g53_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := g53_parts X hX
  have eY := g53_parts Y hY
  have e1 : X + Y = (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) -
      (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) := by
    conv_lhs => rw [← eX, ← eY]
    abel
  have e2 : -(X + Y) = (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) -
      (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) := by
    rw [e1]; abel
  have h1 := g53_posPart_le hXY (pX.add pY) (mX.add mY) e1
  have h2 := g53_posPart_le hXY.neg (mX.add mY) (pX.add pY) e2
  rw [← g53_negPart_eq] at h2
  rw [Matrix.trace_add, Complex.add_re] at h1 h2
  linarith


lemma S180J_tn_psd {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    QAlgorithms.traceNorm P = P.trace.re := by
  rw [g53_traceNorm_herm hP.1]
  have hsp : ∀ x ∈ spectrum ℝ P, 0 ≤ x := fun x hx =>
    spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP) hx
  have e1 : cfc (fun t : ℝ => max t 0) P = P := by
    conv_rhs => rw [← cfc_id' ℝ P]
    exact cfc_congr fun x hx => max_eq_left (hsp x hx)
  have e2 : cfc (fun t : ℝ => max (-t) 0) P = 0 := by
    rw [← cfc_zero ℝ P]
    exact cfc_congr fun x hx => max_eq_right (by linarith [hsp x hx])
  rw [e1, e2]; simp

lemma S180J_tn_neg {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) :
    QAlgorithms.traceNorm (-P) = QAlgorithms.traceNorm P := by
  unfold QAlgorithms.traceNorm; simp [Matrix.conjTranspose_neg]

lemma S180J_tr_real {n : Type*} [Fintype n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    0 ≤ P.trace.re ∧ P.trace = ((P.trace.re : ℝ) : ℂ) := by
  have h := hP.trace_nonneg
  rw [Complex.nonneg_iff] at h
  refine ⟨h.1, Complex.ext (by simp) (by simp [← h.2])⟩

lemma S180J_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) :
    ∃ r : Matrix n n ℂ, QAlgorithms.IsDensityMatrix r ∧ P = ((P.trace.re : ℝ) : ℂ) • r := by
  obtain ⟨h0, htr⟩ := S180J_tr_real hP
  generalize P.trace.re = a at h0 htr ⊢
  by_cases ha : a = 0
  · subst ha
    have hc : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    refine ⟨((1 / (Fintype.card n : ℝ) : ℝ) : ℂ) • 1, ⟨?_, ?_⟩, ?_⟩
    · exact Matrix.PosSemidef.one.smul (by positivity)
    · rw [Matrix.trace_smul, Matrix.trace_one]; simp <;> field_simp
    · have : P.trace = 0 := by rw [htr]; simp
      rw [hP.trace_eq_zero_iff.mp this]; simp
  · have hpos : 0 < a := lt_of_le_of_ne h0 (Ne.symm ha)
    refine ⟨((a⁻¹ : ℝ) : ℂ) • P, ⟨hP.smul (by positivity), ?_⟩, ?_⟩
    · rw [Matrix.trace_smul, smul_eq_mul, htr, ← Complex.ofReal_mul, inv_mul_cancel₀ ha]; simp
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ha]; simp


lemma S180D_pt_herm {I J : Type*} {M : Matrix (I × J) (I × J) ℂ} (hM : M.IsHermitian) :
    (QAlgorithms.Entanglement.partialTransposeFirst M).IsHermitian := by
  ext p q
  have := congrFun (congrFun hM (q.1, p.2)) (p.1, q.2)
  simp only [Matrix.conjTranspose_apply] at this
  simp [QAlgorithms.Entanglement.partialTransposeFirst, Matrix.conjTranspose_apply, ← this]


section
variable {A X Y : Type*} [Fintype A] [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq X]
  [DecidableEq Y]

lemma S180D_trR_eq (M : Matrix ((A × X) × Y) ((A × X) × Y) ℂ) :
    QAlgorithms.traceRight M = ∑ y : Y,
      (Matrix.of (fun (p : (A × X) × Y) (j : A × X) => if p = (j, y) then (1 : ℂ) else 0))ᴴ * M *
      Matrix.of (fun (p : (A × X) × Y) (j : A × X) => if p = (j, y) then (1 : ℂ) else 0) := by
  ext j k
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp [apply_ite star, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

lemma S180D_trR_psd {M : Matrix ((A × X) × Y) ((A × X) × Y) ℂ} (hM : M.PosSemidef) :
    (QAlgorithms.traceRight M).PosSemidef := by
  rw [S180D_trR_eq]
  exact Matrix.posSemidef_sum _ (fun y _ => hM.conjTranspose_mul_mul_same _)

lemma S180D_trR_trace (M : Matrix (A × (X × Y)) (A × (X × Y)) ℂ) :
    (QAlgorithms.traceRight (M.submatrix (Equiv.prodAssoc A X Y) (Equiv.prodAssoc A X Y))).trace =
      M.trace := by
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceRight, Matrix.of_apply,
    Matrix.submatrix_apply]
  rw [← Finset.sum_product', ← Equiv.sum_comp (Equiv.prodAssoc A X Y)]
  rfl

lemma S180D_pt_comm (M : Matrix (A × (X × Y)) (A × (X × Y)) ℂ) :
    QAlgorithms.Entanglement.partialTransposeFirst
        (QAlgorithms.traceRight (M.submatrix (Equiv.prodAssoc A X Y) (Equiv.prodAssoc A X Y))) =
      QAlgorithms.traceRight
        ((QAlgorithms.Entanglement.partialTransposeFirst M).submatrix (Equiv.prodAssoc A X Y)
          (Equiv.prodAssoc A X Y)) := by
  ext p q
  simp [QAlgorithms.Entanglement.partialTransposeFirst, QAlgorithms.traceRight]

lemma S180D_contract {Z : Matrix (A × (X × Y)) (A × (X × Y)) ℂ} (hZ : Z.IsHermitian) :
    QAlgorithms.traceNorm (QAlgorithms.traceRight
        (Z.submatrix (Equiv.prodAssoc A X Y) (Equiv.prodAssoc A X Y))) ≤
      QAlgorithms.traceNorm Z := by
  set P := cfc (fun t : ℝ => max t 0) Z
  set Q := cfc (fun t : ℝ => max (-t) 0) Z
  have hP : P.PosSemidef := g53_cfc_psd Z _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := g53_cfc_psd Z _ (fun t => le_max_right _ _)
  have e : QAlgorithms.traceRight (Z.submatrix (Equiv.prodAssoc A X Y) (Equiv.prodAssoc A X Y)) =
      QAlgorithms.traceRight (P.submatrix (Equiv.prodAssoc A X Y) (Equiv.prodAssoc A X Y)) +
      -QAlgorithms.traceRight (Q.submatrix (Equiv.prodAssoc A X Y) (Equiv.prodAssoc A X Y)) := by
    conv_lhs => rw [← g53_parts Z hZ]
    ext j k
    simp [QAlgorithms.traceRight, Finset.sum_sub_distrib, sub_eq_add_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, P, Q]
  have hP' := S180D_trR_psd (hP.submatrix (Equiv.prodAssoc A X Y))
  have hQ' := S180D_trR_psd (hQ.submatrix (Equiv.prodAssoc A X Y))
  rw [e]
  refine (g53_traceNorm_add_le hP'.1 hQ'.1.neg).trans (le_of_eq ?_)
  rw [S180J_tn_neg, S180J_tn_psd hP', S180J_tn_psd hQ', S180D_trR_trace, S180D_trR_trace,
    g53_traceNorm_herm hZ]

lemma S180D_step (ρ : Matrix (A × (X × Y)) (A × (X × Y)) ℂ) (hρ : ρ.IsHermitian) :
    QAlgorithms.traceNorm (QAlgorithms.Entanglement.partialTransposeFirst
      (QAlgorithms.traceRight (ρ.submatrix (Equiv.prodAssoc A X Y) (Equiv.prodAssoc A X Y)))) ≤
    QAlgorithms.traceNorm (QAlgorithms.Entanglement.partialTransposeFirst ρ) := by
  rw [S180D_pt_comm]
  exact S180D_contract (S180D_pt_herm hρ)

end

lemma S180D_tn_ge_trace {n : Type*} [Fintype n] [DecidableEq n] {Z : Matrix n n ℂ}
    (hZ : Z.IsHermitian) : Z.trace.re ≤ QAlgorithms.traceNorm Z := by
  rw [g53_traceNorm_herm hZ]
  have hQ : (cfc (fun t : ℝ => max (-t) 0) Z).PosSemidef := g53_cfc_psd Z _ (fun t => le_max_right _ _)
  have h0 := (S180J_tr_real hQ).1
  conv_lhs => rw [← g53_parts Z hZ]
  rw [Matrix.trace_sub, Complex.sub_re]
  linarith

lemma S180D_pt_trace {I J : Type*} [Fintype I] [Fintype J] (M : Matrix (I × J) (I × J) ℂ) :
    (QAlgorithms.Entanglement.partialTransposeFirst M).trace = M.trace := by
  simp [Matrix.trace, QAlgorithms.Entanglement.partialTransposeFirst]

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07 in
theorem solution {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (rho : Matrix (A × ((B × C) × D)) (A × ((B × C) × D)) ℂ)
    (hrho : IsDensityMatrix rho) :
    let rABC := traceRight (rho.submatrix (fun z : (A × (B × C)) × D => (z.1.1,(z.1.2,z.2)))
      (fun z : (A × (B × C)) × D => (z.1.1,(z.1.2,z.2))))
    let rAB := traceRight (rABC.submatrix (fun z : (A × B) × C => (z.1.1,(z.1.2,z.2)))
      (fun z : (A × B) × C => (z.1.1,(z.1.2,z.2))))
    negativity rAB ≤ negativity rABC ∧ negativity rABC ≤ negativity rho ∧
    logNeg rAB ≤ logNeg rABC ∧ logNeg rABC ≤ logNeg rho := by
  intro rABC rAB
  have e1 : rABC = traceRight (rho.submatrix (Equiv.prodAssoc A (B × C) D)
      (Equiv.prodAssoc A (B × C) D)) := rfl
  have e2 : rAB = traceRight (rABC.submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)) := rfl
  have hABC : rABC.PosSemidef := by
    rw [e1]; exact S180D_trR_psd (hrho.1.submatrix _)
  have hAB : rAB.PosSemidef := by
    rw [e2]; exact S180D_trR_psd (hABC.submatrix _)
  have t1 : rABC.trace = 1 := by rw [e1, S180D_trR_trace, hrho.2]
  have t2 : rAB.trace = 1 := by rw [e2, S180D_trR_trace, t1]
  have s1 : traceNorm (partialTransposeFirst rAB) ≤ traceNorm (partialTransposeFirst rABC) := by
    rw [e2]; exact S180D_step rABC hABC.1
  have s2 : traceNorm (partialTransposeFirst rABC) ≤ traceNorm (partialTransposeFirst rho) := by
    rw [e1]; exact S180D_step rho hrho.1.1
  have p1 : 0 < traceNorm (partialTransposeFirst rAB) := by
    have := S180D_tn_ge_trace (S180D_pt_herm hAB.1)
    rw [S180D_pt_trace, t2] at this; simp at this; linarith
  have p2 : 0 < traceNorm (partialTransposeFirst rABC) := by
    have := S180D_tn_ge_trace (S180D_pt_herm hABC.1)
    rw [S180D_pt_trace, t1] at this; simp at this; linarith
  refine ⟨?_, ?_, Real.logb_le_logb_of_le one_lt_two p1 s1, Real.logb_le_logb_of_le one_lt_two p2 s2⟩
  · unfold negativity; linarith
  · unfold negativity; linarith
