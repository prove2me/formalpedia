-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P67.uniformMaximalComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:57:14.054989+00:00
-- url     : https://prove2.me/submissions/364eb7fa-8e62-4353-b214-c59bfd33324f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67

namespace G55UM

section gen
variable {A Y : Type*} [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]

lemma aeval_block (Xs : Y → Matrix A A ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval (Matrix.blockDiagonal Xs) P = Matrix.blockDiagonal (fun y => Polynomial.aeval (Xs y) P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Matrix.blockDiagonal_add]; congr 1; funext y; simp [map_add]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]
    rw [← Matrix.blockDiagonal_pow, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_smul,
      ← Matrix.blockDiagonal_mul]
    rfl

lemma cfc_block (f : ℝ → ℝ) (Xs : Y → Matrix A A ℂ) (hX : ∀ y, (Xs y).IsHermitian) :
    cfc f (Matrix.blockDiagonal Xs) = Matrix.blockDiagonal (fun y => cfc f (Xs y)) := by
  have hB : (Matrix.blockDiagonal Xs).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1; funext y; exact (hX y).eq
  let S : Finset ℝ := (Matrix.finite_real_spectrum (A := Matrix.blockDiagonal Xs)).toFinset ∪
    Finset.univ.biUnion (fun y => (Matrix.finite_real_spectrum (A := Xs y)).toFinset)
  let P : Polynomial ℝ := Lagrange.interpolate S id f
  have hP : ∀ x ∈ S, P.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (r := f) (v := id) (Set.injOn_id _) hx
  have h1 : cfc f (Matrix.blockDiagonal Xs) = Polynomial.aeval (Matrix.blockDiagonal Xs) P := by
    rw [← cfc_polynomial P _ hB.isSelfAdjoint]
    refine cfc_congr fun x hx => (hP x ?_).symm
    simp [S, hx]
  have h2 : ∀ y, cfc f (Xs y) = Polynomial.aeval (Xs y) P := by
    intro y
    rw [← cfc_polynomial P _ (hX y).isSelfAdjoint]
    refine cfc_congr fun x hx => (hP x ?_).symm
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
    exact Or.inr ⟨y, hx⟩
  rw [h1, aeval_block]
  congr 1; funext y; exact (h2 y).symm



end gen

lemma cfc_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (f : ℝ → ℝ) (X : Matrix m m ℂ) (hX : X.IsHermitian) :
    cfc f (Matrix.reindex e e X) = Matrix.reindex e e (cfc f X) := by
  have hR : (Matrix.reindex e e X).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, hX.eq]
  let S : Finset ℝ := (Matrix.finite_real_spectrum (A := X)).toFinset ∪
    (Matrix.finite_real_spectrum (A := Matrix.reindex e e X)).toFinset
  let P : Polynomial ℝ := Lagrange.interpolate S id f
  have hP : ∀ x ∈ S, P.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (r := f) (v := id) (Set.injOn_id _) hx
  have h1 : cfc f (Matrix.reindex e e X) = Polynomial.aeval (Matrix.reindex e e X) P := by
    rw [← cfc_polynomial P _ hR.isSelfAdjoint]
    refine cfc_congr fun x hx => (hP x ?_).symm
    simp only [S, Finset.mem_union, Set.Finite.mem_toFinset]
    exact Or.inr hx
  have h2 : cfc f X = Polynomial.aeval X P := by
    rw [← cfc_polynomial P _ hX.isSelfAdjoint]
    refine cfc_congr fun x hx => (hP x ?_).symm
    simp [S, hx]
  rw [h1, h2]
  have := Polynomial.aeval_algHom_apply (Matrix.reindexAlgEquiv ℝ ℂ e).toAlgHom X P
  simpa using this


section rf
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sqrt_herm (X : Matrix I I ℂ) : (cfc Real.sqrt X).IsHermitian :=
  (cfc_predicate (R := ℝ) (p := IsSelfAdjoint) _ X)

lemma sand_herm (X Y : Matrix I I ℂ) (hY : Y.IsHermitian) :
    (cfc Real.sqrt X * Y * cfc Real.sqrt X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, (sqrt_herm X).eq, hY.eq, Matrix.mul_assoc]

lemma sqrt_smul (c : ℝ) (hc : 0 ≤ c) (W : Matrix I I ℂ) (hW : W.IsHermitian) :
    cfc Real.sqrt ((c : ℂ) • W) = ((Real.sqrt c : ℝ) : ℂ) • cfc Real.sqrt W := by
  rw [Complex.coe_smul, Complex.coe_smul,
    ← cfc_comp_smul c _ W ((Matrix.finite_real_spectrum.image _).continuousOn _) hW.isSelfAdjoint,
    ← cfc_const_mul _ _ W (Matrix.finite_real_spectrum.continuousOn _)]
  refine cfc_congr fun x _ => ?_
  simp only [smul_eq_mul]
  exact Real.sqrt_mul hc x

lemma rf_smul (c : ℝ) (hc : 0 ≤ c) (X Y : Matrix I I ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    rootFidelity ((c : ℂ) • X) ((c : ℂ) • Y) = c * rootFidelity X Y := by
  unfold rootFidelity
  rw [sqrt_smul c hc X hX]
  have e : ((Real.sqrt c : ℝ) : ℂ) • cfc Real.sqrt X * ((c : ℂ) • Y) * (((Real.sqrt c : ℝ) : ℂ) • cfc Real.sqrt X)
      = ((c * c : ℝ) : ℂ) • (cfc Real.sqrt X * Y * cfc Real.sqrt X) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    have : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = (c : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
    push_cast
    linear_combination (c : ℂ) * this
  rw [e, sqrt_smul _ (mul_nonneg hc hc) _ (sand_herm X Y hY), Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, Real.sqrt_mul_self hc]

lemma rf_nonneg (X Y : Matrix I I ℂ) : 0 ≤ rootFidelity X Y := by
  unfold rootFidelity
  have : (cfc Real.sqrt (cfc Real.sqrt X * Y * cfc Real.sqrt X)).PosSemidef := by
    open scoped MatrixOrder in
    rw [← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg fun x _ => Real.sqrt_nonneg x
  exact (Complex.nonneg_iff.mp this.trace_nonneg).1

end rf


lemma rf_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (X Y : Matrix m m ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    rootFidelity (Matrix.reindex e e X) (Matrix.reindex e e Y) = rootFidelity X Y := by
  unfold rootFidelity
  rw [cfc_reindex e _ X hX]
  have hm : ∀ P Q : Matrix m m ℂ, Matrix.reindex e e P * Matrix.reindex e e Q = Matrix.reindex e e (P * Q) := by
    intro P Q
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [hm, hm, cfc_reindex e _ _ (sand_herm X Y hY)]
  simp only [Matrix.reindex_apply, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  congr 1
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

lemma rf_block {A Y : Type*} [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]
    (Xs Ys : Y → Matrix A A ℂ) (hX : ∀ y, (Xs y).IsHermitian) (hY : ∀ y, (Ys y).IsHermitian) :
    rootFidelity (Matrix.blockDiagonal Xs) (Matrix.blockDiagonal Ys) = ∑ y, rootFidelity (Xs y) (Ys y) := by
  unfold rootFidelity
  rw [cfc_block _ Xs hX, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul,
    cfc_block _ _ (fun y => sand_herm (Xs y) (Ys y) (hY y)), Matrix.trace_blockDiagonal, Complex.re_sum]


section bound
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma psd_le_norm (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    (((‖K‖ : ℝ) : ℂ) • (1 : Matrix I I ℂ) - K).PosSemidef := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self (a := K) hK.1.isSelfAdjoint
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
  simpa [Complex.coe_smul] using h

lemma spec_nonneg' {X : Matrix I I ℂ} (hX : X.PosSemidef) {x : ℝ} (hx : x ∈ spectrum ℝ X) : 0 ≤ x :=
  spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hX) hx

lemma sqrt_sq_psd (Y : Matrix I I ℂ) (hY : Y.PosSemidef) : cfc Real.sqrt Y * cfc Real.sqrt Y = Y := by
  rw [← cfc_mul _ _ Y (Matrix.finite_real_spectrum.continuousOn _) (Matrix.finite_real_spectrum.continuousOn _)]
  conv_rhs => rw [← cfc_id' ℝ Y]
  refine cfc_congr fun x hx => ?_
  exact Real.mul_self_sqrt (spec_nonneg' hY hx)

lemma rf_bound (X Y : Matrix I I ℂ) (hY : Y.PosSemidef) :
    rootFidelity X Y ≤ Fintype.card I + ‖cfc Real.sqrt X * cfc Real.sqrt X‖ * Y.trace.re := by
  set S := cfc Real.sqrt X with hS
  have hSh : S.IsHermitian := sqrt_herm X
  set Z := S * Y * S with hZ
  have hZp : Z.PosSemidef := by
    have := hY.conjTranspose_mul_mul_same S
    rwa [hSh.eq] at this
  -- step 1: tr √Z ≤ card + tr Z
  have h1 : rootFidelity X Y ≤ Fintype.card I + Z.trace.re := by
    unfold rootFidelity
    rw [← hS, ← hZ]
    have hle : cfc Real.sqrt Z ≤ cfc (fun x : ℝ => 1 + x) Z := by
      apply cfc_mono (fun x hx => ?_) (Matrix.finite_real_spectrum.continuousOn _)
        (Matrix.finite_real_spectrum.continuousOn _)
      have hx0 := spec_nonneg' hZp hx
      have hs := Real.sq_sqrt hx0
      have := Real.sqrt_nonneg x
      nlinarith
    rw [cfc_add Z (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x) (Matrix.finite_real_spectrum.continuousOn _)
      (Matrix.finite_real_spectrum.continuousOn _), cfc_const (1 : ℝ) Z, map_one, cfc_id' ℝ Z] at hle
    have := (Matrix.le_iff.mp hle).trace_nonneg
    rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one] at this
    have := (Complex.nonneg_iff.mp this).1
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re] at this
    linarith
  -- step 2: tr Z ≤ ‖S S‖ tr Y
  have h2 : Z.trace.re ≤ ‖S * S‖ * Y.trace.re := by
    have hW : (S * S).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self S
      rwa [hSh.eq] at this
    set R := cfc Real.sqrt Y
    have hRh : R.IsHermitian := sqrt_herm Y
    have hRR : R * R = Y := sqrt_sq_psd Y hY
    have hp := (psd_le_norm _ hW).conjTranspose_mul_mul_same R
    rw [hRh.eq] at hp
    have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hRR,
      Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at ht
    have hZt : Z.trace = (R * (S * S) * R).trace := by
      rw [hZ, ← hRR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [hZt]; linarith
  have := Complex.nonneg_iff.mp hY.trace_nonneg
  linarith

end bound


section p67
variable {A B E : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

lemma jo_re (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) :
    jointOutput U code = Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
      (Matrix.blockDiagonal (fun m => ((code.M : ℂ)⁻¹) • messageOutput U code m)) := by
  ext a b
  simp only [jointOutput, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Matrix.blockDiagonal_apply, Matrix.smul_apply,
    smul_eq_mul]

lemma ij_re {K : ℕ} (σ : Matrix E E ℂ) :
    idealJoint K σ = Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
      (Matrix.blockDiagonal (fun m : Fin K => ((K : ℂ)⁻¹) • idealMessage m σ)) := by
  ext a b
  simp only [idealJoint, idealMessage, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Matrix.blockDiagonal_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h : a.1 = b.1
  · simp only [h, if_true]
    by_cases h1 : b.1 = a.2.1 <;> by_cases h2 : b.1 = b.2.1 <;> simp [h1, h2, eq_comm]
  · simp [h]

lemma im_herm {K : ℕ} (m : Fin K) (σ : Matrix E E ℂ) (hσ : σ.IsHermitian) : (idealMessage m σ).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, idealMessage]
  by_cases h : a.1 = m ∧ b.1 = m
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; exact congrFun (congrFun hσ.eq a.2) b.2
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]; simp

lemma mo_herm (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) (hc : code.Valid) (m : Fin code.M) :
    (messageOutput U code m).IsHermitian := by
  set W := dilationPower U n
  have hρ : (W * code.messages m * Wᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (hc.2.1 m).1.1.eq, Matrix.mul_assoc]
  ext a b
  rw [Matrix.conjTranspose_apply]
  unfold messageOutput
  by_cases h : b.1 = a.1
  · rw [if_pos h, if_pos h.symm, star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [star_mul']
    have h1 := congrFun (congrFun (hc.2.2.1 b.1).1.eq x) y
    have h2 := congrFun (congrFun hρ.eq (y, a.2)) (x, b.2)
    simp only [Matrix.conjTranspose_apply] at h1 h2
    rw [h1, h2, h]
  · rw [if_neg h, if_neg (Ne.symm h)]; simp

lemma bd_herm {Y : Type*} [Fintype Y] [DecidableEq Y] {I : Type*} (Xs : Y → Matrix I I ℂ)
    (h : ∀ y, (Xs y).IsHermitian) : (Matrix.blockDiagonal Xs).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1; funext y; exact (h y).eq

lemma smul_herm {I : Type*} (c : ℝ) (X : Matrix I I ℂ) (h : X.IsHermitian) :
    ((c : ℂ) • X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, h.eq]; simp

lemma part1 (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) (hc : code.Valid)
    (σ : Matrix (Fin n → E) (Fin n → E) ℂ) (hσ : σ.IsHermitian) :
    rootFidelity (jointOutput U code) (idealJoint code.M σ) =
      ∑ m, (code.M : ℝ)⁻¹ * rootFidelity (messageOutput U code m) (idealMessage m σ) := by
  have e : ((code.M : ℂ)⁻¹) = (((code.M : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [jo_re, ij_re, e,
    rf_reindex _ _ _ (bd_herm _ fun m => smul_herm _ _ (mo_herm U code hc m))
      (bd_herm _ fun m => smul_herm _ _ (im_herm m σ hσ)),
    rf_block _ _ (fun m => smul_herm _ _ (mo_herm U code hc m)) (fun m => smul_herm _ _ (im_herm m σ hσ))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rf_smul _ (by positivity) _ _ (mo_herm U code hc m) (im_herm m σ hσ)]


lemma im_psd {K : ℕ} (m : Fin K) (σ : Matrix E E ℂ) (hσ : σ.PosSemidef) :
    (idealMessage m σ).PosSemidef ∧ (idealMessage m σ).trace = σ.trace := by
  have e : idealMessage m σ = Matrix.kroneckerMap (· * ·)
      (Matrix.vecMulVec (Pi.single m (1 : ℂ)) (star (Pi.single m (1 : ℂ)))) σ := by
    ext a b
    simp only [idealMessage, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    by_cases h1 : a.1 = m <;> by_cases h2 : b.1 = m <;> simp [h1, h2]
  refine ⟨e ▸ (Matrix.posSemidef_vecMulVec_self_star _).kronecker hσ, ?_⟩
  simp only [Matrix.trace, Matrix.diag, idealMessage, Fintype.sum_prod_type, and_self]
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj; simp [hj]
  · simp

end p67

end G55UM

variable {A B E R S T X C Y G1 G2 : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]
variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]
variable [Fintype G2] [DecidableEq G2]

open G55UM in
open scoped Matrix.Norms.L2Operator in
theorem solution [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U) {n : ℕ}
    (code : PrivateCode A B n) (hc : code.Valid) :
    (∀ sigma : Matrix (Fin n → E) (Fin n → E) ℂ, IsDensityMatrix sigma →
      squaredFidelity (jointOutput U code) (idealJoint code.M sigma) =
        (((code.M : ℝ)⁻¹ * ∑ m : Fin code.M,
          Real.sqrt (squaredFidelity (messageOutput U code m) (idealMessage m sigma))) ^ 2)) ∧
    uniformError U code ≤ maximalError U code := by
  have hK : 0 < code.M := hc.1
  have hKr : (0 : ℝ) < code.M := by exact_mod_cast hK
  have hsq : ∀ σ : Matrix (Fin n → E) (Fin n → E) ℂ, σ.IsHermitian →
      squaredFidelity (jointOutput U code) (idealJoint code.M σ) =
        (∑ m, (code.M : ℝ)⁻¹ * rootFidelity (messageOutput U code m) (idealMessage m σ)) ^ 2 := by
    intro σ hσ; unfold squaredFidelity; rw [part1 U code hc σ hσ]
  refine ⟨fun σ hσ => ?_, ?_⟩
  · rw [hsq σ hσ.1.1, Finset.mul_sum]
    congr 2; funext m
    unfold squaredFidelity
    rw [Real.sqrt_sq (rf_nonneg _ _)]
  unfold uniformError maximalError
  let x0 : Fin n → E := fun _ => Classical.arbitrary E
  let σ0 : Matrix (Fin n → E) (Fin n → E) ℂ := Matrix.diagonal (fun x => if x = x0 then 1 else 0)
  have hσ0 : IsDensityMatrix σ0 := by
    refine ⟨Matrix.PosSemidef.diagonal fun x => ?_, ?_⟩
    · simp only [Pi.zero_apply]; split_ifs <;> simp
    · simp [σ0, Matrix.trace_diagonal]
  refine le_csInf ⟨sSup {s | ∃ m : Fin code.M,
    s = 1 - squaredFidelity (messageOutput U code m) (idealMessage m σ0)}, σ0, hσ0, rfl⟩ ?_
  rintro r ⟨σ, hσ, rfl⟩
  have hbdd : BddAbove {r | ∃ σ' : Matrix (Fin n → E) (Fin n → E) ℂ, IsDensityMatrix σ' ∧
      r = squaredFidelity (jointOutput U code) (idealJoint code.M σ')} := by
    refine ⟨(∑ m, (code.M : ℝ)⁻¹ * (Fintype.card (Fin code.M × (Fin n → E)) +
      ‖cfc Real.sqrt (messageOutput U code m) * cfc Real.sqrt (messageOutput U code m)‖ * 1)) ^ 2, ?_⟩
    rintro r ⟨σ', hσ', rfl⟩
    rw [hsq σ' hσ'.1.1]
    apply pow_le_pow_left₀ (Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (rf_nonneg _ _))
    refine Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hb := rf_bound (messageOutput U code m) (idealMessage m σ') (im_psd m σ' hσ'.1).1
    rwa [(im_psd m σ' hσ'.1).2, show σ'.trace.re = 1 by rw [hσ'.2]; simp] at hb
  have hopt : squaredFidelity (jointOutput U code) (idealJoint code.M σ) ≤ optimizedFidelity U code :=
    le_csSup hbdd ⟨σ, hσ, rfl⟩
  obtain ⟨m0, -, hm0⟩ := Finset.exists_min_image Finset.univ
    (fun m => rootFidelity (messageOutput U code m) (idealMessage m σ)) ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hfin : BddAbove {s | ∃ m : Fin code.M, s = 1 - squaredFidelity (messageOutput U code m) (idealMessage m σ)} := by
    have : {s | ∃ m : Fin code.M, s = 1 - squaredFidelity (messageOutput U code m) (idealMessage m σ)} =
        Set.range (fun m : Fin code.M => 1 - squaredFidelity (messageOutput U code m) (idealMessage m σ)) := by
      ext s; simp [eq_comm]
    rw [this]; exact (Set.finite_range _).bddAbove
  have hle := le_csSup hfin ⟨m0, rfl⟩
  have hge : rootFidelity (messageOutput U code m0) (idealMessage m0 σ) ^ 2 ≤
      squaredFidelity (jointOutput U code) (idealJoint code.M σ) := by
    rw [hsq σ hσ.1.1]
    apply pow_le_pow_left₀ (rf_nonneg _ _)
    calc rootFidelity (messageOutput U code m0) (idealMessage m0 σ)
        = ∑ _m : Fin code.M, (code.M : ℝ)⁻¹ * rootFidelity (messageOutput U code m0) (idealMessage m0 σ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
      _ ≤ _ := Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hm0 m (Finset.mem_univ _)) (by positivity)
  have : squaredFidelity (messageOutput U code m0) (idealMessage m0 σ) =
      rootFidelity (messageOutput U code m0) (idealMessage m0 σ) ^ 2 := rfl
  linarith
