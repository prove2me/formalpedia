-- Prove2me | solution 1 for QReversal.PGMBound.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T04:11:04.88107+00:00
-- url     : https://prove2.me/submissions/090ebed5-52f3-4f18-8273-d47470c08eb3

import Mathlib
import Definitions.Def_QReversal_PGMBound_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder
open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

namespace PGMProof

noncomputable def block {J O : Type*} (M : Matrix (J × O) (J × O) ℂ) (i j : J) :
    Matrix O O ℂ := fun a b => M (i,a) (j,b)

noncomputable def frobSq {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℂ) : ℝ := ∑ r, ∑ c, Complex.normSq (M r c)

end PGMProof

open Matrix Unitary
open scoped MatrixOrder ComplexOrder BigOperators

namespace PGMProof

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]

lemma functional_mul {M : Matrix C C ℂ} (h : M.IsHermitian) (f g : ℝ → ℝ) :
    h.cfc f * h.cfc g = h.cfc (fun t => f t * g t) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul, diagonal_mul_diagonal]
  congr 1
  funext i
  simp [Function.comp_def]

lemma functional_sub {M : Matrix C C ℂ} (h : M.IsHermitian) (f g : ℝ → ℝ) :
    h.cfc f - h.cfc g = h.cfc (fun t => f t - g t) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_sub, diagonal_sub]
  congr 1
  funext i
  simp [Function.comp_def]

lemma functional_id {M : Matrix C C ℂ} (h : M.IsHermitian) : h.cfc id = M := by
  exact h.spectral_theorem.symm

lemma functional_one {M : Matrix C C ℂ} (h : M.IsHermitian) : h.cfc (fun _ => 1) = 1 := by
  simp [Matrix.IsHermitian.cfc, Function.comp_def]

lemma functional_congr {M : Matrix C C ℂ} (h : M.IsHermitian) {f g : ℝ → ℝ}
    (heq : ∀ i, f (h.eigenvalues i) = g (h.eigenvalues i)) : h.cfc f = h.cfc g := by
  unfold Matrix.IsHermitian.cfc
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply, heq]

lemma functional_pos {M : Matrix C C ℂ} (h : M.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (h.eigenvalues i)) : (h.cfc f).PosSemidef := by
  rw [Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply posSemidef_diagonal_iff.mpr
  intro i
  simpa [Function.comp_def] using (Complex.zero_le_real.mpr (hf i))

lemma functional_sqrt {M : Matrix C C ℂ} (h : M.PosSemidef) :
    h.isHermitian.cfc Real.sqrt = CFC.sqrt M := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ M, h.isHermitian.cfc_eq]
  congr 1
  funext x
  exact Real.sqrt.eq_def x

omit [DecidableEq C] in
lemma frobSq_eq_trace (Y : Matrix R C ℂ) :
    frobSq Y = (Yᴴ * Y).trace.re := by
  simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := Y j i))

omit [DecidableEq C] in
lemma frobSq_nonneg (Y : Matrix R C ℂ) : 0 ≤ frobSq Y := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- A generalized polar factor; its construction includes zero singular values. -/
theorem rectangular_polar (Y : Matrix R C ℂ) :
    ∃ U : Matrix R C ℂ,
      (1 - Uᴴ * U).PosSemidef ∧
      Uᴴ * Y = CFC.sqrt (Yᴴ * Y) ∧
      U * CFC.sqrt (Yᴴ * Y) = Y := by
  let M := Yᴴ * Y
  have hM : M.PosSemidef := posSemidef_conjTranspose_mul_self Y
  let h := hM.isHermitian
  let D := h.cfc (fun t => (Real.sqrt t)⁻¹)
  let H := h.cfc Real.sqrt
  let E := h.cfc (fun t => if t = 0 then 0 else 1)
  have hD : D.PosSemidef := functional_pos h _ (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hH : H = CFC.sqrt M := functional_sqrt hM
  have hDM : D * M = H := by
    calc
      D * M = D * h.cfc id := by rw [functional_id]
      _ = h.cfc (fun t => (Real.sqrt t)⁻¹ * t) := functional_mul h _ _
      _ = H := by
        apply functional_congr
        intro i
        have ht := hM.eigenvalues_nonneg i
        have hs := Real.sq_sqrt ht
        by_cases hz : Real.sqrt (h.eigenvalues i) = 0
        · have hz' : h.eigenvalues i = 0 := by nlinarith
          simp [hz']
        · calc
            (Real.sqrt (h.eigenvalues i))⁻¹ * h.eigenvalues i =
                (Real.sqrt (h.eigenvalues i))⁻¹ * (Real.sqrt (h.eigenvalues i))^2 := by rw [hs]
            _ = Real.sqrt (h.eigenvalues i) := by field_simp
  have hDMD : D * M * D = E := by
    rw [hDM]
    change h.cfc Real.sqrt * h.cfc (fun t => (Real.sqrt t)⁻¹) = _
    rw [functional_mul]
    apply functional_congr
    intro i
    by_cases hi : h.eigenvalues i = 0
    · simp [hi]
    · have hp : 0 < h.eigenvalues i := lt_of_le_of_ne (hM.eigenvalues_nonneg i) (Ne.symm hi)
      simp [hi, ne_of_gt (Real.sqrt_pos.mpr hp)]
  have hDH : D * H = E := by
    change h.cfc (fun t => (Real.sqrt t)⁻¹) * h.cfc Real.sqrt = _
    rw [functional_mul]
    apply functional_congr
    intro i
    by_cases hi : h.eigenvalues i = 0
    · simp [hi]
    · have hp : 0 < h.eigenvalues i := lt_of_le_of_ne (hM.eigenvalues_nonneg i) (Ne.symm hi)
      simp [hi, ne_of_gt (Real.sqrt_pos.mpr hp)]
  have hE : (1 - E).PosSemidef := by
    rw [← functional_one h]
    change (h.cfc (fun _ => 1) - h.cfc (fun t => if t = 0 then 0 else 1)).PosSemidef
    rw [functional_sub]
    apply functional_pos
    intro i
    split_ifs <;> norm_num
  have hME : M * (1-E) = 0 := by
    rw [← functional_one h]
    change M * (h.cfc (fun _ => 1) - h.cfc (fun t => if t = 0 then 0 else 1)) = 0
    rw [functional_sub]
    conv_lhs => lhs; rw [← functional_id h]
    rw [functional_mul]
    have hz : h.cfc (fun t => t * (1 - if t = 0 then 0 else 1)) = h.cfc (fun _ => 0) := by
      apply functional_congr
      intro i
      split_ifs <;> simp_all
    change h.cfc (fun t => t * (1 - if t = 0 then 0 else 1)) = 0
    rw [hz]
    simp [Matrix.IsHermitian.cfc, Function.comp_def]
  have hYE : Y * (1-E) = 0 := by
    apply (trace_conjTranspose_mul_self_eq_zero_iff).mp
    have hh : (Y * (1-E))ᴴ * (Y * (1-E)) = (1-E)ᴴ * (M * (1-E)) := by
      simp only [conjTranspose_mul, M, Matrix.mul_assoc]
    rw [hh, hME, Matrix.mul_zero, Matrix.trace_zero]
  refine ⟨Y * D, ?_, ?_, ?_⟩
  · have hh : (Y * D)ᴴ * (Y * D) = D * M * D := by
      simp only [conjTranspose_mul, hD.isHermitian.eq, M, Matrix.mul_assoc]
    rw [hh, hDMD]
    exact hE
  · rw [conjTranspose_mul, hD.isHermitian.eq, Matrix.mul_assoc]
    exact hDM.trans hH
  · rw [← hH, Matrix.mul_assoc, hDH]
    have := hYE
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm

end PGMProof

open Matrix Unitary WithLp
open scoped MatrixOrder ComplexOrder BigOperators

namespace PGMProof

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]

omit [DecidableEq C] in
lemma norm_sq_dot (x : C → ℂ) :
    ‖toLp 2 x‖ ^ 2 = (star x ⬝ᵥ x).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  simp only [EuclideanSpace.inner_toLp_toLp, RCLike.re_eq_complex_re, dotProduct_comm]

omit [DecidableEq C] in
lemma mulVec_norm_sq (B : Matrix R C ℂ) (x : C → ℂ) :
    ‖toLp 2 (B *ᵥ x)‖ ^ 2 = (star x ⬝ᵥ ((Bᴴ * B) *ᵥ x)).re := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  exact norm_sq_dot _

lemma contraction_norm (T : Matrix R C ℂ) (hT : (1-Tᴴ*T).PosSemidef) (x : C → ℂ) :
    ‖toLp 2 (T *ᵥ x)‖ ≤ ‖toLp 2 x‖ := by
  have h := hT.re_dotProduct_nonneg x
  change 0 ≤ (star x ⬝ᵥ ((1-Tᴴ*T) *ᵥ x)).re at h
  rw [Matrix.sub_mulVec, one_mulVec, dotProduct_sub, Complex.sub_re,
    ← norm_sq_dot, ← mulVec_norm_sq] at h
  nlinarith [norm_nonneg (toLp 2 x), norm_nonneg (toLp 2 (T *ᵥ x))]

lemma trace_pair_basis (T B : Matrix R C ℂ) (h : (Bᴴ*B).IsHermitian) :
    (Tᴴ * B).trace.re = ∑ i,
      (star (T *ᵥ ⇑(h.eigenvectorBasis i)) ⬝ᵥ (B *ᵥ ⇑(h.eigenvectorBasis i))).re := by
  let V : Matrix C C ℂ := h.eigenvectorUnitary
  have hv : V * Vᴴ = 1 := Unitary.coe_mul_star_self h.eigenvectorUnitary
  have ht : ((T*V)ᴴ * (B*V)).trace = (Tᴴ * B).trace := by
    rw [conjTranspose_mul]
    calc
      _ = (Vᴴ * (Tᴴ * B) * V).trace := by simp only [Matrix.mul_assoc]
      _ = (V * Vᴴ * (Tᴴ * B)).trace := Matrix.trace_mul_cycle _ _ _
      _ = _ := by rw [hv, Matrix.one_mul]
  rw [← ht]
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- The trace pairing with any rectangular contraction is bounded by the spectral trace norm. -/
theorem dual_trace_bound (T B : Matrix R C ℂ) (hT : (1-Tᴴ*T).PosSemidef) :
    (Tᴴ * B).trace.re ≤ (CFC.sqrt (Bᴴ*B)).trace.re := by
  let hM := posSemidef_conjTranspose_mul_self B
  let h := hM.isHermitian
  rw [trace_pair_basis T B h]
  have htrace : (CFC.sqrt (Bᴴ*B)).trace.re = ∑ i, Real.sqrt (h.eigenvalues i) := by
    rw [← functional_sqrt hM, Matrix.IsHermitian.cfc, conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
    simp [Function.comp_def]
  rw [htrace]
  apply Finset.sum_le_sum
  intro i _
  let x : EuclideanSpace ℂ C := h.eigenvectorBasis i
  have hx : ‖x‖ = 1 := h.eigenvectorBasis.norm_eq_one i
  have htx : ‖toLp 2 (T *ᵥ ⇑x)‖ ≤ 1 := by
    simpa only [toLp_ofLp, hx] using contraction_norm T hT ⇑x
  have hbx : ‖toLp 2 (B *ᵥ ⇑x)‖ ^ 2 = h.eigenvalues i := by
    rw [mulVec_norm_sq, h.mulVec_eigenvectorBasis]
    rw [dotProduct_smul]
    rw [← RCLike.re_eq_complex_re, RCLike.smul_re, RCLike.re_eq_complex_re]
    change h.eigenvalues i * (star x.ofLp ⬝ᵥ x.ofLp).re = _
    rw [← norm_sq_dot, toLp_ofLp, hx, one_pow, mul_one]
  have hb : ‖toLp 2 (B *ᵥ ⇑x)‖ = Real.sqrt (h.eigenvalues i) := by
    rw [← hbx, Real.sqrt_sq (norm_nonneg _)]
  have hcs := @re_inner_le_norm ℂ _ _ _ _ (toLp 2 (T *ᵥ ⇑x)) (toLp 2 (B *ᵥ ⇑x))
  have hdot : (star (T *ᵥ ⇑x) ⬝ᵥ (B *ᵥ ⇑x)).re ≤
      ‖toLp 2 (T *ᵥ ⇑x)‖ * ‖toLp 2 (B *ᵥ ⇑x)‖ := by
    simpa only [EuclideanSpace.inner_toLp_toLp, RCLike.re_eq_complex_re, dotProduct_comm] using hcs
  exact hdot.trans (by rw [hb]; nlinarith [Real.sqrt_nonneg (h.eigenvalues i)])

lemma trace_psd_product_nonneg {X Z : Matrix C C ℂ}
    (hX : X.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (X*Z).trace.re := by
  have hs : (CFC.sqrt X).PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  have hp := hZ.mul_mul_conjTranspose_same (CFC.sqrt X)
  rw [hs.isHermitian.eq] at hp
  have ht := hp.trace_nonneg
  have heq : (CFC.sqrt X * Z * CFC.sqrt X).trace = (X*Z).trace := by
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self X hX.nonneg]
  rw [heq] at ht
  exact (Complex.nonneg_iff.mp ht).1

end PGMProof

open Matrix
open scoped MatrixOrder ComplexOrder BigOperators
namespace PGMProof
variable {C R : Type*} [Fintype C] [Fintype R] [DecidableEq C]

/-- Compression of a positive block matrix by a generalized polar factor. -/
theorem block_estimate (X : Matrix C C ℂ) (Y : Matrix R C ℂ) (Z : Matrix R R ℂ)
    (hG : (Matrix.fromBlocks X Yᴴ Y Z).PosSemidef) :
    ∃ U : Matrix R C ℂ, (1-Uᴴ*U).PosSemidef ∧
      2 * frobSq Y ≤ (Uᴴ * (Y*X + Z*Y)).trace.re := by
  obtain ⟨U, hU, hUY, hUH⟩ := rectangular_polar Y
  refine ⟨U, hU, ?_⟩
  let H := CFC.sqrt (Yᴴ*Y)
  change Uᴴ * Y = H at hUY
  change U * H = Y at hUH
  have hH : H.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hYU : Yᴴ * U = H := by
    have hh := congrArg Matrix.conjTranspose hUY
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hH.isHermitian.eq] using hh
  have hK : (X + Uᴴ*Z*U - (H+H)).PosSemidef := by
    have hh := hG.conjTranspose_mul_mul_same (Matrix.fromRows (1 : Matrix C C ℂ) (-U))
    simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      conjTranspose_one, conjTranspose_neg, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_one,
      Matrix.neg_mul, Matrix.mul_neg, hUY, hYU, Matrix.add_mul] at hh
    convert hh using 1; abel
  have ht := trace_psd_product_nonneg hH hK
  have hsq : H*H = Yᴴ*Y := CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self Y).nonneg
  have ha : (H * (Uᴴ*Z*U)).trace = (Uᴴ*Z*Y).trace := by
    calc
      _ = (U * H * (Uᴴ*Z)).trace := by
        rw [← Matrix.mul_assoc H (Uᴴ*Z) U, Matrix.trace_mul_cycle]
      _ = (Y * (Uᴴ*Z)).trace := by rw [hUH]
      _ = _ := Matrix.trace_mul_comm _ _
  have hb : (H*X).trace = (Uᴴ*Y*X).trace := by rw [hUY]
  rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add,
    Complex.sub_re, Complex.add_re, Complex.add_re, ha, hb, hsq,
    ← frobSq_eq_trace] at ht
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  simpa only [Matrix.mul_assoc] using (show 2 * frobSq Y ≤
    (Uᴴ*Y*X).trace.re + (Uᴴ*Z*Y).trace.re by linarith)
end PGMProof

open Matrix
open scoped MatrixOrder ComplexOrder BigOperators
namespace PGMProof

variable {J O C : Type*} [Fintype J] [Fintype O] [Fintype C]
  [DecidableEq J] [DecidableEq O] [DecidableEq C]

noncomputable def rowBlock (U : Matrix (J × O) C ℂ) (j : J) : Matrix O C ℂ :=
  fun a b => U (j,a) b

omit [Fintype C] [DecidableEq J] [DecidableEq O] [DecidableEq C] in
lemma gram_row_sum (U V : Matrix (J × O) C ℂ) :
    Uᴴ*V = ∑ j, (rowBlock U j)ᴴ * rowBlock V j := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Fintype.sum_prod_type, rowBlock]

omit [DecidableEq O] in
lemma row_contraction (U : Matrix (J × O) C ℂ) (hU : (1-Uᴴ*U).PosSemidef) (j : J) :
    (1-(rowBlock U j)ᴴ*rowBlock U j).PosSemidef := by
  have hp := Matrix.posSemidef_sum (Finset.univ.erase j)
    (fun k _ => posSemidef_conjTranspose_mul_self (rowBlock U k))
  have hs := hU.add hp
  have he := Finset.sum_erase_add (Finset.univ (α := J))
    (fun k => (rowBlock U k)ᴴ*rowBlock U k) (Finset.mem_univ j)
  rw [gram_row_sum] at hs
  rw [← he] at hs
  convert hs using 1; abel

omit [DecidableEq J] [DecidableEq O] in
lemma trace_rows_bound (U B : Matrix (J × O) C ℂ) (hU : (1-Uᴴ*U).PosSemidef) :
    (Uᴴ*B).trace.re ≤ ∑ j, (CFC.sqrt ((rowBlock B j)ᴴ * rowBlock B j)).trace.re := by
  classical
  rw [gram_row_sum, Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_le_sum fun j _ => dual_trace_bound _ _ (row_contraction U hU j)

omit [Fintype C] [DecidableEq C] in
lemma column_offdiag_bound (G : Matrix (J×O) (J×O) ℂ) (hG : G.PosSemidef) (j : J) :
    2 * (∑ i : {i : J // i ≠ j}, frobSq (block G i j)) ≤
      ∑ i : {i : J // i ≠ j},
        (CFC.sqrt ((block (G*G) i j)ᴴ * block (G*G) i j)).trace.re := by
  let X := block G j j
  let Y : Matrix ({i : J // i ≠ j} × O) O ℂ := fun r a => G (r.1,r.2) (j,a)
  let Z : Matrix ({i : J // i ≠ j} × O) ({i : J // i ≠ j} × O) ℂ :=
    fun r s => G (r.1,r.2) (s.1,s.2)
  let e : O ⊕ ({i : J // i ≠ j} × O) → J×O := Sum.elim (fun a => (j,a)) (fun r => (r.1,r.2))
  have hg : (Matrix.fromBlocks X Yᴴ Y Z).PosSemidef := by
    convert hG.submatrix e using 1
    ext (a | a) (b | b) <;> simp only [Matrix.fromBlocks, Matrix.of_apply,
      Matrix.submatrix_apply, e, Sum.elim_inl, Sum.elim_inr, X, Y, Z, block]
    exact congrFun (congrFun hG.isHermitian.eq (j,a)) (b.1,b.2)
  obtain ⟨U,hU,hu⟩ := block_estimate X Y Z hg
  have hy : frobSq Y = ∑ i : {i : J // i ≠ j}, frobSq (block G i j) := by
    simp only [frobSq, Fintype.sum_prod_type, Y, block]
  have hb : Y*X+Z*Y = fun r a => (G*G) (r.1,r.2) (j,a) := by
    ext r a
    change (∑ b, G (r.1,r.2) (j,b)*G (j,b) (j,a)) +
      (∑ s : {i : J // i ≠ j} × O, G (r.1,r.2) (s.1,s.2)*G (s.1,s.2) (j,a)) =
      ∑ s : J×O, G (r.1,r.2) s*G s (j,a)
    simp only [Fintype.sum_prod_type]
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun i => ∑ b, G (r.1,r.2) (i,b)*G (i,b) (j,a)) j]
  have ht := trace_rows_bound U (Y*X+Z*Y) hU
  rw [hy] at hu
  apply hu.trans
  rw [hb] at ht ⊢
  exact ht

omit [Fintype C] [DecidableEq C] in
theorem offdiag_bound (G : Matrix (J×O) (J×O) ℂ) (hG : G.PosSemidef) :
    (∑ i, ∑ j, if i=j then 0 else ∑ a, ∑ b, Complex.normSq (G (i,a) (j,b))) ≤
      ∑ i, ∑ j, if i=j then 0 else
        (CFC.sqrt ((block (G*G) i j)ᴴ * block (G*G) i j)).trace.re := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => column_offdiag_bound G hG j)
  have he (f : J → J → ℝ) :
      (∑ j, ∑ i : {i : J // i ≠ j}, f i j) = ∑ i, ∑ j, if i=j then 0 else f i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i : J => i ≠ j)) (by simp) (fun i => f i j)]
    simp only [Finset.sum_filter, ite_not]
  rw [← Finset.mul_sum] at h
  rw [he (fun i j => frobSq (block G i j)),
    he (fun i j => (CFC.sqrt ((block (G*G) i j)ᴴ * block (G*G) i j)).trace.re)] at h
  have hn : 0 ≤ ∑ i, ∑ j, if i=j then 0 else frobSq (block G i j) := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      by split_ifs; exact le_rfl; exact frobSq_nonneg _
  change _ ≤ _
  have hh : (∑ i, ∑ j, if i=j then 0 else frobSq (block G i j)) ≤
      ∑ i, ∑ j, if i=j then 0 else
        (CFC.sqrt ((block (G*G) i j)ᴴ * block (G*G) i j)).trace.re := by linarith
  exact hh
end PGMProof

open Matrix
open scoped MatrixOrder ComplexOrder BigOperators
namespace PGMProof

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma native_invSqrt_psd {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (QReversal.NearOpt.invSqrt M).PosSemidef := by
  unfold QReversal.NearOpt.invSqrt
  rw [hM.isHermitian.cfc_eq]
  exact functional_pos _ _ fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma native_invSqrt_cancel {M : Matrix n n ℂ} (hM : M.PosDef) :
    QReversal.NearOpt.invSqrt M * M * QReversal.NearOpt.invSqrt M = 1 := by
  let h := hM.isHermitian
  unfold QReversal.NearOpt.invSqrt
  simp only [h.cfc_eq]
  conv_lhs => lhs; rhs; rw [← functional_id h]
  rw [functional_mul, functional_mul, ← functional_one h]
  apply functional_congr
  intro i
  have hp := hM.eigenvalues_pos i
  have hs := Real.sq_sqrt hp.le
  have hn : Real.sqrt (h.eigenvalues i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  change (Real.sqrt (h.eigenvalues i))⁻¹ * h.eigenvalues i *
    (Real.sqrt (h.eigenvalues i))⁻¹ = 1
  field_simp
  nlinarith

lemma sqrt_conjugate {M U : Matrix n n ℂ} (hM : M.PosSemidef)
    (hU : U * Uᴴ = 1) :
    CFC.sqrt (Uᴴ * M * U) = Uᴴ * CFC.sqrt M * U := by
  apply CFC.sqrt_unique
  · calc
      (Uᴴ * CFC.sqrt M * U) * (Uᴴ * CFC.sqrt M * U) =
          Uᴴ * (CFC.sqrt M * (U * Uᴴ) * CFC.sqrt M) * U := by noncomm_ring
      _ = Uᴴ * M * U := by rw [hU, Matrix.mul_one, CFC.sqrt_mul_sqrt_self M hM.nonneg]
  · exact ((CFC.sqrt_nonneg M).posSemidef.conjTranspose_mul_mul_same U).nonneg

lemma sqrt_real_smul (a : ℝ) (ha : 0 ≤ a) {M : Matrix n n ℂ}
    (hM : M.PosSemidef) :
    CFC.sqrt ((a : ℂ) • M) = (Real.sqrt a : ℂ) • CFC.sqrt M := by
  apply CFC.sqrt_unique
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      CFC.sqrt_mul_sqrt_self M hM.nonneg]
    congr 1
    norm_cast
    nlinarith [Real.sq_sqrt ha]
  · exact ((CFC.sqrt_nonneg M).posSemidef.smul
      (Complex.zero_le_real.mpr (Real.sqrt_nonneg a))).nonneg

lemma sqrt_real_diagonal (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    CFC.sqrt (diagonal (fun i => (p i : ℂ))) = diagonal (fun i => (Real.sqrt (p i) : ℂ)) := by
  apply CFC.sqrt_unique
  · rw [diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    nlinarith [Real.sq_sqrt (hp i)]
  · apply Matrix.PosSemidef.nonneg
    exact posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr (Real.sqrt_nonneg _)

omit [DecidableEq n] in
lemma positive_gram_square {R : Type*} [Fintype R] [DecidableEq R]
    (A : Matrix R n ℂ) (hA : (A * Aᴴ).PosDef) :
    let G := Aᴴ * QReversal.NearOpt.invSqrt (A * Aᴴ) * A
    G.PosSemidef ∧ G * G = Aᴴ * A := by
  dsimp
  constructor
  · exact (native_invSqrt_psd hA.posSemidef).conjTranspose_mul_mul_same A
  · calc
      (Aᴴ * QReversal.NearOpt.invSqrt (A*Aᴴ) * A) *
          (Aᴴ * QReversal.NearOpt.invSqrt (A*Aᴴ) * A) =
        Aᴴ * (QReversal.NearOpt.invSqrt (A*Aᴴ) * (A*Aᴴ) *
          QReversal.NearOpt.invSqrt (A*Aᴴ)) * A := by simp only [Matrix.mul_assoc]
      _ = Aᴴ * A := by rw [native_invSqrt_cancel hA, Matrix.mul_one]

end PGMProof

open Matrix PeresTerno QReversal.PGMBound
open scoped MatrixOrder ComplexOrder BigOperators
namespace PGMProof

lemma real_star (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x

variable {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]

noncomputable def eigenMatrix (v : O → J → O → ℂ) (j : J) : Matrix O O ℂ :=
  fun a i => v i j a
noncomputable def weightedColumns (p : J → ℝ) (lam : O → J → ℝ)
    (v : O → J → O → ℂ) (j : J) : Matrix O O ℂ :=
  fun a i => (Real.sqrt (p j) * Real.sqrt (lam i j) : ℂ) * v i j a

omit [Fintype J] [DecidableEq J] in
lemma eigenMatrix_unitary (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hs : IsSpectralData lam v) (j : J) :
    (eigenMatrix v j)ᴴ * eigenMatrix v j = 1 ∧
    eigenMatrix v j * (eigenMatrix v j)ᴴ = 1 := by
  have h : (eigenMatrix v j)ᴴ * eigenMatrix v j = 1 := by
    ext i k
    simpa [Matrix.mul_apply, eigenMatrix, Matrix.one_apply, dotProduct] using hs.2.2 j i k
  exact ⟨h, mul_eq_one_comm.mp h⟩

omit [Fintype J] [DecidableEq J] in
lemma rhoHat_spectral (lam : O → J → ℝ) (v : O → J → O → ℂ) (j : J) :
    rhoHat lam v j = eigenMatrix v j * diagonal (fun i => (lam i j : ℂ)) *
      (eigenMatrix v j)ᴴ := by
  ext a b
  simp only [rhoHat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, eigenMatrix, Matrix.conjTranspose_apply, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype J] [DecidableEq J] in
lemma rhoHat_psd (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hs : IsSpectralData lam v) (j : J) : (rhoHat lam v j).PosSemidef := by
  rw [rhoHat_spectral]
  exact (posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr
    (hs.1 i j)).mul_mul_conjTranspose_same _

omit [Fintype J] [DecidableEq J] in
lemma rhoHat_trace (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hs : IsSpectralData lam v) (j : J) : (rhoHat lam v j).trace = 1 := by
  rw [rhoHat_spectral, Matrix.trace_mul_cycle, (eigenMatrix_unitary lam v hs j).1,
    Matrix.one_mul, Matrix.trace_diagonal]
  norm_cast
  exact hs.2.1 j

omit [Fintype J] [DecidableEq J] in
lemma columns_spectral (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ) (j : J) :
    weightedColumns p lam v j = eigenMatrix v j *
      diagonal (fun i => (Real.sqrt (p j) * Real.sqrt (lam i j) : ℂ)) := by
  ext a i
  simp [weightedColumns, eigenMatrix, Matrix.mul_diagonal, mul_comm]

omit [Fintype J] [DecidableEq J] in
lemma columns_square (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : ∀ j, 0 ≤ p j) (hl : ∀ i j, 0 ≤ lam i j) (j : J) :
    weightedColumns p lam v j * (weightedColumns p lam v j)ᴴ = weightedState p lam v j := by
  ext a b
  simp only [weightedColumns, weightedState, rhoHat, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_mul, real_star, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h1 : (Real.sqrt (p j) : ℂ) ^ 2 = (p j : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hp j)
  have h2 : (Real.sqrt (lam i j) : ℂ) ^ 2 = (lam i j : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hl i j)
  calc
    _ = (Real.sqrt (p j) : ℂ)^2 * (Real.sqrt (lam i j) : ℂ)^2 *
      (v i j a * star (v i j b)) := by ring
    _ = _ := by rw [h1, h2]; ring

omit [DecidableEq J] in
lemma amat_square (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : ∀ j, 0 ≤ p j) (hl : ∀ i j, 0 ≤ lam i j) :
    Amat p lam v * (Amat p lam v)ᴴ = ∑ j, weightedState p lam v j := by
  simp_rw [← columns_square p lam v hp hl]
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Fintype.sum_prod_type, Amat, weightedColumns]

lemma classic_output (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hl : ∀ i j, 0 ≤ lam i j) :
    rhoOut p lam v = ∑ j, weightedState p lam v j := by
  have hterm (i : O) (j : J) :
      classicKraus lam v (i,j) * rho p * (classicKraus lam v (i,j))ᴴ =
      ((p j : ℂ)*(lam i j : ℂ)) • vecMulVec (v i j) (star (v i j)) := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [rho, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    simp [classicKraus, vecMulVec, Pi.single_apply, mul_ite, ite_mul]
    have hs : (Real.sqrt (lam i j) : ℂ)^2 = (lam i j : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (hl i j)
    calc
      _ = (Real.sqrt (lam i j) : ℂ)^2 * ((p j : ℂ)*v i j a*(starRingEnd ℂ) (v i j b)) := by ring
      _ = _ := by rw [hs]; ring
  unfold rhoOut krausUpdate
  simp only [Fintype.sum_prod_type, hterm]
  rw [Finset.sum_comm]
  ext a b
  simp only [weightedState, rhoHat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma output_eq_gram (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) :
    rhoOut p lam v = Amat p lam v * (Amat p lam v)ᴴ := by
  rw [classic_output p lam v hs.1, amat_square p lam v hp.1 hs.1]

lemma output_trace (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) : (rhoOut p lam v).trace = 1 := by
  rw [classic_output p lam v hs.1, Matrix.trace_sum]
  simp only [weightedState, Matrix.trace_smul, rhoHat_trace lam v hs, smul_eq_mul, mul_one]
  norm_cast
  exact hp.2

end PGMProof

open Matrix PeresTerno QReversal.PGMBound
open scoped MatrixOrder ComplexOrder BigOperators
namespace PGMProof

variable {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]

noncomputable def recoveryGram (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ) :
    Matrix (J × O) (J × O) ℂ :=
  (Amat p lam v)ᴴ * QReversal.NearOpt.invSqrt (rhoOut p lam v) * Amat p lam v

lemma recoveryGram_psd_square (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) (hfull : (rhoOut p lam v).PosDef) :
    (recoveryGram p lam v).PosSemidef ∧
      recoveryGram p lam v * recoveryGram p lam v = (Amat p lam v)ᴴ * Amat p lam v := by
  rw [output_eq_gram p lam v hp hs] at hfull
  simpa only [recoveryGram, output_eq_gram p lam v hp hs] using positive_gram_square (Amat p lam v) hfull

lemma recoveryGram_total (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) (hfull : (rhoOut p lam v).PosDef) :
    frobSq (recoveryGram p lam v) = 1 := by
  obtain ⟨hG, hsq⟩ := recoveryGram_psd_square p lam v hp hs hfull
  rw [frobSq_eq_trace, hG.isHermitian.eq, hsq, Matrix.trace_mul_comm,
    ← output_eq_gram p lam v hp hs, output_trace p lam v hp hs]
  simp

omit [Fintype O] [DecidableEq O] in
lemma kraus_diagonal {K : Type*} [Fintype K] (M : K → Matrix J J ℂ) (j : J) :
    (krausUpdate M (Matrix.single j j 1) j j).re = ∑ k, Complex.normSq (M k j j) := by
  simp [krausUpdate, Matrix.sum_apply, Matrix.mul_apply, Matrix.single, ite_and,
    Matrix.conjTranspose_apply, Complex.mul_conj ]

lemma recovery_amplitude (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (a b : O) (k l j : J) :
    (Real.sqrt (p j) : ℂ) *
      (QReversal.PGMBound.comp (reversal (classicKraus lam v) (rho p))
        (classicKraus lam v) ((a,k),(b,l))) j j =
      if k = j ∧ l = j then recoveryGram p lam v (j,a) (j,b) else 0 := by
  have hr := sqrt_real_diagonal p hp.1
  change (Real.sqrt (p j) : ℂ) *
    ((CFC.sqrt (rho p) * (classicKraus lam v (a,k))ᴴ *
      QReversal.NearOpt.invSqrt (rhoOut p lam v)) * classicKraus lam v (b,l)) j j = _
  rw [show CFC.sqrt (rho p) = diagonal (fun j => (Real.sqrt (p j) : ℂ)) from hr]
  simp only [Matrix.mul_assoc, Matrix.diagonal_mul]
  by_cases hk : k = j <;> by_cases hl : l = j
  · subst k
    subst l
    simp only [and_self, if_true]
    simp only [recoveryGram, Matrix.mul_apply, classicKraus,
      Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
      star_mul, real_star, Pi.single_eq_same, mul_one,
      Amat, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro r _
    ring
  · simp [classicKraus, vecMulVec, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Pi.single_apply, hl, hk, eq_comm]
  · simp [classicKraus, vecMulVec, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Pi.single_apply, hk, hl, eq_comm]
  · simp [classicKraus, vecMulVec, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Pi.single_apply, hk, hl, eq_comm]

lemma classical_diagonal_mass (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) :
    Fcl p (QReversal.PGMBound.comp (reversal (classicKraus lam v) (rho p))
      (classicKraus lam v)) =
      ∑ j, ∑ a, ∑ b, Complex.normSq (recoveryGram p lam v (j,a) (j,b)) := by
  unfold Fcl
  simp only [kraus_diagonal, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  have hsqrt : Complex.normSq (Real.sqrt (p j) : ℂ) = p j := by
    simpa [Complex.normSq_ofReal, pow_two] using Real.sq_sqrt (hp.1 j)
  have hnorm (z : ℂ) : p j * Complex.normSq z =
      Complex.normSq ((Real.sqrt (p j) : ℂ) * z) := by
    rw [Complex.normSq_mul, hsqrt]
  simp_rw [hnorm, recovery_amplitude p lam v hp]
  simp only [apply_ite, Complex.normSq_zero, ite_and]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single j]
  · simp only [if_true, Finset.sum_ite_eq', Finset.mem_univ]
  · intro k _ hk
    simp [hk]
  · simp

lemma recovery_error_identity (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) (hfull : (rhoOut p lam v).PosDef) :
    Fcl p (QReversal.PGMBound.comp (reversal (classicKraus lam v) (rho p))
      (classicKraus lam v)) = 1 -
      ∑ i, ∑ j, if i = j then 0 else
        ∑ a, ∑ b, Complex.normSq (recoveryGram p lam v (i,a) (j,b)) := by
  rw [classical_diagonal_mass p lam v hp]
  have ht := recoveryGram_total p lam v hp hs hfull
  unfold frobSq at ht
  simp only [Fintype.sum_prod_type] at ht
  have heq : (∑ i, ∑ a, ∑ j, ∑ b, Complex.normSq (recoveryGram p lam v (i,a) (j,b))) =
      (∑ i, ∑ a, ∑ b, Complex.normSq (recoveryGram p lam v (i,a) (i,b))) +
      ∑ i, ∑ j, if i = j then 0 else
        ∑ a, ∑ b, Complex.normSq (recoveryGram p lam v (i,a) (j,b)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    let f : J → ℝ := fun j => ∑ a, ∑ b, Complex.normSq (recoveryGram p lam v (i,a) (j,b))
    change (∑ j, f j) = f i + ∑ j, if i = j then 0 else f j
    calc
      (∑ j, f j) = ∑ j, ((if j = i then f i else 0) + (if i = j then 0 else f j)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j
        · subst j; simp
        · simp [h, Ne.symm h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linarith

end PGMProof

open Matrix PeresTerno QReversal.PGMBound
open scoped MatrixOrder ComplexOrder BigOperators
namespace PGMProof

variable {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]

omit [Fintype J] [DecidableEq J] in
lemma weighted_psd (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : ∀ j, 0 ≤ p j) (hs : IsSpectralData lam v) (j : J) :
    (weightedState p lam v j).PosSemidef :=
  (rhoHat_psd lam v hs j).smul (Complex.zero_le_real.mpr (hp j))

omit [Fintype J] [DecidableEq J] in
lemma columns_eq_sqrt (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : ∀ j, 0 ≤ p j) (hs : IsSpectralData lam v) (j : J) :
    weightedColumns p lam v j = CFC.sqrt (weightedState p lam v j) * eigenMatrix v j := by
  let V := eigenMatrix v j
  let D : Matrix O O ℂ := diagonal (fun i => (Real.sqrt (p j) * Real.sqrt (lam i j) : ℂ))
  have hv : Vᴴ * V = 1 := (eigenMatrix_unitary lam v hs j).1
  have hw : weightedColumns p lam v j = V * D := columns_spectral p lam v j
  have hD : D.PosSemidef := posSemidef_diagonal_iff.mpr fun i =>
    mul_nonneg (Complex.zero_le_real.mpr (Real.sqrt_nonneg _))
      (Complex.zero_le_real.mpr (Real.sqrt_nonneg _))
  have hroot : CFC.sqrt (weightedState p lam v j) = V * D * Vᴴ := by
    apply CFC.sqrt_unique
    · rw [← columns_square p lam v hp hs.1 j, hw, conjTranspose_mul, hD.isHermitian.eq]
      calc
        (V*D*Vᴴ)*(V*D*Vᴴ) = V*D*(Vᴴ*V)*D*Vᴴ := by noncomm_ring
        _ = (V*D)*(D*Vᴴ) := by rw [hv, Matrix.mul_one]; noncomm_ring
    · exact (hD.mul_mul_conjTranspose_same V).nonneg
  rw [hroot, Matrix.mul_assoc (V*D), hv, Matrix.mul_one]
  exact hw

omit [DecidableEq J] [DecidableEq O] in
lemma native_block_eq (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ) (k j : J) :
    Bblk p lam v k j = (weightedColumns p lam v k)ᴴ * weightedColumns p lam v j := by
  ext a b
  rfl

lemma sandwich_psd {M N : Matrix O O ℂ} (hN : N.PosSemidef) :
    (CFC.sqrt M * N * CFC.sqrt M).PosSemidef := by
  have hs := (CFC.sqrt_nonneg M).posSemidef.isHermitian.eq
  simpa only [hs] using hN.conjTranspose_mul_mul_same (CFC.sqrt M)

omit [Fintype J] [DecidableEq J] in
lemma weighted_fidelity (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : ∀ j, 0 ≤ p j) (hs : IsSpectralData lam v) (j k : J) :
    FBU (weightedState p lam v j) (weightedState p lam v k) =
      Real.sqrt (p k * p j) * FBU (rhoHat lam v j) (rhoHat lam v k) := by
  have hsj := rhoHat_psd lam v hs j
  have hsk := rhoHat_psd lam v hs k
  have hscalar : (Real.sqrt (p j) : ℂ)^2 = (p j : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hp j)
  unfold FBU weightedState
  rw [sqrt_real_smul (p j) (hp j) hsj]
  have heq : ((Real.sqrt (p j) : ℂ) • CFC.sqrt (rhoHat lam v j)) *
      ((p k : ℂ) • rhoHat lam v k) *
      ((Real.sqrt (p j) : ℂ) • CFC.sqrt (rhoHat lam v j)) =
      ((p k*p j : ℝ) : ℂ) •
        (CFC.sqrt (rhoHat lam v j) * rhoHat lam v k * CFC.sqrt (rhoHat lam v j)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    push_cast
    calc
      _ = (p k : ℂ) * (Real.sqrt (p j) : ℂ)^2 := by ring
      _ = _ := by rw [hscalar]
  rw [heq, sqrt_real_smul _ (mul_nonneg (hp k) (hp j)) (sandwich_psd hsk),
    Matrix.trace_smul]
  simp

omit [DecidableEq J] in
lemma block_trace_fidelity (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) (k j : J) :
    (Matrix.trace (CFC.sqrt ((Bblk p lam v k j)ᴴ * Bblk p lam v k j))).re =
      Real.sqrt (p k * p j) * FBU (rhoHat lam v j) (rhoHat lam v k) := by
  let Wk := weightedColumns p lam v k
  let Wj := weightedColumns p lam v j
  let V := eigenMatrix v j
  let H := CFC.sqrt (weightedState p lam v j)
  have hH : Hᴴ = H := (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  have hWj : Wj = H * V := columns_eq_sqrt p lam v hp.1 hs j
  have hWk : Wk * Wkᴴ = weightedState p lam v k := columns_square p lam v hp.1 hs.1 k
  have heq : (Bblk p lam v k j)ᴴ * Bblk p lam v k j =
      Vᴴ * (H * weightedState p lam v k * H) * V := by
    rw [native_block_eq]
    change (Wkᴴ * Wj)ᴴ * (Wkᴴ * Wj) = _
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hWj, conjTranspose_mul, hH]
    calc
      (Vᴴ * H) * Wk * (Wkᴴ * (H*V)) = Vᴴ * (H*(Wk*Wkᴴ)*H)*V := by noncomm_ring
      _ = _ := by rw [hWk]
  rw [heq, sqrt_conjugate (sandwich_psd (weighted_psd p lam v hp.1 hs k))
    (eigenMatrix_unitary lam v hs j).2]
  rw [Matrix.trace_mul_cycle, (eigenMatrix_unitary lam v hs j).2, Matrix.one_mul]
  exact weighted_fidelity p lam v hp.1 hs j k

end PGMProof

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder BigOperators

namespace QReversal.PGMBound

theorem theorem_5 {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    1 - ∑ i, ∑ j, (if i = j then 0 else
      Real.sqrt (p i * p j) * FBU (rhoHat lam v i) (rhoHat lam v j)) ≤
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) := by
  let G := PGMProof.recoveryGram p lam v
  obtain ⟨hG, hsq⟩ := PGMProof.recoveryGram_psd_square p lam v hp hs hfull
  have hbound := PGMProof.offdiag_bound G hG
  have hb : ∀ i j, PGMProof.block (G * G) i j = Bblk p lam v i j := by
    intro i j
    unfold PGMProof.block
    change (fun a b => (PGMProof.recoveryGram p lam v *
      PGMProof.recoveryGram p lam v) (i,a) (j,b)) = _
    rw [hsq]
    rfl
  simp_rw [hb, PGMProof.block_trace_fidelity p lam v hp hs] at hbound
  have hswap : (∑ i, ∑ j, if i = j then 0 else
      Real.sqrt (p i*p j) * FBU (rhoHat lam v j) (rhoHat lam v i)) =
      ∑ i, ∑ j, if i = j then 0 else
        Real.sqrt (p i*p j) * FBU (rhoHat lam v i) (rhoHat lam v j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [eq_comm, mul_comm]
  rw [hswap] at hbound
  rw [PGMProof.recovery_error_identity p lam v hp hs hfull]
  change _ ≤ _ at hbound
  linarith


end QReversal.PGMBound

open QReversal.PGMBound

theorem solution {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    1 - ∑ i, ∑ j, (if i = j then 0 else
      Real.sqrt (p i * p j) * FBU (rhoHat lam v i) (rhoHat lam v j)) ≤
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) := by
  exact QReversal.PGMBound.theorem_5 p lam v hp hs hfull
