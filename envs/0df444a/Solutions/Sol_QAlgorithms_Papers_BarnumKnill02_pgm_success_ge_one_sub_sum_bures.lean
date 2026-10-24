-- Prove2me | solution 1 for QAlgorithms.Papers.BarnumKnill02.pgm_success_ge_one_sub_sum_bures
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:55:05.169317+00:00
-- url     : https://prove2.me/submissions/4f898cf9-903a-4d32-9c44-5cad383db7d4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

set_option autoImplicit false


/-! Generic block overlap inequality, copied from the accepted actual proof of
QReversal.PGMBound.theorem_5 by sometik179, submission
090ebed5-52f3-4f18-8273-d47470c08eb3 (2026-10-21).
Only namespace/import changes; no full-rank theorem or hypothesis is imported. -/

open Matrix
open scoped MatrixOrder ComplexOrder
open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

namespace BarnumKnillOverlap

noncomputable def block {J O : Type*} (M : Matrix (J × O) (J × O) ℂ) (i j : J) :
    Matrix O O ℂ := fun a b => M (i,a) (j,b)

noncomputable def frobSq {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℂ) : ℝ := ∑ r, ∑ c, Complex.normSq (M r c)

end BarnumKnillOverlap

open Matrix Unitary
open scoped MatrixOrder ComplexOrder BigOperators

namespace BarnumKnillOverlap

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

end BarnumKnillOverlap

open Matrix Unitary WithLp
open scoped MatrixOrder ComplexOrder BigOperators

namespace BarnumKnillOverlap

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

end BarnumKnillOverlap

open Matrix
open scoped MatrixOrder ComplexOrder BigOperators
namespace BarnumKnillOverlap
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
end BarnumKnillOverlap

open Matrix
open scoped MatrixOrder ComplexOrder BigOperators
namespace BarnumKnillOverlap

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
end BarnumKnillOverlap



open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

namespace BarnumKnillOverlap

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
theorem inverse_support (M : Matrix R R ℂ) (hM : M.PosSemidef) :
    let D := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) M
    D.PosSemidef ∧ (1 - D * M * D).PosSemidef ∧ M * (1 - D * M * D) = 0 := by
  let h := hM.isHermitian
  let D := h.cfc (fun t => (Real.sqrt t)⁻¹)
  let E := h.cfc (fun t => if t = 0 then 0 else 1)
  have hD : D.PosSemidef := functional_pos h _ (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hDMD : D * M * D = E := by
    conv_lhs => lhs; rhs; rw [← functional_id h]
    rw [functional_mul, functional_mul]
    apply functional_congr
    intro i
    have ht := hM.eigenvalues_nonneg i
    by_cases hz : h.eigenvalues i = 0
    · simp [hz]
    · have hn : Real.sqrt (h.eigenvalues i) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm hz)))
      simp only [hz, if_false, id_eq]
      field_simp
      nlinarith [Real.sq_sqrt ht]
  have hE : (1 - E).PosSemidef := by
    rw [← functional_one h]
    change (h.cfc (fun _ => 1) - h.cfc (fun t => if t = 0 then 0 else 1)).PosSemidef
    rw [functional_sub]
    apply functional_pos
    intro i
    split_ifs <;> norm_num
  have hME : M * (1 - E) = 0 := by
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
  change (cfc (fun t : ℝ => (Real.sqrt t)⁻¹) M).PosSemidef ∧ _
  simp only [h.cfc_eq]
  change D.PosSemidef ∧ (1 - D * M * D).PosSemidef ∧ M * (1 - D * M * D) = 0
  exact ⟨hD, hDMD ▸ hE, hDMD ▸ hME⟩

omit [DecidableEq C] in
/-- The positive Gram factor identity on the support, without invertibility. -/
theorem positive_gram_square (A : Matrix R C ℂ) :
    let D := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (A * Aᴴ)
    let G := Aᴴ * D * A
    G.PosSemidef ∧ G * G = Aᴴ * A := by
  dsimp
  let M := A * Aᴴ
  let D := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) M
  let E := D * M * D
  obtain ⟨hD, _, hME⟩ := inverse_support M (posSemidef_self_mul_conjTranspose A)
  have hAE : Aᴴ * (1 - E) = 0 := by
    apply (trace_conjTranspose_mul_self_eq_zero_iff).mp
    have hh : (Aᴴ * (1-E))ᴴ * (Aᴴ * (1-E)) = (1-E)ᴴ * (M * (1-E)) := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, M, Matrix.mul_assoc]
    rw [hh, hME, Matrix.mul_zero, Matrix.trace_zero]
  have hEA : Aᴴ * E = Aᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hAE
    exact hAE.symm
  refine ⟨hD.conjTranspose_mul_mul_same A, ?_⟩
  change (Aᴴ * D * A) * (Aᴴ * D * A) = Aᴴ * A
  calc
    _ = Aᴴ * E * A := by simp only [E, M, Matrix.mul_assoc]
    _ = Aᴴ * A := by rw [hEA]

end BarnumKnillOverlap


open Matrix QAlgorithms
open scoped MatrixOrder ComplexOrder BigOperators

namespace BarnumKnillOverlap

variable {O ι : Type*} [Fintype O] [DecidableEq O] [Fintype ι] [DecidableEq ι]

omit [Fintype O] [DecidableEq O] in
lemma cfc_sqrt_eq {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    cfc Real.sqrt M = CFC.sqrt M := by
  rw [hM.isHermitian.cfc_eq]
  exact functional_sqrt hM

omit [Fintype O] [DecidableEq O] in
lemma sqrt_real_smul (a : ℝ) (ha : 0 ≤ a) {M : Matrix ι ι ℂ}
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

omit [Fintype O] [DecidableEq O] in
lemma sandwich_psd (M : Matrix ι ι ℂ) {N : Matrix ι ι ℂ} (hN : N.PosSemidef) :
    (CFC.sqrt M * N * CFC.sqrt M).PosSemidef := by
  have hs := (CFC.sqrt_nonneg M).posSemidef.isHermitian.eq
  simpa only [hs] using hN.conjTranspose_mul_mul_same (CFC.sqrt M)

omit [Fintype O] [DecidableEq O] in
lemma rootFidelity_eq {M N : Matrix ι ι ℂ} (hM : M.PosSemidef) (hN : N.PosSemidef) :
    rootFidelity M N = (CFC.sqrt (CFC.sqrt M * N * CFC.sqrt M)).trace.re := by
  unfold rootFidelity
  rw [cfc_sqrt_eq hM, cfc_sqrt_eq (sandwich_psd M hN)]

omit [Fintype O] [DecidableEq O] in
lemma weighted_fidelity (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {M N : Matrix ι ι ℂ} (hM : M.PosSemidef) (hN : N.PosSemidef) :
    rootFidelity ((a : ℂ) • M) ((b : ℂ) • N) =
      Real.sqrt (a * b) * rootFidelity M N := by
  rw [rootFidelity_eq (hM.smul (Complex.zero_le_real.mpr ha))
    (hN.smul (Complex.zero_le_real.mpr hb)), rootFidelity_eq hM hN,
    sqrt_real_smul a ha hM]
  have hscalar : (Real.sqrt a : ℂ)^2 = (a : ℂ) := by
    norm_cast
    exact Real.sq_sqrt ha
  have heq : ((Real.sqrt a : ℂ) • CFC.sqrt M) *
      ((b : ℂ) • N) * ((Real.sqrt a : ℂ) • CFC.sqrt M) =
      ((a*b : ℝ) : ℂ) • (CFC.sqrt M * N * CFC.sqrt M) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    push_cast
    calc
      _ = (Real.sqrt a : ℂ)^2 * (b : ℂ) := by ring
      _ = _ := by rw [hscalar]
  rw [heq, sqrt_real_smul _ (mul_nonneg ha hb) (sandwich_psd M hN), Matrix.trace_smul]
  simp

noncomputable def blockRow (W : O → Matrix ι ι ℂ) : Matrix ι (O × ι) ℂ :=
  fun a j => W j.1 a j.2

omit [DecidableEq O] [DecidableEq ι] in
lemma blockRow_square (W : O → Matrix ι ι ℂ) :
    blockRow W * (blockRow W)ᴴ = ∑ j, W j * (W j)ᴴ := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Fintype.sum_prod_type, blockRow]

omit [Fintype O] [DecidableEq O] [DecidableEq ι] in
lemma block_gram (W : O → Matrix ι ι ℂ) (i j : O) :
    block ((blockRow W)ᴴ * blockRow W) i j = (W i)ᴴ * W j := rfl

omit [Fintype O] [DecidableEq O] [DecidableEq ι] in
lemma block_sandwich (W : O → Matrix ι ι ℂ) (D : Matrix ι ι ℂ) (i j : O) :
    block ((blockRow W)ᴴ * D * blockRow W) i j = (W i)ᴴ * D * W j := rfl

omit [Fintype O] [DecidableEq O] in
lemma diagonal_frob (R D : Matrix ι ι ℂ) (hR : R.PosSemidef) (hD : D.IsHermitian) :
    frobSq ((CFC.sqrt R)ᴴ * D * CFC.sqrt R) = (D * R * D * R).trace.re := by
  let W := CFC.sqrt R
  have hW : Wᴴ = W := (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq
  have hWW : W * W = R := CFC.sqrt_mul_sqrt_self R hR.nonneg
  change frobSq (Wᴴ * D * W) = _
  rw [hW, frobSq_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hW, hD.eq]
  congr 1
  calc
    _ = (W * (D * W * W * D * W)).trace := by congr 1; noncomm_ring
    _ = ((D * W * W * D * W) * W).trace := Matrix.trace_mul_comm _ _
    _ = (D * (W * W) * D * (W * W)).trace := by congr 1; noncomm_ring
    _ = _ := by rw [hWW]

/-- The original PGM overlap bound, including singular average states. -/
theorem mixedPgmSuccess_bound (p : O → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (ρh : O → Matrix ι ι ℂ)
    (hρ : ∀ j, IsDensityMatrix (ρh j)) :
    1 - ∑ i, ∑ j ∈ Finset.univ.erase i,
        Real.sqrt (p i * p j) * rootFidelity (ρh i) (ρh j) ≤ mixedPgmSuccess p ρh := by
  let R : O → Matrix ι ι ℂ := fun j => (p j : ℂ) • ρh j
  have hR (j : O) : (R j).PosSemidef :=
    (hρ j).1.smul (Complex.zero_le_real.mpr (hp0 j))
  let W : O → Matrix ι ι ℂ := fun j => CFC.sqrt (R j)
  have hW (j : O) : (W j)ᴴ = W j := (CFC.sqrt_nonneg (R j)).posSemidef.isHermitian.eq
  have hWW (j : O) : W j * W j = R j := CFC.sqrt_mul_sqrt_self _ (hR j).nonneg
  let A := blockRow W
  let S := ∑ j, R j
  have hAS : A * Aᴴ = S := by
    rw [blockRow_square]
    simp_rw [hW, hWW]
    rfl
  let D := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) S
  let G := Aᴴ * D * A
  have hGS : G.PosSemidef ∧ G * G = Aᴴ * A := by
    simpa only [hAS] using positive_gram_square A
  have hD : D.PosSemidef := (inverse_support S (hAS ▸ posSemidef_self_mul_conjTranspose A)).1
  have htrace : S.trace = 1 := by
    simp only [S, R, Matrix.trace_sum, Matrix.trace_smul, (hρ _).2, smul_eq_mul, mul_one]
    norm_cast
  have htotal : frobSq G = 1 := by
    rw [frobSq_eq_trace, hGS.1.isHermitian.eq, hGS.2, Matrix.trace_mul_comm, hAS, htrace]
    simp
  have hdiag : (∑ j, frobSq (block G j j)) = mixedPgmSuccess p ρh := by
    change (∑ j, frobSq (block (Aᴴ * D * A) j j)) = ∑ j, (D * R j * D * R j).trace.re
    apply Finset.sum_congr rfl
    intro j _
    rw [block_sandwich]
    exact diagonal_frob (R j) D (hR j) hD.isHermitian
  have hsplit : frobSq G = (∑ j, frobSq (block G j j)) +
      ∑ i, ∑ j, if i = j then 0 else frobSq (block G i j) := by
    unfold frobSq
    simp only [Fintype.sum_prod_type, block]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    let f : O → ℝ := fun j => ∑ a, ∑ b, Complex.normSq (G (i,a) (j,b))
    change (∑ j, f j) = f i + ∑ j, if i = j then 0 else f j
    calc
      _ = ∑ j, ((if j = i then f i else 0) + (if i = j then 0 else f j)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j
        · subst j; simp
        · simp [h, Ne.symm h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hbound := offdiag_bound G hGS.1
  have hb (i j : O) :
      (CFC.sqrt ((block (G*G) i j)ᴴ * block (G*G) i j)).trace.re =
        Real.sqrt (p j * p i) * rootFidelity (ρh j) (ρh i) := by
    rw [hGS.2, block_gram]
    have heq : ((W i)ᴴ * W j)ᴴ * ((W i)ᴴ * W j) = W j * R i * W j := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hW, hW]
      calc
        _ = W j * (W i * W i) * W j := by noncomm_ring
        _ = _ := by rw [hWW]
    rw [heq]
    change (CFC.sqrt (CFC.sqrt (R j) * R i * CFC.sqrt (R j))).trace.re = _
    rw [← rootFidelity_eq (hR j) (hR i)]
    exact weighted_fidelity (p j) (p i) (hp0 j) (hp0 i) (hρ j).1 (hρ i).1
  simp_rw [hb] at hbound
  have hswap : (∑ i, ∑ j, if i = j then 0 else
      Real.sqrt (p j * p i) * rootFidelity (ρh j) (ρh i)) =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        Real.sqrt (p i * p j) * rootFidelity (ρh i) (ρh j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Finset.univ.erase i = Finset.univ.filter (fun j => j ≠ i) by
      ext j; simp]
    simp [Finset.sum_filter]
  rw [hswap] at hbound
  rw [hdiag, htotal] at hsplit
  change (∑ i, ∑ j, if i = j then 0 else frobSq (block G i j)) ≤ _ at hbound
  linarith

end BarnumKnillOverlap




/- Six finite spectral-calculus helpers reused from sometik179's accepted submission
090ebed5-52f3-4f18-8273-d47470c08eb3. The singular inverse_support proof is the
shared direct PGM1 proof, copied unchanged; only namespace/imports are changed. -/

open Matrix Unitary
open scoped MatrixOrder ComplexOrder BigOperators
namespace QAlgorithms.Papers.BarnumKnill02.CompletionSpectral
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

variable [DecidableEq R]

omit [Fintype C] [DecidableEq C] in
theorem inverse_support (M : Matrix R R ℂ) (hM : M.PosSemidef) :
    let D := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) M
    D.PosSemidef ∧ (1 - D * M * D).PosSemidef ∧ M * (1 - D * M * D) = 0 := by
  let h := hM.isHermitian
  let D := h.cfc (fun t => (Real.sqrt t)⁻¹)
  let E := h.cfc (fun t => if t = 0 then 0 else 1)
  have hD : D.PosSemidef := functional_pos h _ (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hDMD : D * M * D = E := by
    conv_lhs => lhs; rhs; rw [← functional_id h]
    rw [functional_mul, functional_mul]
    apply functional_congr
    intro i
    have ht := hM.eigenvalues_nonneg i
    by_cases hz : h.eigenvalues i = 0
    · simp [hz]
    · have hn : Real.sqrt (h.eigenvalues i) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm hz)))
      simp only [hz, if_false, id_eq]
      field_simp
      nlinarith [Real.sq_sqrt ht]
  have hE : (1 - E).PosSemidef := by
    rw [← functional_one h]
    change (h.cfc (fun _ => 1) - h.cfc (fun t => if t = 0 then 0 else 1)).PosSemidef
    rw [functional_sub]
    apply functional_pos
    intro i
    split_ifs <;> norm_num
  have hME : M * (1 - E) = 0 := by
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
  change (cfc (fun t : ℝ => (Real.sqrt t)⁻¹) M).PosSemidef ∧ _
  simp only [h.cfc_eq]
  change D.PosSemidef ∧ (1 - D * M * D).PosSemidef ∧ M * (1 - D * M * D) = 0
  exact ⟨hD, hDMD ▸ hE, hDMD ▸ hME⟩

end QAlgorithms.Papers.BarnumKnill02.CompletionSpectral



noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

namespace QAlgorithms.Papers.BarnumKnill02.CompletionProof

variable {O ι : Type*} [Fintype O] [DecidableEq O] [Fintype ι] [DecidableEq ι]

/- The following trace-positivity proof is reused verbatim, except its index name,
from sometik179's accepted submission 090ebed5-52f3-4f18-8273-d47470c08eb3
for QReversal.PGMBound.theorem_5. It has no full-rank hypothesis. -/
lemma trace_psd_product_nonneg {X Z : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (X*Z).trace.re := by
  have hs : (CFC.sqrt X).PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  have hp := hZ.mul_mul_conjTranspose_same (CFC.sqrt X)
  rw [hs.isHermitian.eq] at hp
  have ht := hp.trace_nonneg
  have heq : (CFC.sqrt X * Z * CFC.sqrt X).trace = (X*Z).trace := by
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self X hX.nonneg]
  rw [heq] at ht
  exact (Complex.nonneg_iff.mp ht).1


/-- Every positive subnormalized finite measurement can be completed by putting
its positive defect into a selected outcome. -/
lemma complete_subpovm (E : O → Matrix ι ι ℂ) (hE : ∀ j, (E j).PosSemidef)
    (hdef : (1 - ∑ j, E j).PosSemidef) (j0 : O) :
    ∃ M : O → Matrix ι ι ℂ, IsPOVM M ∧ ∀ j, (M j - E j).PosSemidef := by
  let M : O → Matrix ι ι ℂ := fun j => E j + if j = j0 then 1 - ∑ k, E k else 0
  refine ⟨M, ⟨?_, ?_⟩, ?_⟩
  · intro j
    dsimp [M]
    split_ifs
    · exact (hE j).add hdef
    · simpa using hE j
  · simp only [M, Finset.sum_add_distrib]
    simp
  · intro j
    dsimp [M]
    split_ifs
    · simpa using hdef
    · simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)

lemma effectProb_nonneg {E ρ : Matrix ι ι ℂ}
    (hE : E.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ effectProb E ρ :=
  trace_psd_product_nonneg hE hρ

lemma effectProb_mono {E F ρ : Matrix ι ι ℂ}
    (hEF : (F-E).PosSemidef) (hρ : ρ.PosSemidef) : effectProb E ρ ≤ effectProb F ρ := by
  have h := trace_psd_product_nonneg hEF hρ
  simpa only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, sub_nonneg, effectProb] using h

omit [DecidableEq O] in
lemma povm_effectProb_le_one (M : O → Matrix ι ι ℂ) (hM : IsPOVM M)
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) (j : O) : effectProb (M j) ρ ≤ 1 := by
  have hsum : ∑ k, effectProb (M k) ρ = 1 := by
    calc
      ∑ k, effectProb (M k) ρ = ((∑ k, M k) * ρ).trace.re := by
        simp only [effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
      _ = 1 := by rw [hM.2, Matrix.one_mul, hρ.2]; rfl
  rw [← hsum]
  exact Finset.single_le_sum (fun k _ => effectProb_nonneg (hM.1 k) hρ.1) (Finset.mem_univ j)

omit [DecidableEq O] in
lemma povm_score_le_one (p : O → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (ρh : O → Matrix ι ι ℂ) (hρ : ∀ j, IsDensityMatrix (ρh j))
    (M : O → Matrix ι ι ℂ) (hM : IsPOVM M) :
    (∑ j, p j * effectProb (M j) (ρh j)) ≤ 1 := by
  calc
    (∑ j, p j * effectProb (M j) (ρh j)) ≤ ∑ j, p j * 1 :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (povm_effectProb_le_one M hM (ρh j) (hρ j) j) (hp0 j)
    _ = 1 := by simpa using hp1

omit [DecidableEq O] in
lemma completed_score_ge (p : O → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (ρh : O → Matrix ι ι ℂ) (hρ : ∀ j, (ρh j).PosSemidef)
    (E M : O → Matrix ι ι ℂ) (hME : ∀ j, (M j-E j).PosSemidef) :
    (∑ j, p j * effectProb (E j) (ρh j)) ≤ ∑ j, p j * effectProb (M j) (ρh j) :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (effectProb_mono (hME j) (hρ j)) (hp0 j)

omit [DecidableEq O] in
lemma povm_score_le_mixedOptSuccess (p : O → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (ρh : O → Matrix ι ι ℂ)
    (hρ : ∀ j, IsDensityMatrix (ρh j)) (M : O → Matrix ι ι ℂ) (hM : IsPOVM M) :
    (∑ j, p j * effectProb (M j) (ρh j)) ≤ mixedOptSuccess p ρh := by
  unfold mixedOptSuccess
  apply le_ciSup (f := fun M : {M : O → Matrix ι ι ℂ // IsPOVM M} =>
    ∑ j, p j * effectProb (M.1 j) (ρh j)) ?_ ⟨M,hM⟩
  refine ⟨1, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact povm_score_le_one p hp0 hp1 ρh hρ N.1 N.2

end QAlgorithms.Papers.BarnumKnill02.CompletionProof



noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

namespace QAlgorithms.Papers.BarnumKnill02.CompletionProof

/-- The support-restricted PGM can be completed to a genuine POVM without
reducing its success, including singular average states and zero weights. -/
theorem mixedPgmSuccess_le_mixedOptSuccess {O ι : Type*}
    [Fintype O] [DecidableEq O] [Fintype ι] [DecidableEq ι]
    (p : O → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (ρh : O → Matrix ι ι ℂ) (hρ : ∀ j, IsDensityMatrix (ρh j)) :
    mixedPgmSuccess p ρh ≤ mixedOptSuccess p ρh := by
  let R : O → Matrix ι ι ℂ := fun j => (p j : ℂ) • ρh j
  have hR : ∀ j, (R j).PosSemidef := fun j =>
    (hρ j).1.smul (Complex.zero_le_real.mpr (hp0 j))
  let S : Matrix ι ι ℂ := ∑ j, R j
  have hS : S.PosSemidef := Matrix.posSemidef_sum Finset.univ (fun j _ => hR j)
  let D := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) S
  obtain ⟨hD, hdef, _⟩ := CompletionSpectral.inverse_support S hS
  let E : O → Matrix ι ι ℂ := fun j => D * R j * D
  have hE : ∀ j, (E j).PosSemidef := by
    intro j
    have h := (hR j).mul_mul_conjTranspose_same D
    have hDh : D.IsHermitian := hD.isHermitian
    simpa only [E, hDh.eq] using h
  have hsum : ∑ j, E j = D * S * D := by
    simp only [E, S, Matrix.mul_sum, Matrix.sum_mul]
  have hdefE : (1 - ∑ j, E j).PosSemidef := by
    rw [hsum]
    exact hdef
  have hO : Nonempty O := by
    by_contra h
    let : IsEmpty O := not_nonempty_iff.mp h
    simp at hp1
  obtain ⟨j0⟩ := hO
  obtain ⟨M, hM, hME⟩ := complete_subpovm E hE hdefE j0
  have hscore : mixedPgmSuccess p ρh = ∑ j, p j * effectProb (E j) (ρh j) := by
    change (∑ j, (E j * R j).trace.re) = _
    apply Finset.sum_congr rfl
    intro j _
    simp [R, effectProb, Matrix.trace_smul, Complex.mul_re]
  rw [hscore]
  exact (completed_score_ge p hp0 ρh (fun j => (hρ j).1) E M hME).trans
    (povm_score_le_mixedOptSuccess p hp0 hp1 ρh hρ M hM)

end QAlgorithms.Papers.BarnumKnill02.CompletionProof

open QAlgorithms

/-- The original reviewed Barnum–Knill mixed-state bound, with singular averages. -/
theorem solution {O ι : Type*} [Fintype O] [DecidableEq O] [Fintype ι]
    [DecidableEq ι] (p : O → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (ρh : O → Matrix ι ι ℂ) (hρ : ∀ j, IsDensityMatrix (ρh j)) :
    1 - ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt (p i * p j) * rootFidelity (ρh i) (ρh j) ≤
        mixedPgmSuccess p ρh ∧
      1 - ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt (p i * p j) * rootFidelity (ρh i) (ρh j) ≤
        mixedOptSuccess p ρh := by
  have h := BarnumKnillOverlap.mixedPgmSuccess_bound p hp0 hp1 ρh hρ
  exact ⟨h, h.trans
    (QAlgorithms.Papers.BarnumKnill02.CompletionProof.mixedPgmSuccess_le_mixedOptSuccess
      p hp0 hp1 ρh hρ)⟩
