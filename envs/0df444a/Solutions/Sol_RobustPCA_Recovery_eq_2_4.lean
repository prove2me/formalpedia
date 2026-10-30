-- Prove2me | solution 1 for RobustPCA.Recovery.eq_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T09:14:33.210321+00:00
-- url     : https://prove2.me/submissions/53c033be-0157-4b0b-9e1f-5e7e6e8700ec

import Mathlib
import Definitions.Def_RobustPCA_Recovery_Setup
import Theorems.Thm_nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm
import Theorems.Thm_matrix_trace_duality_inequality

set_option autoImplicit false

open MatrixCompletion

namespace RPCA24

open RobustPCA.Recovery
open scoped BigOperators

/-! ## Projection algebra -/

/-- `∑_k u_k u_k^T` as a matrix. -/
noncomputable def projM {n r : ℕ} (u : Fin r → Fin n → ℝ) : RealMatrix n n :=
  fun i a => ∑ k, u k i * u k a

/-- `P_U` as a matrix. -/
noncomputable def PU {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.u

/-- `P_V` as a matrix. -/
noncomputable def PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.v

lemma tangent_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV X = PU SV * X + X * PV SV - PU SV * X * PV SV := by
  ext i j
  simp only [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, PU, PV, projM]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

lemma projM_transpose {n r : ℕ} (u : Fin r → Fin n → ℝ) : Matrix.transpose (projM u) = projM u := by
  ext i a
  simp only [Matrix.transpose_apply, projM]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

lemma projM_mul_vmv {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) (k : Fin r) (w : Fin n → ℝ) :
    projM u * Matrix.vecMulVec (u k) w = Matrix.vecMulVec (u k) w := by
  ext i j
  simp only [Matrix.mul_apply, projM, Matrix.vecMulVec_apply]
  have h1 : ∀ a, (∑ l, u l i * u l a) * (u k a * w j) = ∑ l, u l i * w j * (u l a * u k a) := by
    intro a
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hu]
  simp

lemma vmv_mul_projM {n r : ℕ} (v : Fin r → Fin n → ℝ)
    (hv : ∀ k l, ∑ i, v k i * v l i = if k = l then 1 else 0) (k : Fin r) (w : Fin n → ℝ) :
    Matrix.vecMulVec w (v k) * projM v = Matrix.vecMulVec w (v k) := by
  ext i j
  simp only [Matrix.mul_apply, projM, Matrix.vecMulVec_apply]
  have h1 : ∀ b, w i * v k b * (∑ l, v l b * v l j) = ∑ l, w i * v l j * (v k b * v l b) := by
    intro b
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hv]
  simp

lemma PU_mul_sign {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    PU SV * signMatrix SV = signMatrix SV := by
  unfold signMatrix PU
  rw [Matrix.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => projM_mul_vmv SV.u SV.u_orthonormal k (SV.v k))

lemma sign_mul_PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    signMatrix SV * PV SV = signMatrix SV := by
  unfold signMatrix PV
  rw [Matrix.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => vmv_mul_projM SV.v SV.v_orthonormal k (SV.u k))

lemma tangent_sign {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    tangentProjection SV (signMatrix SV) = signMatrix SV := by
  rw [tangent_eq, PU_mul_sign, sign_mul_PV]
  abel

/-! ## The Frobenius inner product -/

lemma inner_eq_trace {n : ℕ} (X Y : RealMatrix n n) : matrixInner X Y = (Matrix.transpose X * Y).trace := by
  simp only [matrixInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma inner_tangent {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    matrixInner (tangentProjection SV X) Y = matrixInner X (tangentProjection SV Y) := by
  rw [inner_eq_trace, inner_eq_trace, tangent_eq, tangent_eq]
  have hU : Matrix.transpose (PU SV) = PU SV := projM_transpose _
  have hV : Matrix.transpose (PV SV) = PV SV := projM_transpose _
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, hU, hV,
    Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_add, Matrix.mul_assoc]
  have e1 : (PV SV * (Matrix.transpose X * Y)).trace = (Matrix.transpose X * (Y * PV SV)).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have e2 : (PV SV * (Matrix.transpose X * (PU SV * Y))).trace = (Matrix.transpose X * (PU SV * (Y * PV SV))).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, e2]

lemma mi_add_left {n : ℕ} (X Y Z : RealMatrix n n) :
    matrixInner (X + Y) Z = matrixInner X Z + matrixInner Y Z := by
  simp only [matrixInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma mi_sub_left {n : ℕ} (X Y Z : RealMatrix n n) :
    matrixInner (X - Y) Z = matrixInner X Z - matrixInner Y Z := by
  simp only [matrixInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma mi_sub_right {n : ℕ} (X Y Z : RealMatrix n n) :
    matrixInner X (Y - Z) = matrixInner X Y - matrixInner X Z := by
  simp only [matrixInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma mi_smul_left {n : ℕ} (c : ℝ) (X Y : RealMatrix n n) :
    matrixInner (c • X) Y = c * matrixInner X Y := by
  simp only [matrixInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma mi_zero_left {n : ℕ} (Y : RealMatrix n n) : matrixInner 0 Y = 0 := by
  simp [matrixInner]

/-! ## Frobenius norm via `EuclideanSpace` -/

/-- A matrix as a vector of `EuclideanSpace ℝ (Fin n × Fin n)`. -/
noncomputable def toE {n : ℕ} (X : RealMatrix n n) : EuclideanSpace ℝ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => X p.1 p.2)

lemma toE_apply {n : ℕ} (X : RealMatrix n n) (p : Fin n × Fin n) : toE X p = X p.1 p.2 := rfl

lemma toE_add {n : ℕ} (X Y : RealMatrix n n) : toE (X + Y) = toE X + toE Y := by
  ext p
  simp [toE_apply]

lemma frob_toE {n : ℕ} (X : RealMatrix n n) : frobeniusNorm X = ‖toE X‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold frobeniusNorm frobeniusNormSq
  congr 1
  rw [Fintype.sum_prod_type]
  simp [toE_apply, sq_abs]

lemma inner_toE {n : ℕ} (X Y : RealMatrix n n) :
    matrixInner X Y = inner ℝ (toE X) (toE Y) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [matrixInner, toE_apply, mul_comm]

lemma frob_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _

lemma frob_add {n : ℕ} (X Y : RealMatrix n n) :
    frobeniusNorm (X + Y) ≤ frobeniusNorm X + frobeniusNorm Y := by
  rw [frob_toE, frob_toE, frob_toE, toE_add]
  exact norm_add_le _ _

lemma abs_inner_le {n : ℕ} (X Y : RealMatrix n n) :
    |matrixInner X Y| ≤ frobeniusNorm X * frobeniusNorm Y := by
  rw [inner_toE, frob_toE, frob_toE]
  exact abs_real_inner_le_norm _ _

lemma eq_zero_of_frob {n : ℕ} (X : RealMatrix n n) (h : frobeniusNorm X ≤ 0) : X = 0 := by
  have h0 : ‖toE X‖ = 0 := le_antisymm (frob_toE X ▸ h) (norm_nonneg _)
  rw [norm_eq_zero] at h0
  ext i j
  have := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n) => v (i, j)) h0
  simpa [toE_apply] using this

lemma abs_le_l1 {n : ℕ} (X : RealMatrix n n) (i j : Fin n) : |X i j| ≤ l1Norm X := by
  unfold l1Norm
  calc |X i j| ≤ ∑ j', |X i j'| :=
        Finset.single_le_sum (f := fun j' => |X i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |X i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |X i' j'|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)

lemma l1_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ l1Norm X :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

lemma frob_le_l1 {n : ℕ} (X : RealMatrix n n) : frobeniusNorm X ≤ l1Norm X := by
  unfold frobeniusNorm
  rw [← Real.sqrt_sq (l1_nonneg X)]
  apply Real.sqrt_le_sqrt
  unfold frobeniusNormSq
  calc ∑ i, ∑ j, X i j ^ 2 ≤ ∑ i, ∑ j, |X i j| * l1Norm X := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [← sq_abs, sq]
        exact mul_le_mul_of_nonneg_left (abs_le_l1 X i j) (abs_nonneg _)
    _ = l1Norm X ^ 2 := by
        rw [sq]
        unfold l1Norm
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])

/-! ## Spectral and nuclear norms -/

lemma spectral_le_frob {n : ℕ} (X : RealMatrix n n) :
    MatrixCompletion.spectralNorm X ≤ frobeniusNorm X := by
  unfold MatrixCompletion.spectralNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (frob_nonneg X) (fun v => ?_)
  rw [LinearMap.coe_toContinuousLinearMap']
  change ‖(WithLp.toLp 2 (Matrix.mulVec X (WithLp.ofLp v)) : EuclideanSpace ℝ (Fin n))‖ ≤ _
  have h0 : 0 ≤ frobeniusNormSq X := by unfold frobeniusNormSq; positivity
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, frobeniusNorm, ← Real.sqrt_mul h0]
  apply Real.sqrt_le_sqrt
  simp only [Real.norm_eq_abs, sq_abs]
  unfold frobeniusNormSq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma nuc_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ nuclearNorm X := by
  unfold nuclearNorm Finsupp.sum
  exact Finset.sum_nonneg (fun i _ => LinearMap.singularValues_nonneg _ i)

lemma frob_le_nuc {n : ℕ} (X : RealMatrix n n) : frobeniusNorm X ≤ nuclearNorm X := by
  have hd := matrix_trace_duality_inequality X X
  have hs := spectral_le_frob X
  have hn := nuc_nonneg X
  have hf := frob_nonneg X
  have hXX : matrixInner X X = frobeniusNorm X ^ 2 := by
    have h0 : 0 ≤ frobeniusNormSq X := by unfold frobeniusNormSq; positivity
    rw [frobeniusNorm, Real.sq_sqrt h0]
    simp only [matrixInner, frobeniusNormSq, sq]
  rcases eq_or_lt_of_le hf with h0 | hpos
  · rw [← h0]; exact hn
  · have h2 : frobeniusNorm X ^ 2 ≤ frobeniusNorm X * nuclearNorm X :=
      hXX ▸ hd.trans (mul_le_mul_of_nonneg_right hs hn)
    nlinarith

/-! ## Entrywise facts about `Ω = supp S0` -/

lemma sampling_add {n : ℕ} (Ω : Finset (Fin n × Fin n)) (A B : RealMatrix n n) :
    samplingProjection Ω (A + B) = samplingProjection Ω A + samplingProjection Ω B := by
  ext i j
  simp only [samplingProjection, Matrix.add_apply]
  split_ifs <;> simp

lemma frob_sampling_le {n : ℕ} (Ω : Finset (Fin n × Fin n)) (X : RealMatrix n n) :
    frobeniusNorm (samplingProjection Ω X) ≤ frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  simp only [samplingProjection]
  split_ifs
  · exact le_rfl
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; exact sq_nonneg _

lemma split_P {n : ℕ} (Ω : Finset (Fin n × Fin n)) (X : RealMatrix n n) :
    X = samplingProjection Ω X + compProj Ω X := by
  simp [compProj]

lemma inner_split {n : ℕ} (Ω : Finset (Fin n × Fin n)) (Z H : RealMatrix n n) :
    matrixInner Z H = matrixInner (samplingProjection Ω Z) (samplingProjection Ω H) +
      matrixInner (compProj Ω Z) H := by
  simp only [matrixInner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [compProj, samplingProjection, Matrix.sub_apply]
  split_ifs <;> ring

lemma comp_sgn {n : ℕ} (S0 E W : RealMatrix n n) (lam : ℝ) :
    compProj (supp S0) (E - lam • sgnMatrix S0 + W) = compProj (supp S0) (E + W) := by
  ext i j
  simp only [compProj, samplingProjection, supp, Finset.mem_filter, Finset.mem_univ, true_and,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sgnMatrix]
  by_cases h : S0 i j = 0
  · simp [h]
  · simp [h]

lemma l1_lower {n : ℕ} (S0 H : RealMatrix n n) :
    l1Norm S0 - matrixInner (sgnMatrix S0) H + l1Norm (compProj (supp S0) H) ≤
      l1Norm (S0 - H) := by
  unfold l1Norm matrixInner
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  simp only [compProj, samplingProjection, supp, Finset.mem_filter, Finset.mem_univ, true_and,
    Matrix.sub_apply, sgnMatrix]
  by_cases h : S0 i j = 0
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, if_true, sub_self, abs_zero, add_zero]
    rcases lt_or_gt_of_ne h with hs | hs
    · rw [Real.sign_of_neg hs, abs_of_neg hs]
      linarith [neg_abs_le (S0 i j - H i j)]
    · rw [Real.sign_of_pos hs, abs_of_pos hs]
      linarith [le_abs_self (S0 i j - H i j)]

lemma entrySup_nonneg {n : ℕ} (A : RealMatrix n n) : 0 ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))

lemma le_entrySup {n : ℕ} (A : RealMatrix n n) (i j : Fin n) : |A i j| ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact le_ciSup_of_le (Finite.bddAbove_range _) i
    (le_ciSup (f := fun j => |A i j|) (Finite.bddAbove_range _) j)

lemma off_lower {n : ℕ} (Ω : Finset (Fin n × Fin n)) (Y H : RealMatrix n n) :
    -(entrySupNorm (compProj Ω Y) * l1Norm (compProj Ω H)) ≤ matrixInner (compProj Ω Y) H := by
  unfold l1Norm matrixInner
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum; intro j _
  have hy := le_entrySup (compProj Ω Y) i j
  have heq : compProj Ω Y i j * H i j = compProj Ω Y i j * compProj Ω H i j := by
    simp only [compProj, samplingProjection, Matrix.sub_apply]
    split_ifs <;> ring
  rw [heq]
  have h1 := neg_abs_le (compProj Ω Y i j * compProj Ω H i j)
  rw [abs_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right hy (abs_nonneg (compProj Ω H i j))
  linarith

end RPCA24

open RPCA24 MatrixCompletion RobustPCA.Recovery in
theorem solution {n r : ℕ} (lam : ℝ) (L0 S0 : RealMatrix n n) (SV : SVD L0 r)
    (W : RealMatrix n n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hΩT : PTOpNormLe (supp S0) SV (1 / 2))
    (hWT : tangentProjection SV W = 0) (hW : spectralNorm W < 1 / 2)
    (hΩ : frobeniusNorm (samplingProjection (supp S0) (signMatrix SV - lam • sgnMatrix S0 + W))
      ≤ lam / 4)
    (hΩc : entrySupNorm (compProj (supp S0) (signMatrix SV + W)) < lam / 2) :
    IsPCPExact lam L0 S0 := by
  intro L S hLS hne
  have hL : L = L0 + (L - L0) := by abel
  have hS : S = S0 - (L - L0) := by
    have h' : S = L0 + S0 - L := by rw [← hLS]; abel
    rw [h']; abel
  have hH0 : L - L0 ≠ 0 := by
    intro h0
    apply hne
    rw [hL, hS, h0]
    simp
  rw [hL, hS]
  generalize L - L0 = H at hH0 ⊢
  -- notation
  set E := signMatrix SV with hEdef
  set Ω := supp S0 with hΩdef
  set B := normalProjection SV H with hBdef
  -- (1) subgradient bound for the nuclear norm (child)
  have h1 := nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm SV H
  have hE : matrixInner E (tangentProjection SV H) = matrixInner E H := by
    rw [← inner_tangent, tangent_sign]
  rw [hE] at h1
  -- (2) the l1 bound
  have h2 := l1_lower S0 H
  -- (3) `⟨W, H⟩ ≤ ‖B‖_* / 2`
  have hWB : matrixInner W H = matrixInner W B := by
    rw [hBdef, normalProjection, mi_sub_right, ← inner_tangent, hWT, mi_zero_left, sub_zero]
  have hnB := nuc_nonneg B
  have hWH : matrixInner W H ≤ 1 / 2 * nuclearNorm B := by
    rw [hWB]
    have hd := matrix_trace_duality_inequality W B
    have : MatrixCompletion.spectralNorm W * nuclearNorm B ≤ 1 / 2 * nuclearNorm B :=
      mul_le_mul_of_nonneg_right hW.le hnB
    linarith
  -- (4) split the certificate pairing over `Ω` and `Ωᶜ`
  set Z := E - lam • sgnMatrix S0 + W with hZdef
  have hZ : matrixInner Z H =
      matrixInner E H - lam * matrixInner (sgnMatrix S0) H + matrixInner W H := by
    rw [hZdef, mi_add_left, mi_sub_left, mi_smul_left]
  have hsplit := inner_split Ω Z H
  rw [hΩdef, comp_sgn S0 E W lam, ← hΩdef] at hsplit
  have h3 : -(lam / 4 * frobeniusNorm (samplingProjection Ω H)) ≤
      matrixInner (samplingProjection Ω Z) (samplingProjection Ω H) := by
    have ha := abs_inner_le (samplingProjection Ω Z) (samplingProjection Ω H)
    have hb := mul_le_mul_of_nonneg_right hΩ (frob_nonneg (samplingProjection Ω H))
    have hc := neg_abs_le (matrixInner (samplingProjection Ω Z) (samplingProjection Ω H))
    linarith
  have h4 := off_lower Ω (E + W) H
  -- (5) Frobenius bookkeeping
  have hT := hΩT H
  have hHB : H = tangentProjection SV H + B := by rw [hBdef, normalProjection]; abel
  have hPH : frobeniusNorm (samplingProjection Ω H) ≤
      frobeniusNorm (samplingProjection Ω (tangentProjection SV H)) + frobeniusNorm B := by
    have := frob_add (samplingProjection Ω (tangentProjection SV H)) (samplingProjection Ω B)
    rw [← sampling_add, ← hHB] at this
    linarith [frob_sampling_le Ω B]
  have hHf : frobeniusNorm H ≤ frobeniusNorm (samplingProjection Ω H) +
      frobeniusNorm (compProj Ω H) := by
    have := frob_add (samplingProjection Ω H) (compProj Ω H)
    rwa [← split_P] at this
  have heB := frob_le_nuc B
  have hgC := frob_le_l1 (compProj Ω H)
  have hc0 := entrySup_nonneg (compProj Ω (E + W))
  have hb0 := l1_nonneg (compProj Ω H)
  have hf0 := frob_nonneg (samplingProjection Ω H)
  have he0 := frob_nonneg B
  have hg0 := frob_nonneg (compProj Ω H)
  have hh0 := frob_nonneg H
  -- f ≤ b + 2a
  have hfb : frobeniusNorm (samplingProjection Ω H) ≤
      l1Norm (compProj Ω H) + 2 * nuclearNorm B := by linarith
  by_contra hcon
  push Not at hcon
  have hlb := mul_le_mul_of_nonneg_left h2 hlam0.le
  have hl4 := mul_le_mul_of_nonneg_left hfb (by linarith : (0 : ℝ) ≤ lam / 4)
  have hcb := mul_le_mul_of_nonneg_right hΩc.le hb0
  -- 0 ≥ a (1 - lam) / 2 + b lam / 4
  have key : nuclearNorm B * (1 - lam) / 2 + l1Norm (compProj Ω H) * (lam / 4) ≤ 0 := by
    nlinarith
  have ha : nuclearNorm B ≤ 0 := by
    by_contra hp; push Not at hp
    have : 0 < nuclearNorm B * (1 - lam) / 2 := by
      have : 0 < 1 - lam := by linarith
      positivity
    nlinarith [mul_nonneg hb0 (by linarith : (0 : ℝ) ≤ lam / 4)]
  have hb : l1Norm (compProj Ω H) ≤ 0 := by
    by_contra hp; push Not at hp
    have : 0 < l1Norm (compProj Ω H) * (lam / 4) := by positivity
    nlinarith [mul_nonneg hnB (by linarith : (0 : ℝ) ≤ (1 - lam) / 2)]
  apply hH0
  apply eq_zero_of_frob
  linarith
