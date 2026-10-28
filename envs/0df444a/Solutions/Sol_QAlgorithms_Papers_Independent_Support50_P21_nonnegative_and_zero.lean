-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P21.nonnegative_and_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:29:51.976752+00:00
-- url     : https://prove2.me/submissions/c4e73d57-5872-4c57-b00d-71a93bcb33a9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21


noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder

namespace X6D21

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P07

variable {J : Type} [Fintype J] [DecidableEq J]

lemma cfc_spec {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
  rw [hX.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma spec {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
  have hs := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  exact hs

lemma trace_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  rw [cfc_spec hX, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

lemma sq_eq_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    X * X = cfc (fun x : ℝ => x ^ 2) X := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  rw [cfc_spec hX]
  conv_lhs => rw [spec hX]
  set U := (hX.eigenvectorUnitary : Matrix J J ℂ)
  calc U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U *
        (U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U)
      = U * (Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * (star U * U) *
        Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 2; funext i; push_cast; ring

lemma traceNorm_herm {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    traceNorm X = ∑ i, |hX.eigenvalues i| := by
  rw [traceNorm, hX.eq, sq_eq_cfc hX, ← cfc_comp Real.sqrt (fun x : ℝ => x ^ 2) X]
  have : (Real.sqrt ∘ fun x : ℝ => x ^ 2) = fun x => |x| := by
    funext x; simp [Real.sqrt_sq_eq_abs]
  rw [this, trace_cfc hX, Complex.re_sum]
  simp

lemma effect_conj {P : Matrix J J ℂ} (hP : IsEffect P) (U : Matrix J J ℂ)
    (hU : star U * U = 1) : IsEffect (star U * P * U) := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using hP.1.conjTranspose_mul_mul_same U
  · have h := hP.2.conjTranspose_mul_mul_same U
    have e : Uᴴ * (1 - P) * U = 1 - star U * P * U := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hU]
    rwa [e] at h

/-- Effects have trace pairing with a Hermitian bounded by the trace norm. -/
theorem effect_le_traceNorm {P H : Matrix J J ℂ} (hP : IsEffect P) (hH : H.IsHermitian) :
    (P * H).trace.re ≤ traceNorm H := by
  set U : Matrix J J ℂ := (hH.eigenvectorUnitary : Matrix J J ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hH.eigenvectorUnitary).2
  set Q := star U * P * U
  have hQ : IsEffect Q := effect_conj hP U hU
  have e : (P * H).trace = (Q * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))).trace := by
    conv_lhs => rw [spec hH]
    simp only [Q, U]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
  rw [e, traceNorm_herm hH]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h0 : 0 ≤ Q i i := hQ.1.diag_nonneg
  have h1 : 0 ≤ (1 - Q) i i := hQ.2.diag_nonneg
  have h0' := Complex.nonneg_iff.mp h0
  have h1' := Complex.nonneg_iff.mp h1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h1'
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp at h1'
  rcases le_total 0 (hH.eigenvalues i) with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_nonpos h]; nlinarith

end X6D21


noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder MatrixOrder

namespace X6D21

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P07
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

variable {J : Type} [Fintype J] [DecidableEq J]

lemma tel_mul (A B : Matrix J J ℂ) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, map_mul]
  rfl

lemma tel_proj (S : Submodule ℂ (EuclideanSpace ℂ J)) :
    Matrix.toEuclideanLin (projection S) = S.starProjection.toLinearMap := by
  simp [projection]

lemma proj_herm (S : Submodule ℂ (EuclideanSpace ℂ J)) : (projection S).IsHermitian := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, tel_proj]
  exact S.starProjection_isSymmetric

lemma proj_idem (S : Submodule ℂ (EuclideanSpace ℂ J)) :
    projection S * projection S = projection S := by
  apply Matrix.toEuclideanLin.injective
  rw [tel_mul, tel_proj]
  ext1 x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Submodule.starProjection_eq_self_iff]
  exact Submodule.starProjection_apply_mem S x

lemma psd_of_proj {P : Matrix J J ℂ} (hH : P.IsHermitian) (hI : P * P = P) : P.PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hH.eq, hI] at this

lemma proj_mul_N (N : Matrix J J ℂ) :
    projection (operatorRange N) * N = N := by
  apply Matrix.toEuclideanLin.injective
  rw [tel_mul, tel_proj]
  ext1 x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Submodule.starProjection_eq_self_iff]
  exact LinearMap.mem_range_self _ x

lemma Bp_mul_proj (N Bp : Matrix J J ℂ) (h : Bp * N = 0) :
    Bp * projection (operatorRange N) = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [tel_mul, tel_proj, map_zero]
  ext1 x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply]
  obtain ⟨y, hy⟩ : (operatorRange N).starProjection x ∈ LinearMap.range (Matrix.toEuclideanLin N) :=
    Submodule.starProjection_apply_mem _ x
  rw [← hy, ← LinearMap.comp_apply, ← tel_mul, h, map_zero, LinearMap.zero_apply]

lemma tr_nonneg {A B : Matrix J J ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  have hA0 : (0 : Matrix J J ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hs : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have e : A = CFC.sqrt A * CFC.sqrt A := (CFC.sqrt_mul_sqrt_self A hA0).symm
  rw [e, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have := (hB.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg
  rw [hs.1.eq] at this
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp this).1

/-! ## support projections -/

lemma supp_herm (X : Matrix J J ℂ) : (support X).IsHermitian := proj_herm _

lemma supp_idem (X : Matrix J J ℂ) : support X * support X = support X := proj_idem _

lemma supp_psd (X : Matrix J J ℂ) : (support X).PosSemidef :=
  psd_of_proj (supp_herm X) (supp_idem X)

lemma supp_mul (X : Matrix J J ℂ) : support X * X = X := proj_mul_N X

lemma mul_supp {X : Matrix J J ℂ} (hX : X.IsHermitian) : X * support X = X := by
  have h := congrArg Matrix.conjTranspose (supp_mul X)
  rwa [Matrix.conjTranspose_mul, hX.eq, (supp_herm X).eq] at h

lemma compl_psd {P : Matrix J J ℂ} (hH : P.IsHermitian) (hI : P * P = P) :
    (1 - P).PosSemidef := by
  apply psd_of_proj
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, hH.eq]
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hI]; simp

lemma supp_effect (X : Matrix J J ℂ) : IsEffect (support X) :=
  ⟨supp_psd X, compl_psd (supp_herm X) (supp_idem X)⟩

lemma tr_eq (X : Matrix J J ℂ) : tr X = X.trace.re := rfl

lemma tr_supp (X : Matrix J J ℂ) : tr (support X * X) = tr X := by rw [supp_mul]

/-- `tr(Aρ) = 0` for PSD `A, ρ` forces `Aρ = 0`. -/
lemma mul_eq_zero_of_tr {A R : Matrix J J ℂ} (hA : A.PosSemidef) (hR : R.PosSemidef)
    (h : (A * R).trace.re = 0) : A * R = 0 := by
  have hA0 : (0 : Matrix J J ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hR0 : (0 : Matrix J J ℂ) ≤ R := Matrix.nonneg_iff_posSemidef.mpr hR
  set s := CFC.sqrt A
  set r := CFC.sqrt R
  have hs : s.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).1
  have hr : r.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg R)).1
  have eA : s * s = A := CFC.sqrt_mul_sqrt_self A hA0
  have eR : r * r = R := CFC.sqrt_mul_sqrt_self R hR0
  -- tr(A R) = tr((r s)ᴴ (r s))
  have key : (A * R).trace = ((r * s)ᴴ * (r * s)).trace := by
    rw [Matrix.conjTranspose_mul, hs.eq, hr.eq, ← eA, ← eR]
    calc (s * s * (r * r)).trace = (s * (s * r * r)).trace := by simp only [Matrix.mul_assoc]
      _ = (s * r * r * s).trace := Matrix.trace_mul_comm _ _
      _ = (s * r * (r * s)).trace := by simp only [Matrix.mul_assoc]
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self (r * s)
  have h0 : ((r * s)ᴴ * (r * s)).trace = 0 := by
    have hn := hpsd.trace_nonneg
    rw [← key] at hn ⊢
    apply Complex.ext
    · simpa using h
    · have := (Complex.nonneg_iff.mp hn).2
      simpa using this.symm
  rw [hpsd.trace_eq_zero_iff, Matrix.conjTranspose_mul_self_eq_zero] at h0
  -- R A = r (r s) s = 0
  have hRA : R * A = 0 := by
    rw [← eR, ← eA, Matrix.mul_assoc, ← Matrix.mul_assoc r s s, h0]; simp
  have := congrArg Matrix.conjTranspose hRA
  rwa [Matrix.conjTranspose_mul, hA.1.eq, hR.1.eq, Matrix.conjTranspose_zero] at this

/-- Optimal zero-type-I test. -/
lemma supp_le_effect {R P S : Matrix J J ℂ} (hR : R.PosSemidef) (hP : IsEffect P)
    (h : ((1 - P) * R).trace.re = 0) (hS : S.PosSemidef) :
    (support R * S).trace.re ≤ (P * S).trace.re := by
  have h1 : (1 - P) * R = 0 := mul_eq_zero_of_tr hP.2 hR h
  have h2 : (1 - P) * support R = 0 := Bp_mul_proj R (1 - P) h1
  have hPP : P * support R = support R := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h2; exact h2.symm
  have hPP' : support R * P = support R := by
    have := congrArg Matrix.conjTranspose hPP
    rwa [Matrix.conjTranspose_mul, hP.1.1.eq, (supp_herm R).eq] at this
  have e : P - support R = (1 - support R)ᴴ * P * (1 - support R) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (supp_herm R).eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP, hPP',
      supp_idem]
    abel
  have hD : (P - support R).PosSemidef := by
    rw [e]; exact hP.1.conjTranspose_mul_mul_same _
  have := tr_nonneg hD hS
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

/-! ## extended logs -/

lemma nelog_anti {x y : ℝ} (hxy : x ≤ y) : -elog y ≤ -elog x := by
  unfold elog
  by_cases hx : 0 < x
  · have hy : 0 < y := lt_of_lt_of_le hx hxy
    rw [if_pos hx, if_pos hy, EReal.neg_le_neg_iff, EReal.coe_le_coe_iff]
    exact Real.logb_le_logb_of_le (by norm_num) hx hxy
  · rw [if_neg hx]; simp

lemma nelog_le {x l : ℝ} (h : (2 : ℝ) ^ (-l) ≤ x) : -elog x ≤ (l : EReal) := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) h
  unfold elog
  rw [if_pos hx, ← EReal.coe_neg, EReal.coe_le_coe_iff, neg_le]
  rw [Real.le_logb_iff_rpow_le (by norm_num) hx]
  exact h

lemma nelog_nonneg {x : ℝ} (h : x ≤ 1) : 0 ≤ -elog x := by
  have := nelog_anti (y := 1) h
  simpa [elog] using (le_trans (by simp [elog]) this : (0 : EReal) ≤ -elog x) |>.trans le_rfl

end X6D21


noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder MatrixOrder

namespace X6D21

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P07
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

variable {J : Type} [Fintype J] [DecidableEq J]

lemma tr_supp_le (R : Matrix J J ℂ) {S : Matrix J J ℂ} (hS : S.PosSemidef) :
    (support R * S).trace.re ≤ S.trace.re := by
  have := tr_nonneg (compl_psd (supp_herm R) (supp_idem R)) hS
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma tr_compl_supp (R : Matrix J J ℂ) : ((1 - support R) * R).trace.re = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, supp_mul, sub_self]; simp

lemma dmax_le_of {R S : Matrix J J ℂ} {l : ℝ}
    (h : ((((2 : ℝ) ^ l : ℝ) : ℂ) • S - R).PosSemidef) : maxRelative R S ≤ (l : EReal) :=
  sInf_le ⟨l, rfl, h⟩

lemma le_dmax {R S : Matrix J J ℂ} {x : EReal}
    (h : ∀ l : ℝ, ((((2 : ℝ) ^ l : ℝ) : ℂ) • S - R).PosSemidef → x ≤ (l : EReal)) :
    x ≤ maxRelative R S :=
  le_sInf (by rintro v ⟨l, rfl, hl⟩; exact h l hl)

lemma feas_mono {R S : Matrix J J ℂ} (hS : S.PosSemidef) {l x : ℝ}
    (h : ((((2 : ℝ) ^ l : ℝ) : ℂ) • S - R).PosSemidef) (hlx : l ≤ x) :
    ((((2 : ℝ) ^ x : ℝ) : ℂ) • S - R).PosSemidef := by
  have e : (((2 : ℝ) ^ x : ℝ) : ℂ) • S - R =
      ((((2 : ℝ) ^ x - (2 : ℝ) ^ l : ℝ) : ℂ) • S) + ((((2 : ℝ) ^ l : ℝ) : ℂ) • S - R) := by
    rw [Complex.ofReal_sub, sub_smul]; abel
  rw [e]
  refine Matrix.PosSemidef.add ?_ h
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ x - (2 : ℝ) ^ l :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) hlx)
  have := hS.smul hc
  rw [Complex.coe_smul]; exact this

lemma trace_feas (R S P : Matrix J J ℂ) (l : ℝ) :
    (P * ((((2 : ℝ) ^ l : ℝ) : ℂ) • S - R)).trace.re =
      (2 : ℝ) ^ l * (P * S).trace.re - (P * R).trace.re := by
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re,
    smul_eq_mul, Complex.re_ofReal_mul]

/-- `Dmin ≤ Dmax` for `tr ρ = 1`. -/
lemma dmin_le_dmax {R S : Matrix J J ℂ} (hR1 : R.trace.re = 1) :
    -elog (tr (support R * S)) ≤ maxRelative R S := by
  apply le_dmax
  intro l hl
  apply nelog_le
  have h := tr_nonneg (supp_psd R) hl
  rw [trace_feas, supp_mul, hR1] at h
  have hp : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  rw [Real.rpow_neg (by norm_num)]
  change ((2 : ℝ) ^ l)⁻¹ ≤ (support R * S).trace.re
  rw [inv_le_iff_one_le_mul₀' hp]; linarith

lemma dmax_nonneg {R S : Matrix J J ℂ} (hR1 : R.trace.re = 1) (hS1 : S.trace.re = 1) :
    0 ≤ maxRelative R S := by
  apply le_dmax
  intro l hl
  have h := hl.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul] at h
  have h' := (Complex.nonneg_iff.mp h).1
  rw [Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul, hR1, hS1] at h'
  rw [EReal.coe_nonneg]
  by_contra hneg
  push Not at hneg
  have : (2 : ℝ) ^ l < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  linarith

lemma dmin_nonneg {R S : Matrix J J ℂ} (hS : S.PosSemidef) (hS1 : S.trace.re = 1) :
    0 ≤ -elog (tr (support R * S)) := by
  have h := nelog_anti (tr_supp_le R hS)
  rw [hS1] at h
  refine le_trans ?_ h
  simp [elog]

lemma dmin_self {R : Matrix J J ℂ} (hR1 : R.trace.re = 1) :
    -elog (tr (support R * R)) = 0 := by
  rw [tr_supp, tr_eq, hR1]; simp [elog]

end X6D21

noncomputable section

open QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- Lemma 6, PDF p.4: all clauses, without an incorrect converse for Dmin. -/
theorem solution (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    0 ≤ dMin rho sigma ∧ 0 ≤ maxRelative rho sigma ∧ dMin rho rho = 0 ∧ maxRelative rho rho = 0 ∧
    (support rho = support sigma → dMin rho sigma = 0) := by
  have h1 : rho.trace.re = 1 := by rw [hrho.2]; simp
  have h2 : sigma.trace.re = 1 := by rw [hsigma.2]; simp
  refine ⟨X6D21.dmin_nonneg hsigma.1 h2, X6D21.dmax_nonneg h1 h2, X6D21.dmin_self h1, ?_, ?_⟩
  · refine le_antisymm ?_ (X6D21.dmax_nonneg h1 h1)
    have := X6D21.dmax_le_of (R := rho) (S := rho) (l := 0) (by simp [Matrix.PosSemidef.zero])
    simpa using this
  · intro h
    show -elog (tr (support rho * sigma)) = 0
    rw [h]; exact X6D21.dmin_self h2

end Statements


end

