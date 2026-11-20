-- Prove2me | solution 1 for SqrtQueries.pure_traceDist_le
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-19T22:05:29.81817+00:00
-- url     : https://prove2.me/submissions/98273bfd-0fb2-4be5-ae57-6fd17e1aaf0a

import Definitions.Def_WildeQIT_Gentle_postMeasurementState
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_traceNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq

noncomputable section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.RecoveryMatrixSVD
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Square SVD tied to the exact Gram spectral calculus; no rank assumption. -/
theorem gram_svd (A : Matrix n n ℂ) :
    ∃ (U V : unitary (Matrix n n ℂ)) (s : n → ℝ),
      (∀ i, 0 ≤ s i) ∧
      A=(U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ) ∧
      (∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
        (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) := by
  classical
  let hG := posSemidef_conjTranspose_mul_self A
  let Q := hG.isHermitian.eigenvectorUnitary
  let s : n → ℝ := fun i => Real.sqrt (hG.isHermitian.eigenvalues i)
  have hs (i : n) : 0 ≤ s i := Real.sqrt_nonneg _
  have hsq (i : n) : s i^2 = hG.isHermitian.eigenvalues i := Real.sq_sqrt (hG.eigenvalues_nonneg i)
  let D : Matrix n n ℂ := diagonal (fun i => (s i : ℂ))
  let B : Matrix n n ℂ := D*(Q : Matrix n n ℂ)ᴴ
  have hD : Dᴴ=D := by simp [D,diagonal_conjTranspose]
  have hB : Bᴴ*B=Aᴴ*A := by
    dsimp [B]
    rw [conjTranspose_mul,conjTranspose_conjTranspose,hD]
    rw [Matrix.mul_assoc,← Matrix.mul_assoc D D]
    have hd : D*D=diagonal (fun i => (hG.isHermitian.eigenvalues i : ℂ)) := by
      dsimp [D]
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      exact_mod_cast (show s i*s i=hG.isHermitian.eigenvalues i by simpa only [pow_two] using hsq i)
    rw [hd]
    rw [← Matrix.mul_assoc]
    exact hG.isHermitian.spectral_theorem.symm
  obtain ⟨W,hW,hh⟩ := WildeQIT.Purification.exists_unitary_eq_mul_of_mul_conjTranspose_eq Aᴴ Bᴴ
    (by simpa only [conjTranspose_conjTranspose] using hB.symm)
  let U : unitary (Matrix n n ℂ) := star ⟨W,hW⟩
  let V : unitary (Matrix n n ℂ) := star Q
  refine ⟨U,V,s,hs,?_,?_⟩
  · have hh' := congrArg conjTranspose hh
    simpa only [U,V,B,conjTranspose_conjTranspose,conjTranspose_mul,
      Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.mul_assoc] using hh'
  · intro f
    rw [hG.isHermitian.cfc_eq,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    dsimp [V,Q]
    simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_conjTranspose]
    congr 2
    ext i j
    simp [diagonal_apply,hsq]

end QValue20Support.RecoveryMatrixSVD

end

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.RecoverySchatten
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_gram_cfc (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ))
    (f : ℝ → ℝ) : (cfc f (Aᴴ*A)).trace.re=∑ i, f (s i^2) := by
  rw [hcalc,trace_mul_cycle]
  have hVV : (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 := Unitary.coe_mul_star_self V
  rw [hVV,Matrix.one_mul,trace_diagonal]
  simp

lemma schatten_finite (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ))
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    schattenNorm p A = (∑ i, (s i)^p.toReal)^(1/p.toReal) := by
  rw [schattenNorm,if_neg hp,trace_gram_cfc A V s hcalc]
  simp only [Real.rpow_eq_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.rpow_natCast,← Real.rpow_mul (hs i)]
  congr 1
  ring

lemma schatten_two (A : Matrix n n ℂ) :
    schattenNorm 2 A = Real.sqrt ((Aᴴ*A).trace.re) := by
  rw [schattenNorm,if_neg (by simp),ENNReal.toReal_ofNat]
  simp only [Real.rpow_eq_pow]
  norm_num only [show (2 : ℝ)/2=1 by norm_num,Real.rpow_one]
  change (cfc id (Aᴴ*A)).trace.re^(1/2 : ℝ)=Real.sqrt ((Aᴴ*A).trace.re)
  have hG : IsSelfAdjoint (Aᴴ*A) := (posSemidef_conjTranspose_mul_self A).isHermitian
  rw [cfc_id ℝ (Aᴴ*A)]
  exact (Real.sqrt_eq_rpow _).symm

lemma schatten_one_svd (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) :
    schattenNorm 1 A = ∑ i, s i := by
  rw [schatten_finite A V s hs hcalc 1 (by simp)]
  simp

lemma schatten_one_nonneg (A : Matrix n n ℂ) : 0 ≤ schattenNorm 1 A := by
  obtain ⟨U,V,s,hs,_,hcalc⟩ := QValue20Support.RecoveryMatrixSVD.gram_svd A
  rw [schatten_one_svd A V s hs hcalc]
  exact Finset.sum_nonneg fun i _ => hs i

end QValue20Support.RecoverySchatten

end

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.RecoveryTraceBounds
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma entry_le_opNorm (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have hh := (PiLp.norm_apply_le ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A) e) i).trans
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).le_opNorm e)
  have he : ‖e‖=1 := by simp [e]
  have hval : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A) e) i = A i j := by
    change (A *ᵥ Pi.single j (1 : ℂ)) i = A i j
    simp
  rw [hval,Matrix.l2_opNorm_toEuclideanCLM,he,mul_one] at hh
  exact hh

lemma gram_trace (A : Matrix n n ℂ) : (Aᴴ*A).trace.re=∑ i, ∑ j, ‖A i j‖^2 := by
  change (∑ i, ∑ j, star (A j i)*A j i).re=∑ i, ∑ j, ‖A i j‖^2
  simp only [Complex.re_sum]
  have hterm (z : ℂ) : (star z*z).re=‖z‖^2 := by
    change (conj z*z).re=‖z‖^2
    rw [← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  simp_rw [hterm]
  exact Finset.sum_comm

lemma trace_diagonal_mul (X : Matrix n n ℂ) (s : n → ℂ) :
    (X*diagonal s).trace=∑ i, X i i*s i := by
  simp [Matrix.trace,Matrix.diag]

lemma trace_op_trace_bound (X A : Matrix n n ℂ) :
    ‖(X*A).trace‖ ≤ ‖X‖*schattenNorm 1 A := by
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := QValue20Support.RecoveryMatrixSVD.gram_svd A
  rw [QValue20Support.RecoverySchatten.schatten_one_svd A V s hs hcalc]
  have ht : (X*A).trace = ((V : Matrix n n ℂ)*X*(U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))).trace := by
    rw [hA,← Matrix.mul_assoc,trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [ht,trace_diagonal_mul]
  calc
    _ ≤ ∑ i, ‖((V : Matrix n n ℂ)*X*(U : Matrix n n ℂ)) i i*(s i : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖X‖*s i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hs i)]
      apply mul_le_mul_of_nonneg_right _ (hs i)
      exact (entry_le_opNorm _ i i).trans_eq (by
        rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul])
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma trace_hilbert_schmidt_bound (X A : Matrix n n ℂ) :
    ‖(X*A).trace‖ ≤ schattenNorm 2 X*schattenNorm 2 A := by
  rw [QValue20Support.RecoverySchatten.schatten_two,QValue20Support.RecoverySchatten.schatten_two,gram_trace,gram_trace]
  have ht : (X*A).trace = ∑ p : n×n, X p.1 p.2*A p.2 p.1 := by
    simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type]
  rw [ht]
  calc
    _ ≤ ∑ p : n×n, ‖X p.1 p.2*A p.2 p.1‖ := norm_sum_le _ _
    _ = ∑ p : n×n, ‖X p.1 p.2‖*‖A p.2 p.1‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ p : n×n, ‖X p.1 p.2‖^2)*Real.sqrt (∑ p : n×n, ‖A p.2 p.1‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp only [Fintype.sum_prod_type]; rw [Finset.sum_comm (f := fun i j => ‖A j i‖^2)]

end QValue20Support.RecoveryTraceBounds

end

noncomputable section
open Matrix Unitary WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.QuantumValueTrace
variable {n : Type} [Fintype n] [DecidableEq n]

lemma schatten_bridge (A : Matrix n n ℂ) :
    QAlgorithms.Papers.Independent.Information100.P50.schattenNorm 1 A=traceNorm A := by
  rw [QAlgorithms.Papers.Independent.Information100.P50.schattenNorm,
    if_neg (by simp),ENNReal.toReal_one,div_one]
  simp only [Real.rpow_eq_pow,Real.rpow_one]
  unfold traceNorm
  rw [CFC.sqrt_eq_rpow,CFC.rpow_eq_cfc_real (posSemidef_conjTranspose_mul_self A).nonneg]

lemma trace_bound (A B : Matrix n n ℂ) : ‖(A*B).trace‖ ≤ ‖A‖*traceNorm B := by
  simpa only [schatten_bridge] using
    QValue20Support.RecoveryTraceBounds.trace_op_trace_bound A B

lemma traceNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ traceNorm A := by
  rw [← schatten_bridge]
  exact QValue20Support.RecoverySchatten.schatten_one_nonneg A

lemma traceNorm_svd (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A)=
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) :
    traceNorm A=∑ i, s i := by
  rw [← schatten_bridge]
  exact QValue20Support.RecoverySchatten.schatten_one_svd A V s hs hc

lemma norm_unitary_le_one (U : unitary (Matrix n n ℂ)) : ‖(U : Matrix n n ℂ)‖ ≤ 1 := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    haveI := hn
    have hU : (U : Matrix n n ℂ)=0 := Subsingleton.elim _ _
    rw [hU,norm_zero]
    exact zero_le_one
  | inr hn =>
    haveI := hn
    exact (CStarRing.norm_coe_unitary U).le

lemma trace_unitary_bound (A : Matrix n n ℂ) (U : unitary (Matrix n n ℂ)) :
    ‖(A*(U : Matrix n n ℂ)).trace‖ ≤ traceNorm A := by
  rw [trace_mul_comm]
  exact (trace_bound _ A).trans ((mul_le_mul_of_nonneg_right
    (norm_unitary_le_one U) (traceNorm_nonneg A)).trans_eq (one_mul _))

lemma variational (A : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ U ∈ Matrix.unitaryGroup n ℂ, x=‖(A*U).trace‖} (traceNorm A) := by
  classical
  obtain ⟨U,V,s,hs,hA,hc⟩ := QValue20Support.RecoveryMatrixSVD.gram_svd A
  let W : unitary (Matrix n n ℂ) := star V*star U
  have hVV : (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 := Unitary.coe_mul_star_self V
  have hUU : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  have hw : (A*(W : Matrix n n ℂ)).trace=(∑ i, s i : ℝ) := by
    rw [hA]
    change (((U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ))*
      ((V : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)ᴴ)).trace=_
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V : Matrix n n ℂ),hVV,Matrix.one_mul]
    rw [← Matrix.mul_assoc,trace_mul_cycle,hUU,Matrix.one_mul,trace_diagonal]
    simp
  refine ⟨?_,?_⟩
  · refine ⟨W,W.property,?_⟩
    rw [hw,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _ => hs i))]
    exact traceNorm_svd A V s hs hc
  · rintro x ⟨W,hW,rfl⟩
    exact trace_unitary_bound A ⟨W,hW⟩

lemma triangle (A B : Matrix n n ℂ) : traceNorm (A+B) ≤ traceNorm A+traceNorm B := by
  obtain ⟨W,hW,h⟩ := (variational (A+B)).1
  rw [h,Matrix.add_mul,trace_add]
  exact (norm_add_le _ _).trans (add_le_add (trace_unitary_bound A ⟨W,hW⟩)
    (trace_unitary_bound B ⟨W,hW⟩))

lemma contraction_norm (A : Matrix n n ℂ) (hA : Aᴴ*A ≤ 1) : ‖A‖ ≤ 1 := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    haveI := hn
    have hz : A=0 := Subsingleton.elim _ _
    rw [hz,norm_zero]
    exact zero_le_one
  | inr hn =>
    haveI := hn
    have hg := (CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ*A)
      (posSemidef_conjTranspose_mul_self A).nonneg).mpr hA
    have he : ‖Aᴴ*A‖=‖A‖*‖A‖ := CStarRing.norm_star_mul_self
    rw [he] at hg
    nlinarith [norm_nonneg A]

lemma contraction_trace (X A : Matrix n n ℂ) (hA : Aᴴ*A ≤ 1) :
    ‖(X*A).trace‖ ≤ traceNorm X := by
  rw [trace_mul_comm]
  exact (trace_bound A X).trans ((mul_le_mul_of_nonneg_right (contraction_norm A hA)
    (traceNorm_nonneg X)).trans_eq (one_mul _))

end QValue20Support.QuantumValueTrace

end

open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

noncomputable section
open Matrix Unitary WildeQIT QValue20Support.QuantumValueTrace
open QAlgorithms.Papers.Independent.Information100.P50
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace QValue20Support.QuantumValueGentle
variable {n : Type} [Fintype n] [DecidableEq n]

lemma sqrt_star (A : Matrix n n ℂ) : (CFC.sqrt A)ᴴ=CFC.sqrt A := by
  change star (CFC.sqrt A)=CFC.sqrt A
  exact (CFC.sqrt_nonneg A).star_eq

lemma hs_unitary (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    schattenNorm 2 ((U : Matrix n n ℂ)*A)=schattenNorm 2 A := by
  have hU : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  rw [QValue20Support.RecoverySchatten.schatten_two,QValue20Support.RecoverySchatten.schatten_two]
  congr 2
  rw [conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),hU,Matrix.one_mul]

lemma product_bound (X Y : Matrix n n ℂ) :
    traceNorm (X*Y) ≤ schattenNorm 2 X*schattenNorm 2 Y := by
  obtain ⟨U,hU,hu⟩ := (variational (X*Y)).1
  rw [hu]
  have ht : ((X*Y)*U).trace=((U*X)*Y).trace := trace_mul_cycle X Y U
  rw [ht]
  exact (QValue20Support.RecoveryTraceBounds.trace_hilbert_schmidt_bound (U*X) Y).trans_eq
    (by rw [hs_unitary ⟨U,hU⟩ X])

lemma hs_adjoint (A : Matrix n n ℂ) : schattenNorm 2 Aᴴ=schattenNorm 2 A := by
  rw [QValue20Support.RecoverySchatten.schatten_two,QValue20Support.RecoverySchatten.schatten_two,
    conjTranspose_conjTranspose,trace_mul_comm A Aᴴ]

lemma positive_product_trace (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  have hh := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [sqrt_star,trace_mul_cycle,CFC.sqrt_mul_sqrt_self A hA.nonneg] at hh
  exact (Complex.nonneg_iff.mp hh).1

lemma gentle (ρ L : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hL : L.PosSemidef) (hLI : (1-L).PosSemidef) (ε : ℝ) (hε : 0 ≤ ε)
    (hdet : 1-ε ≤ (L*ρ).trace.re) :
    traceNorm (ρ-CFC.sqrt L*ρ*CFC.sqrt L) ≤ 2*Real.sqrt ε := by
  let S := CFC.sqrt L
  let T := CFC.sqrt ρ
  have hS : Sᴴ=S := sqrt_star L
  have hT : Tᴴ=T := sqrt_star ρ
  have hS2 : S*S=L := CFC.sqrt_mul_sqrt_self L hL.nonneg
  have hT2 : T*T=ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg L
  have hS1 : S ≤ 1 := by
    have hh := CFC.sqrt_le_sqrt L 1 (sub_nonneg.mp hLI.nonneg)
    simpa only [CFC.sqrt_one] using hh
  have hc : Commute S (1-S) := (Commute.one_right S).sub_right (Commute.refl S)
  have hSL : (S-L).PosSemidef := by
    have hh := hc.mul_nonneg hS0 (sub_nonneg.mpr hS1)
    rw [Matrix.mul_sub,Matrix.mul_one,hS2] at hh
    exact hh.posSemidef
  let p : ℝ := (S*ρ*S).trace.re
  let s : ℝ := (S*ρ).trace.re
  let d : ℝ := ((1-S)*ρ*(1-S)).trace.re
  have hp : p=(L*ρ).trace.re := by dsimp [p]; rw [trace_mul_cycle,hS2]
  have hp0 : 0 ≤ p := by
    have hh := (hρ.1.mul_mul_conjTranspose_same S).trace_nonneg
    rw [hS] at hh
    exact (Complex.nonneg_iff.mp hh).1
  have hp1 : p ≤ 1 := by
    have hh := positive_product_trace (1-L) ρ hLI hρ.1
    rw [Matrix.sub_mul,Matrix.one_mul,trace_sub,hρ.2,Complex.sub_re,Complex.one_re,← hp] at hh
    linarith
  have hsp : p ≤ s := by
    have hh := positive_product_trace (S-L) ρ hSL hρ.1
    rw [Matrix.sub_mul,trace_sub,Complex.sub_re,← hp] at hh
    exact sub_nonneg.mp hh
  have hd0 : 0 ≤ d := by
    have hh := (hρ.1.mul_mul_conjTranspose_same (1-S)).trace_nonneg
    rw [conjTranspose_sub,conjTranspose_one,hS] at hh
    exact (Complex.nonneg_iff.mp hh).1
  have hd : d=1-2*s+p := by
    have he : (1-S)*ρ*(1-S)=ρ-S*ρ-ρ*S+S*ρ*S := by noncomm_ring
    have hc' : (ρ*S).trace=(S*ρ).trace := trace_mul_comm _ _
    dsimp [d,p,s]
    rw [he,trace_add,trace_sub,trace_sub,hρ.2,hc']
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re]
    ring
  have hdε : d ≤ ε := by rw [← hp] at hdet; linarith
  let X := (1-S)*T
  let Y := T
  let Z := S*T
  have hXX : X*Xᴴ=(1-S)*ρ*(1-S) := by
    dsimp [X]
    rw [conjTranspose_mul,hT,conjTranspose_sub,conjTranspose_one,hS]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T T,hT2]
  have hZZ : Z*Zᴴ=S*ρ*S := by
    dsimp [Z]
    rw [conjTranspose_mul,hT,hS]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T T,hT2]
  have hx : schattenNorm 2 X=Real.sqrt d := by
    rw [← hs_adjoint X,QValue20Support.RecoverySchatten.schatten_two,conjTranspose_conjTranspose,hXX]
  have hxa : schattenNorm 2 Xᴴ=Real.sqrt d := by rw [hs_adjoint,hx]
  have hy : schattenNorm 2 Y=1 := by
    rw [QValue20Support.RecoverySchatten.schatten_two,hT,hT2,hρ.2]
    norm_num
  have hz : schattenNorm 2 Z=Real.sqrt p := by
    rw [← hs_adjoint Z,QValue20Support.RecoverySchatten.schatten_two,conjTranspose_conjTranspose,hZZ]
  have hf : ρ-S*ρ*S=X*Y+Z*Xᴴ := by
    calc
      ρ-S*ρ*S=T*T-S*(T*T)*S := by rw [hT2]
      _=X*Y+Z*Xᴴ := by
        dsimp [X,Y,Z]
        rw [conjTranspose_mul,hT,conjTranspose_sub,conjTranspose_one,hS]
        noncomm_ring
  have hb := (triangle (X*Y) (Z*Xᴴ)).trans (add_le_add (product_bound X Y) (product_bound Z Xᴴ))
  rw [hx,hxa,hy,hz,mul_one] at hb
  have hpR : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hmul := mul_le_mul_of_nonneg_right hpR (Real.sqrt_nonneg d)
  have hdR := Real.sqrt_le_sqrt hdε
  change traceNorm (ρ-S*ρ*S) ≤ _
  rw [hf]
  nlinarith

end QValue20Support.QuantumValueGentle

end

noncomputable section
open Matrix WildeQIT QValue20Support.QuantumValueTrace QValue20Support.QuantumValueGentle
open QAlgorithms.Papers.Independent.Information100.P50
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace QValue20Support.QuantumValueHSDifference
variable {n : Type} [Fintype n] [DecidableEq n]

lemma traceNorm_smul (z : ℂ) (A : Matrix n n ℂ) : traceNorm (z • A)=‖z‖*traceNorm A := by
  obtain ⟨U,hU,hu⟩ := (variational (z • A)).1
  obtain ⟨V,hV,hv⟩ := (variational A).1
  have hbU := (variational A).2 ⟨U,hU,rfl⟩
  have hbV := (variational (z • A)).2 ⟨V,hV,rfl⟩
  rw [hu,Matrix.smul_mul,Matrix.trace_smul,norm_smul]
  apply le_antisymm (mul_le_mul_of_nonneg_left hbU (norm_nonneg z))
  rw [Matrix.smul_mul,Matrix.trace_smul,norm_smul,← hv] at hbV
  rwa [hu,Matrix.smul_mul,Matrix.trace_smul,norm_smul] at hbV

lemma cross_re (X Y : Matrix n n ℂ) : (Y*Xᴴ).trace.re=(X*Yᴴ).trace.re := by
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (X*Yᴴ))
  simpa only [conjTranspose_mul,conjTranspose_conjTranspose,Complex.star_def,Complex.conj_re] using h

lemma difference_bound (X Y : Matrix n n ℂ)
    (hX : (X*Xᴴ).trace.re=1) (hY : (Y*Yᴴ).trace.re=1)
    (ε : ℝ) (hε : 0 ≤ ε) (hc : 1-ε ≤ ((X*Yᴴ).trace.re)^2) :
    traceNorm (X*Xᴴ-Y*Yᴴ) ≤ 2*Real.sqrt ε := by
  let c : ℝ := (X*Yᴴ).trace.re
  let A := X-Y
  let B := X+Y
  have hA : (A*Aᴴ).trace.re=2-2*c := by
    dsimp [A,c]
    rw [conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,
      Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_sub]
    simp only [Complex.sub_re,hX,hY,cross_re X Y]
    ring
  have hB : (B*Bᴴ).trace.re=2+2*c := by
    dsimp [B,c]
    rw [conjTranspose_add,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,
      Matrix.trace_add,Matrix.trace_add,Matrix.trace_add]
    simp only [Complex.add_re,hX,hY,cross_re X Y]
    ring
  have hA0 : 0 ≤ 2-2*c := by
    rw [← hA]; exact (Complex.nonneg_iff.mp (posSemidef_self_mul_conjTranspose A).trace_nonneg).1
  have hB0 : 0 ≤ 2+2*c := by
    rw [← hB]; exact (Complex.nonneg_iff.mp (posSemidef_self_mul_conjTranspose B).trace_nonneg).1
  have hsA : schattenNorm 2 A=Real.sqrt (2-2*c) := by
    rw [← hs_adjoint A,QValue20Support.RecoverySchatten.schatten_two,conjTranspose_conjTranspose,hA]
  have hsB : schattenNorm 2 B=Real.sqrt (2+2*c) := by
    rw [← hs_adjoint B,QValue20Support.RecoverySchatten.schatten_two,conjTranspose_conjTranspose,hB]
  have hf : X*Xᴴ-Y*Yᴴ=(1/2 : ℂ) • (A*Bᴴ+B*Aᴴ) := by
    dsimp [A,B]
    rw [conjTranspose_add,conjTranspose_sub]
    apply (smul_right_injective (M := Matrix n n ℂ) (show (2:ℂ) ≠ 0 by norm_num))
    simp only [smul_smul,show (2:ℂ)*(1/2)=1 by norm_num,one_smul]
    rw [show (2:ℂ) • (X*Xᴴ-Y*Yᴴ)=(X*Xᴴ-Y*Yᴴ)+(X*Xᴴ-Y*Yᴴ) by
      simp [two_smul]]
    noncomm_ring
  have hb := (triangle (A*Bᴴ) (B*Aᴴ)).trans
    (add_le_add (product_bound A Bᴴ) (product_bound B Aᴴ))
  rw [hs_adjoint,hs_adjoint,hsA,hsB] at hb
  have hp : traceNorm (X*Xᴴ-Y*Yᴴ) ≤ Real.sqrt (2-2*c)*Real.sqrt (2+2*c) := by
    rw [hf,traceNorm_smul]
    norm_num
    linarith
  apply hp.trans
  have h1 := Real.sq_sqrt hA0
  have h2 := Real.sq_sqrt hB0
  have h3 := Real.sq_sqrt hε
  have hprod : (Real.sqrt (2-2*c)*Real.sqrt (2+2*c))^2=(2-2*c)*(2+2*c) := by
    rw [mul_pow,h1,h2]
  have hp0 := mul_nonneg (Real.sqrt_nonneg (2-2*c)) (Real.sqrt_nonneg (2+2*c))
  dsimp [c] at hprod hA0 hB0 hp0 ⊢
  nlinarith [Real.sqrt_nonneg ε]
end QValue20Support.QuantumValueHSDifference

end

noncomputable section
open Matrix WildeQIT QValue20Support.QuantumValueTrace QValue20Support.QuantumValueGentle
open QAlgorithms.Papers.Independent.Information100.P50
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace QValue20Support.QuantumValueNormalized
variable {n : Type} [Fintype n] [DecidableEq n]
lemma normalized (ρ L : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hL : L.PosSemidef) (hLI : (1-L).PosSemidef) (ε : ℝ) (hε : 0 ≤ ε)
    (hdet : 1-ε ≤ (L*ρ).trace.re) (hnz : (L*ρ).trace ≠ 0) :
    traceNorm (ρ-WildeQIT.Gentle.postMeasurementState L ρ) ≤ 2*Real.sqrt ε := by
  let S := CFC.sqrt L
  let T := CFC.sqrt ρ
  have hS : Sᴴ=S := sqrt_star L
  have hT : Tᴴ=T := sqrt_star ρ
  have hS2 : S*S=L := CFC.sqrt_mul_sqrt_self L hL.nonneg
  have hT2 : T*T=ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg L
  have hS1 : S ≤ 1 := by
    have hh := CFC.sqrt_le_sqrt L 1 (sub_nonneg.mp hLI.nonneg)
    simpa only [CFC.sqrt_one] using hh
  have hc : Commute S (1-S) := (Commute.one_right S).sub_right (Commute.refl S)
  have hSL : (S-L).PosSemidef := by
    have hh := hc.mul_nonneg hS0 (sub_nonneg.mpr hS1)
    rw [Matrix.mul_sub,Matrix.mul_one,hS2] at hh
    exact hh.posSemidef
  let p : ℝ := (S*ρ*S).trace.re
  let s : ℝ := (S*ρ).trace.re
  have hp : p=(L*ρ).trace.re := by dsimp [p]; rw [trace_mul_cycle,hS2]
  have hp0 : 0 ≤ p := by
    have hh := (hρ.1.mul_mul_conjTranspose_same S).trace_nonneg
    rw [hS] at hh
    exact (Complex.nonneg_iff.mp hh).1
  have hp1 : p ≤ 1 := by
    have hh := positive_product_trace (1-L) ρ hLI hρ.1
    rw [Matrix.sub_mul,Matrix.one_mul,trace_sub,hρ.2,Complex.sub_re,Complex.one_re,← hp] at hh
    linarith
  have hsp : p ≤ s := by
    have hh := positive_product_trace (S-L) ρ hSL hρ.1
    rw [Matrix.sub_mul,trace_sub,Complex.sub_re,← hp] at hh
    exact sub_nonneg.mp hh
  have hpC : (L*ρ).trace=(p : ℂ) := by
    have hh := (hρ.1.mul_mul_conjTranspose_same S).trace_nonneg
    rw [hS,trace_mul_cycle,hS2] at hh
    apply Complex.ext
    · exact hp.symm
    · exact (Complex.nonneg_iff.mp hh).2.symm
  have hpne : p ≠ 0 := by
    intro hz
    apply hnz
    rw [hpC,hz,Complex.ofReal_zero]
  have hpPos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpne)
  let r : ℝ := (Real.sqrt p)⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr2 : r^2=p⁻¹ := by
    dsimp [r]
    rw [inv_pow,Real.sq_sqrt hp0]
  have hrp : r^2*p=1 := by rw [hr2,inv_mul_cancel₀ hpne]
  let Y : Matrix n n ℂ := (r : ℂ) • (S*T)
  have hYY : Y*Yᴴ=((r^2 : ℝ) : ℂ) • (S*ρ*S) := by
    dsimp [Y]
    simp only [conjTranspose_smul,conjTranspose_mul,hT,hS,Complex.star_def,
      Complex.conj_ofReal,star_trivial,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← Complex.ofReal_mul]
    simp only [← pow_two,Complex.ofReal_pow]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T T,hT2]
  have hX : (T*Tᴴ).trace.re=1 := by rw [hT,hT2,hρ.2]; rfl
  have hY : (Y*Yᴴ).trace.re=1 := by
    rw [hYY,Matrix.trace_smul]
    change (((r^2 : ℝ) : ℂ)*(S*ρ*S).trace).re=1
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hrp
  have hc : (T*Yᴴ).trace.re=r*s := by
    have he : T*Yᴴ=(r : ℂ) • (ρ*S) := by
      dsimp [Y]
      simp only [conjTranspose_smul,conjTranspose_mul,hT,hS,Complex.star_def,
        Complex.conj_ofReal,star_trivial,Matrix.mul_smul]
      rw [← Matrix.mul_assoc,hT2]
    rw [he,Matrix.trace_smul,trace_mul_comm ρ S]
    change ((r:ℂ)*(S*ρ).trace).re=r*s
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  have hcε : 1-ε ≤ ((T*Yᴴ).trace.re)^2 := by
    rw [hc,mul_pow]
    have hss : p^2 ≤ s^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hss (sq_nonneg r)
    have he : r^2*p^2=p := by calc
      r^2*p^2=(r^2*p)*p := by ring
      _=p := by rw [hrp,one_mul]
    rw [he] at hh
    rw [← hp] at hdet
    linarith
  have hpost : Y*Yᴴ=WildeQIT.Gentle.postMeasurementState L ρ := by
    rw [hYY,WildeQIT.Gentle.postMeasurementState,hpC,← Complex.ofReal_inv,hr2]
  have hb := QValue20Support.QuantumValueHSDifference.difference_bound T Y hX hY ε hε hcε
  rwa [hT,hT2,hpost] at hb
end QValue20Support.QuantumValueNormalized

end

noncomputable section
open Matrix WildeQIT
open scoped ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.QuantumValuePureBound
variable {n : Type} [Fintype n] [DecidableEq n]
lemma pure_bound (ψ φ : EuclideanSpace ℂ n) (hψ : ‖ψ‖=1) (hφ : ‖φ‖=1) :
    (1/2 : ℝ)*traceDist (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
      (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) ≤ ‖ψ-φ‖ := by
  classical
  haveI : Nonempty n := by
    by_contra hn
    haveI : IsEmpty n := not_nonempty_iff.mp hn
    have he : ψ=0 := Subsingleton.elim _ _
    simp [he] at hψ
  let j : n := Classical.choice inferInstance
  let emb : EuclideanSpace ℂ n → Matrix n n ℂ := fun u i k => if k=j then u i else 0
  have hgram (u v : EuclideanSpace ℂ n) : emb u*(emb v)ᴴ=
      vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp v)) := by
    ext i k
    simp [emb,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.vecMulVec_apply]
  have htr (u v : EuclideanSpace ℂ n) : (emb u*(emb v)ᴴ).trace=inner ℂ v u := by
    rw [hgram,Matrix.trace_vecMulVec]
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]
  have hX : (emb ψ*(emb ψ)ᴴ).trace.re=1 := by
    rw [htr,inner_self_eq_norm_sq_to_K,hψ]; norm_num
  have hY : (emb φ*(emb φ)ᴴ).trace.re=1 := by
    rw [htr,inner_self_eq_norm_sq_to_K,hφ]; norm_num
  have hc : 1-‖ψ-φ‖^2 ≤ ((emb ψ*(emb φ)ᴴ).trace.re)^2 := by
    rw [htr]
    have hs := norm_sub_sq (𝕜 := ℂ) ψ φ
    rw [hψ,hφ] at hs
    have hi : (inner ℂ ψ φ).re=(inner ℂ φ ψ).re := inner_re_symm (𝕜 := ℂ) ψ φ
    change ‖ψ-φ‖^2=1^2-2*(inner ℂ ψ φ).re+1^2 at hs
    rw [hi] at hs
    nlinarith [sq_nonneg ((inner ℂ φ ψ).re-1)]
  have hb := QValue20Support.QuantumValueHSDifference.difference_bound (emb ψ) (emb φ) hX hY
    (‖ψ-φ‖^2) (sq_nonneg _) hc
  rw [hgram,hgram,Real.sqrt_sq (norm_nonneg _)] at hb
  change (1/2 : ℝ)*traceNorm _ ≤ _
  linarith
end QValue20Support.QuantumValuePureBound

end

open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Kronecker




/-- **Pure-state trace distance** in the proof of Theorem 3.3 of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.18: the `L2` bound on the

`D(|ψ⟩⟨ψ|, |φ⟩⟨φ|) = ½‖|ψ⟩⟨ψ| − |φ⟩⟨φ|‖₁ ≤ ‖ψ − φ‖`.

**Formalization Note.** `|ψ⟩⟨ψ|` is `Matrix.vecMulVec ψ (star ψ)` (entries `ψ_i \overline{ψ_j}`),
the norm on vectors is the Euclidean norm, and the paper's trace distance is
`(1/2) * WildeQIT.traceDist` (the published `traceDist` has no factor `½`). -/
theorem solution {n : Type} [Fintype n] [DecidableEq n] (ψ φ : EuclideanSpace ℂ n)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    (1 / 2) * WildeQIT.traceDist (Matrix.vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
        (Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) ≤ ‖ψ - φ‖ := by
  exact QValue20Support.QuantumValuePureBound.pure_bound ψ φ hψ hφ