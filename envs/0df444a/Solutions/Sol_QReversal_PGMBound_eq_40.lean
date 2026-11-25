-- Prove2me | solution 1 for QReversal.PGMBound.eq_40
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T18:03:09.909866+00:00
-- url     : https://prove2.me/submissions/388db681-d48d-47b0-9c97-9f52afd59ee4

import Definitions.Def_QReversal_PGMBound_Setting
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
noncomputable section
open Matrix Unitary QReversal.PGMBound PeresTerno
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumValuePGMAlgebra
variable {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]

lemma sqrt_square_complex (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ)^2=(x : ℂ) := by
  exact_mod_cast Real.sq_sqrt hx

lemma kraus_entry (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hs : IsSpectralData lam v) (ij : O×J) (o o' : O) :
    (classicKraus lam v ij*rho p*(classicKraus lam v ij)ᴴ) o o'=
      (p ij.2 : ℂ)*(lam ij.1 ij.2 : ℂ)*(v ij.1 ij.2 o*star (v ij.1 ij.2 o')) := by
  simp only [classicKraus,rho,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.smul_apply,
    Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul,star_mul]
  simp [Matrix.diagonal_apply,Pi.single_apply,Complex.star_def,Complex.conj_ofReal,
    Finset.sum_mul,Finset.mul_sum,mul_ite,ite_mul]
  have hsq := sqrt_square_complex (lam ij.1 ij.2) (hs.1 ij.1 ij.2)
  ring_nf
  rw [hsq] <;> ring

lemma output_entry (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hs : IsSpectralData lam v) (o o' : O) :
    rhoOut p lam v o o'=∑ i, ∑ j, (p j : ℂ)*(lam i j : ℂ)*(v i j o*star (v i j o')) := by
  simp only [rhoOut,krausUpdate,Matrix.sum_apply,Fintype.sum_prod_type,kraus_entry p lam v hs]

lemma output_gram (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) :
    Amat p lam v*(Amat p lam v)ᴴ=rhoOut p lam v := by
  ext o o'
  rw [output_entry p lam v hs]
  simp only [Amat,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Complex.ofReal_mul,star_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.star_def,map_mul,Complex.conj_ofReal]
  have hp2 := sqrt_square_complex (p j) (hp.1 j)
  have hl2 := sqrt_square_complex (lam i j) (hs.1 i j)
  calc
    _=(Real.sqrt (p j) : ℂ)^2*(Real.sqrt (lam i j) : ℂ)^2*(v i j o*star (v i j o')) := by
      simp only [Complex.star_def];ring
    _=_ := by rw [hp2,hl2];simp only [starRingEnd_apply]

lemma output_trace (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) : (rhoOut p lam v).trace=1 := by
  have hv (i : O) (j : J) : ∑ o, v i j o*star (v i j o)=1 := by
    have hh := hs.2.2 j i i
    simpa [dotProduct,mul_comm] using hh
  have htrace : (rhoOut p lam v).trace=∑ i, ∑ j, (p j : ℂ)*(lam i j : ℂ) := by
    simp only [Matrix.trace,Matrix.diag,output_entry p lam v hs]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum,hv,mul_one]
  rw [htrace,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,← Complex.ofReal_sum,hs.2.1,Complex.ofReal_one,mul_one]
  rw [← Complex.ofReal_sum,hp.2,Complex.ofReal_one]

lemma inverse_sandwich {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.PosDef) :
    QReversal.NearOpt.invSqrt X*X*QReversal.NearOpt.invSqrt X=1 := by
  let h := hX.posSemidef.isHermitian
  let U : Matrix n n ℂ := h.eigenvectorUnitary
  let d : n → ℂ := fun i => (Real.sqrt (h.eigenvalues i))⁻¹
  let e : n → ℂ := fun i => (h.eigenvalues i : ℂ)
  have hUU : Uᴴ*U=1 := Unitary.coe_star_mul_self h.eigenvectorUnitary
  have hUU' : U*Uᴴ=1 := Unitary.coe_mul_star_self h.eigenvectorUnitary
  have hx : X=U*diagonal e*Uᴴ := h.spectral_theorem
  have hs : QReversal.NearOpt.invSqrt X=U*diagonal d*Uᴴ := by
    rw [QReversal.NearOpt.invSqrt,h.cfc_eq,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    change U*diagonal (fun i => (((Real.sqrt (h.eigenvalues i))⁻¹ : ℝ) : ℂ))*Uᴴ=U*diagonal d*Uᴴ
    simp only [Complex.ofReal_inv]
    rfl
  have hd : diagonal d*diagonal e*diagonal d=(1 : Matrix n n ℂ) := by
    rw [diagonal_mul_diagonal,diagonal_mul_diagonal]
    apply Matrix.diagonal_eq_one.mpr
    funext i
    change d i*e i*d i=1
    have hp : 0 < h.eigenvalues i := hX.eigenvalues_pos i
    dsimp [d,e]
    have hsq := sqrt_square_complex (h.eigenvalues i) hp.le
    have hn : (Real.sqrt (h.eigenvalues i) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hp))
    field_simp
    exact hsq.symm
  rw [hs,hx]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U,hUU,Matrix.one_mul,
    ← Matrix.mul_assoc Uᴴ U,hUU,Matrix.one_mul]
  rw [← Matrix.mul_assoc (diagonal d) (diagonal e),← Matrix.mul_assoc (diagonal d*diagonal e) (diagonal d),hd]
  simpa only [Matrix.mul_one,Matrix.one_mul] using hUU'
lemma frobenius {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    (∑ a, ∑ b, Complex.normSq (M a b))=(Mᴴ*M).trace.re := by
  symm
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  rfl

lemma unit_frobenius (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) (hfull : (rhoOut p lam v).PosDef) :
    ∑ a : J×O, ∑ b : J×O, Complex.normSq ((Rmat p lam v*Amat p lam v) a b)=1 := by
  let A := Amat p lam v
  let S := QReversal.NearOpt.invSqrt (A*Aᴴ)
  have hG : (A*Aᴴ).PosDef := by rw [output_gram p lam v hp hs];exact hfull
  have hSGS : S*(A*Aᴴ)*S=1 := inverse_sandwich (A*Aᴴ) hG
  have hS : Sᴴ=S := by
    change IsSelfAdjoint S
    exact cfc_predicate _ _
  have hMM : (Rmat p lam v*A)ᴴ*(Rmat p lam v*A)=Aᴴ*A := by
    change (Aᴴ*S*A)ᴴ*(Aᴴ*S*A)=Aᴴ*A
    rw [conjTranspose_mul,conjTranspose_mul,conjTranspose_conjTranspose,hS]
    calc
      Aᴴ*(S*A)*(Aᴴ*S*A)=Aᴴ*(S*(A*Aᴴ)*S)*A := by simp only [Matrix.mul_assoc]
      _=Aᴴ*A := by rw [hSGS,Matrix.mul_one]
  rw [frobenius,hMM,Matrix.trace_mul_comm Aᴴ A]
  change (A*Aᴴ).trace.re=1
  rw [output_gram p lam v hp hs,output_trace p lam v hp hs]
  rfl
end QuantumValuePGMAlgebra

end
open Matrix PeresTerno QReversal.PGMBound
open scoped MatrixOrder ComplexOrder

set_option autoImplicit false



theorem solution {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    ∑ a : J × O, ∑ b : J × O,
      Complex.normSq ((Rmat p lam v * Amat p lam v) a b) = 1 := by
  exact QuantumValuePGMAlgebra.unit_frobenius p lam v hp hs hfull