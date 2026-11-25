-- Prove2me | solution 1 for QReversal.PGMBound.eq_41
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T18:07:49.919169+00:00
-- url     : https://prove2.me/submissions/2242bd93-e11b-4c77-84db-ad4f333e7bd0

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
noncomputable section
open Matrix QReversal.PGMBound PeresTerno QuantumValuePGMAlgebra
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
namespace QuantumValuePGMFidelity
variable {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
lemma sqrt_density (p : J → ℝ) (hp : IsProbability p) :
    CFC.sqrt (rho p)=diagonal (fun j => (Real.sqrt (p j) : ℂ)) := by
  have hρ : (rho p).PosSemidef := posSemidef_diagonal_iff.mpr (fun j => by exact_mod_cast hp.1 j)
  have hD : (diagonal (fun j => (Real.sqrt (p j) : ℂ))).PosSemidef :=
    posSemidef_diagonal_iff.mpr (fun j => by exact_mod_cast Real.sqrt_nonneg (p j))
  apply (CFC.sqrt_eq_iff _ _ hρ.nonneg hD.nonneg).mpr
  rw [diagonal_mul_diagonal]
  change diagonal (fun j => (Real.sqrt (p j) : ℂ)*(Real.sqrt (p j) : ℂ))=diagonal (fun j => (p j : ℂ))
  congr 1
  funext j
  simpa only [pow_two] using sqrt_square_complex (p j) (hp.1 j)

lemma classic_entry (lam : O → J → ℝ) (v : O → J → O → ℂ) (i : O) (j t : J) (o : O) :
    classicKraus lam v (i,j) o t=if t=j then (Real.sqrt (lam i j) : ℂ)*v i j o else 0 := by
  by_cases h : t=j
  · subst t;simp [classicKraus,Matrix.vecMulVec_apply,Matrix.smul_apply]
  · simp [classicKraus,Matrix.vecMulVec_apply,Matrix.smul_apply,Pi.single_apply,h,Ne.symm h]

lemma weighted_entry (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) (a b : O×J) (t : J) :
    (Real.sqrt (p t) : ℂ)*
      (QReversal.PGMBound.comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v) (a,b)) t t=
        if a.2=t ∧ b.2=t then ((Rmat p lam v*Amat p lam v) : Matrix (J×O) (J×O) ℂ) (t,a.1) (t,b.1) else 0 := by
  rcases a with ⟨i,j⟩
  rcases b with ⟨i',j'⟩
  have ho : krausUpdate (classicKraus lam v) (rho p)=Amat p lam v*(Amat p lam v)ᴴ :=
    (output_gram p lam v hp hs).symm
  simp only [QReversal.PGMBound.comp,QReversal.PGMBound.reversal,Rmat]
  rw [ho,sqrt_density p hp]
  by_cases hj : j=t <;> by_cases hj' : j'=t
  · subst j;subst j'
    simp only [and_self,ite_true,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.diagonal_apply,classic_entry,if_pos rfl,Finset.sum_mul,Finset.mul_sum]
    simp only [mul_ite,ite_mul,zero_mul,mul_zero,Finset.sum_ite_eq',Finset.sum_ite_eq]
    simp only [Finset.mem_univ,ite_true]
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro x _
    simp only [Amat,Complex.ofReal_mul,Complex.star_def,map_mul,Complex.conj_ofReal,ite_true]
    ring
  · simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
      classic_entry,hj,hj',Ne.symm hj',mul_ite,ite_mul]
  · simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
      classic_entry,hj,hj',Ne.symm hj,mul_ite,ite_mul]
  · simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
      classic_entry,hj,hj',Ne.symm hj,Ne.symm hj',mul_ite,ite_mul]

lemma basis_update {ι : Type*} [Fintype ι] (K : ι → Matrix J J ℂ) (j : J) :
    (krausUpdate K (Matrix.single j j 1) j j).re=∑ a, Complex.normSq (K a j j) := by
  have hx (a : ι) : ((K a*Matrix.single j j (1 : ℂ)*(K a)ᴴ) : Matrix J J ℂ) j j=K a j j*star (K a j j) := by
    have he (x : J) : (K a*Matrix.single j j (1 : ℂ)) j x=if x=j then K a j j else 0 := by
      by_cases h : x=j
      · subst x;simp
      · rw [Matrix.mul_single_apply_of_ne 1 j j j x h]
        simp [h]
    rw [Matrix.mul_apply]
    simp only [he,Matrix.conjTranspose_apply,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [krausUpdate,Matrix.sum_apply,Complex.re_sum,hx]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm,Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  rfl

lemma classical_fidelity (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) :
    Fcl p (QReversal.PGMBound.comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v))=
      ∑ j, ∑ i, ∑ i', Complex.normSq (((Rmat p lam v*Amat p lam v) : Matrix (J×O) (J×O) ℂ) (j,i) (j,i')) := by
  unfold Fcl
  simp_rw [basis_update]
  apply Finset.sum_congr rfl
  intro j _
  have hm (a b : O×J) : p j*Complex.normSq
      ((QReversal.PGMBound.comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v) (a,b)) j j)=
      Complex.normSq (if a.2=j ∧ b.2=j then ((Rmat p lam v*Amat p lam v) : Matrix (J×O) (J×O) ℂ) (j,a.1) (j,b.1) else 0) := by
    rw [← weighted_entry p lam v hp hs a b j,Complex.normSq_mul,Complex.normSq_ofReal,
      Real.mul_self_sqrt (hp.1 j)]
  rw [Finset.mul_sum]
  simp only [Fintype.sum_prod_type]
  simp_rw [hm]
  change (∑ i : O, ∑ k : J, ∑ i' : O, ∑ l : J, Complex.normSq (if k=j ∧ l=j then (Rmat p lam v * Amat p lam v) (j,i) (j,i') else 0)) = _
  simp only [ite_and, apply_ite Complex.normSq, Complex.normSq_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
end QuantumValuePGMFidelity

end
open Matrix PeresTerno QReversal.PGMBound
open scoped MatrixOrder ComplexOrder

set_option autoImplicit false



theorem solution {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      ∑ j, ∑ i, ∑ i',
        Complex.normSq ((Rmat p lam v * Amat p lam v) (j, i) (j, i')) := by
  exact QuantumValuePGMFidelity.classical_fidelity p lam v hp hs