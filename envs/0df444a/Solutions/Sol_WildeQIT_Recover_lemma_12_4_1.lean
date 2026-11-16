-- Prove2me | solution 1 for WildeQIT.Recover.lemma_12_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-16T02:18:26.351575+00:00
-- url     : https://prove2.me/submissions/136100c1-88e6-4e57-bef8-e30a57349525

import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_Recover_spectralFun
import Definitions.Def_WildeQIT_Recover_renyiDelta
import Definitions.Def_WildeQIT_Recover_rotatedPetz
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Recover_qRelEntropy
import Theorems.Thm_Matrix_hasDerivAt_trace_rpow_at_one
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open Matrix WildeQIT.Recover
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.PetzSpectral
variable {n : Type} [Fintype n] [DecidableEq n]
lemma sf_eq (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) :
    spectralFun f A = (hA.eigenvectorUnitary : Matrix n n ℂ)*diagonal (fun i=>f (hA.eigenvalues i))*(hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  simp only [spectralFun,dif_pos hA]
lemma sf_congr (A : Matrix n n ℂ) (hA : A.IsHermitian) {f g : ℝ → ℂ}
    (h : ∀ i,f (hA.eigenvalues i)=g (hA.eigenvalues i)) : spectralFun f A=spectralFun g A := by
  rw [sf_eq A hA,sf_eq A hA]
  congr 2
  ext i j
  simp [diagonal_apply,h]
lemma sf_mul (A : Matrix n n ℂ) (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    spectralFun f A*spectralFun g A=spectralFun (fun x=>f x*g x) A := by
  simp only [sf_eq A hA,Matrix.mul_assoc]
  have hu : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self _
  rw [← Matrix.mul_assoc (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ (hA.eigenvectorUnitary : Matrix n n ℂ),hu]
  simp [← Matrix.mul_assoc,diagonal_mul_diagonal]
lemma sf_one (A : Matrix n n ℂ) (hA : A.IsHermitian) : spectralFun (fun _=>1) A=1 := by
  rw [sf_eq A hA]
  simp only [diagonal_one, Matrix.mul_one]
  exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
lemma sf_sub (A : Matrix n n ℂ) (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    spectralFun f A-spectralFun g A=spectralFun (fun x=>f x-g x) A := by
  simp only [sf_eq A hA, ← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
lemma sf_id (A : Matrix n n ℂ) (hA : A.IsHermitian) : spectralFun (fun x=>(x:ℂ)) A=A := by
  rw [sf_eq A hA]
  exact hA.spectral_theorem.symm
lemma sf_star (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) :
    (spectralFun f A)ᴴ=spectralFun (fun x=>conj (f x)) A := by
  simp only [sf_eq A hA,conjTranspose_mul,conjTranspose_conjTranspose,diagonal_conjTranspose,Matrix.mul_assoc]
  rfl
lemma pow_add (A : Matrix n n ℂ) (hA : A.IsHermitian) (z w : ℂ) :
    supportPow A z*supportPow A w=supportPow A (z+w) := by
  unfold supportPow
  rw [sf_mul A hA]
  apply sf_congr A hA
  intro i
  split_ifs <;> simp [Complex.exp_add,add_mul]
lemma pow_zero (A : Matrix n n ℂ) : supportPow A 0=supportProj A := by
  simp only [supportPow,supportProj,zero_mul,Complex.exp_zero]
lemma pow_star (A : Matrix n n ℂ) (hA : A.IsHermitian) (z : ℂ) :
    (supportPow A z)ᴴ = supportPow A (conj z) := by
  rw [supportPow,sf_star A hA]
  apply sf_congr A hA
  intro i
  split_ifs <;> simp [← Complex.exp_conj]
lemma support_star (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (supportProj A)ᴴ = supportProj A := by
  rw [← pow_zero,pow_star A hA]
  simp
lemma support_square (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    supportProj A * supportProj A = supportProj A := by
  rw [← pow_zero,pow_add A hA,zero_add]
lemma support_pow_left (A : Matrix n n ℂ) (hA : A.IsHermitian) (z : ℂ) :
    supportProj A * supportPow A z = supportPow A z := by
  rw [← pow_zero,pow_add A hA,zero_add]
lemma support_pow_right (A : Matrix n n ℂ) (hA : A.IsHermitian) (z : ℂ) :
    supportPow A z * supportProj A = supportPow A z := by
  rw [← pow_zero,pow_add A hA,add_zero]
lemma pow_one (A : Matrix n n ℂ) (hA : A.PosSemidef) : supportPow A 1=A := by
  apply Eq.trans (b := spectralFun (fun x => (x : ℂ)) A) _ (sf_id A hA.isHermitian)
  unfold supportPow
  apply sf_congr A hA.isHermitian
  intro i
  by_cases hi : hA.isHermitian.eigenvalues i=0
  · simp [hi]
  · have hip : 0 < hA.isHermitian.eigenvalues i := lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi)
    simp only [if_neg hi,one_mul,← Complex.ofReal_exp,Real.exp_log hip]
lemma pow_real_star (A : Matrix n n ℂ) (hA : A.IsHermitian) (r : ℝ) :
    (supportPow A (r:ℂ))ᴴ=supportPow A r := by
  rw [supportPow,sf_star A hA]
  apply sf_congr A hA
  intro i
  split_ifs <;> simp [← Complex.exp_conj]
lemma pow_half_square (A : Matrix n n ℂ) (hA : A.PosSemidef) : supportPow A (1/2)*supportPow A (1/2)=A := by
  rw [pow_add A hA.isHermitian,show (1/2:ℂ)+1/2=1 by norm_num,pow_one A hA]
lemma inverse_sandwich (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    supportPow A (-(1/2))*A*supportPow A (-(1/2))=supportProj A := by
  calc
    _=supportPow A (-(1/2))*supportPow A 1*supportPow A (-(1/2)) := by rw [pow_one A hA]
    _=_ := by rw [pow_add A hA.isHermitian,pow_add A hA.isHermitian,show (-(1/2):ℂ)+1+ -(1/2)=0 by norm_num,pow_zero]
lemma support_mul (A : Matrix n n ℂ) (hA : A.PosSemidef) : supportProj A*A=A := by
  calc
    _ = supportPow A 0 * supportPow A 1 := by rw [pow_zero,pow_one A hA]
    _ = A := by rw [pow_add A hA.isHermitian,zero_add,pow_one A hA]
lemma rotation_self (A : Matrix n n ℂ) (hA : A.PosSemidef) (t : ℝ) :
    supportPow A ((t:ℂ)*Complex.I)*A*supportPow A (-((t:ℂ)*Complex.I))=A := by
  calc
    _=supportPow A ((t:ℂ)*Complex.I)*supportPow A 1*supportPow A (-((t:ℂ)*Complex.I)) := by rw [pow_one A hA]
    _=_ := by rw [pow_add A hA.isHermitian,pow_add A hA.isHermitian,show (t:ℂ)*Complex.I+1+ -((t:ℂ)*Complex.I)=1 by ring,pow_one A hA]
lemma support_complement_pos (A : Matrix n n ℂ) (hA : A.PosSemidef) : (1-supportProj A).PosSemidef := by
  rw [← sf_one A hA.isHermitian]
  unfold supportProj
  rw [sf_sub A hA.isHermitian,sf_eq A hA.isHermitian]
  apply PosSemidef.mul_mul_conjTranspose_same
  apply posSemidef_diagonal_iff.mpr
  intro i
  split_ifs <;> simp
end RenyiLimitSupport.PetzSpectral

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover
open scoped ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.PetzChannel
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma map_positive (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) : (N.apply A).PosSemidef := by
  unfold QChannel.apply
  exact posSemidef_sum _ (fun i _ => hA.mul_mul_conjTranspose_same (N.K i))
lemma adjoint_positive (N : QChannel a b) (A : Matrix b b ℂ) (hA : A.PosSemidef) : (adjointMap N A).PosSemidef := by
  unfold adjointMap
  exact posSemidef_sum _ (fun i _ => hA.conjTranspose_mul_mul_same (N.K i))
lemma adjoint_one (N : QChannel a b) : adjointMap N 1=1 := by
  simpa only [adjointMap,Matrix.mul_one] using N.complete
lemma adjoint_sub (N : QChannel a b) (A B : Matrix b b ℂ) : adjointMap N (A-B)=adjointMap N A-adjointMap N B := by
  simp only [adjointMap,Matrix.mul_sub,Matrix.sub_mul,Finset.sum_sub_distrib]
lemma trace_preserved (N : QChannel a b) (A : Matrix a a ℂ) : (N.apply A).trace=A.trace := by
  simp only [QChannel.apply,trace_sum]
  have hh : (∑ i,trace (N.K i*A*(N.K i)ᴴ)) = trace ((∑ i,(N.K i)ᴴ*N.K i)*A) := by
    simp only [Finset.sum_mul,trace_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [trace_mul_cycle]
  rw [hh,N.complete,one_mul]
lemma trace_dual (N : QChannel a b) (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    trace (A*adjointMap N B)=trace (N.apply A*B) := by
  simp only [adjointMap,QChannel.apply,Finset.mul_sum,Finset.sum_mul,trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.mul_assoc A ((N.K i)ᴴ * B) (N.K i), trace_mul_comm _ (N.K i)]
  simp only [Matrix.mul_assoc]
lemma half_star (A : Matrix a a ℂ) (hA : A.PosSemidef) : (supportPow A (1/2))ᴴ=supportPow A (1/2) := by
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using RenyiLimitSupport.PetzSpectral.pow_real_star A hA.isHermitian (1/2)
lemma petz_input (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    petzMap A N (N.apply A) = supportPow A (1/2)*adjointMap N (supportProj (N.apply A))*supportPow A (1/2) := by
  rw [petzMap,RenyiLimitSupport.PetzSpectral.inverse_sandwich _ (map_positive N A hA)]
lemma petz_defect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    A-petzMap A N (N.apply A) = supportPow A (1/2)*adjointMap N (1-supportProj (N.apply A))*supportPow A (1/2) := by
  rw [adjoint_sub,adjoint_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,RenyiLimitSupport.PetzSpectral.pow_half_square A hA,petz_input N A hA]
lemma petz_perfect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) : petzMap A N (N.apply A)=A := by
  have hd : (A-petzMap A N (N.apply A)).PosSemidef := by
    rw [petz_defect N A hA]
    have hh := (adjoint_positive N _ (RenyiLimitSupport.PetzSpectral.support_complement_pos _ (map_positive N A hA))).mul_mul_conjTranspose_same (supportPow A (1/2))
    rwa [half_star A hA] at hh
  have ht : (A-petzMap A N (N.apply A)).trace=0 := by
    rw [trace_sub,petz_input N A hA]
    have hh : trace (supportPow A (1/2)*adjointMap N (supportProj (N.apply A))*supportPow A (1/2)) = A.trace := by
      rw [trace_mul_cycle,RenyiLimitSupport.PetzSpectral.pow_half_square A hA,trace_dual,trace_mul_comm,RenyiLimitSupport.PetzSpectral.support_mul _ (map_positive N A hA),trace_preserved]
    rw [hh,sub_self]
  exact (sub_eq_zero.mp (hd.trace_eq_zero_iff.mp ht)).symm
lemma rotated_perfect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) (t : ℝ) :
    rotatedPetz A N t (N.apply A)=A := by
  unfold rotatedPetz rotU
  rw [RenyiLimitSupport.PetzSpectral.rotation_self _ (map_positive N A hA),petz_perfect N A hA,RenyiLimitSupport.PetzSpectral.rotation_self A hA]
end RenyiLimitSupport.PetzChannel

end

noncomputable section
namespace RenyiLimitSupport.RecoveryDualFamily
variable {n : Type*} [Fintype n] [DecidableEq n]
def diagonalCLM : (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  (Matrix.diagonalLinearMap n ℂ ℂ).toContinuousLinearMap
end RenyiLimitSupport.RecoveryDualFamily
end

noncomputable section
open Matrix Unitary WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryPowerCalculus
variable {n : Type} [Fintype n] [DecidableEq n]

lemma spectral_real_eq_cfc (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    spectralFun (fun x => (f x : ℂ)) A=cfc f A := by
  rw [RenyiLimitSupport.PetzSpectral.sf_eq A hA,hA.cfc_eq,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  rfl

lemma supportPow_pos_eq_cfc (A : Matrix n n ℂ) (hA : A.PosSemidef) {r : ℝ} (hr : 0 < r) :
    supportPow A r=cfc (fun x : ℝ => x^r) A := by
  calc
    _ = spectralFun (fun x => ((x^r : ℝ) : ℂ)) A := by
      unfold supportPow
      apply RenyiLimitSupport.PetzSpectral.sf_congr A hA.isHermitian
      intro i
      by_cases hi : hA.isHermitian.eigenvalues i=0
      · simp [hi,Real.zero_rpow hr.ne']
      · have hp : 0 < hA.isHermitian.eigenvalues i := lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi)
        rw [if_neg hi,Real.rpow_def_of_pos hp,Complex.ofReal_exp]
        congr 1
        push_cast
        ring
    _ = _ := spectral_real_eq_cfc A hA.isHermitian _

lemma supportPow_imag_norm_le_one (A : Matrix n n ℂ) (hA : A.IsHermitian) (t : ℝ) :
    ‖supportPow A ((t : ℂ)*Complex.I)‖ ≤ 1 := by
  rw [supportPow,RenyiLimitSupport.PetzSpectral.sf_eq A hA]
  change ‖(hA.eigenvectorUnitary : Matrix n n ℂ)*
    diagonal (fun i => if hA.eigenvalues i=0 then 0 else
      Complex.exp (((t : ℂ)*Complex.I)*(Real.log (hA.eigenvalues i) : ℂ)))*
      ((star hA.eigenvectorUnitary : unitary (Matrix n n ℂ)) : Matrix n n ℂ)‖ ≤ 1
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs <;> simp [Complex.norm_exp,Complex.mul_re]

lemma supportPow_differentiable (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    Differentiable ℂ (supportPow A) := by
  have hcoeff (i : n) : Differentiable ℂ (fun z : ℂ => if hA.eigenvalues i=0 then 0 else
      Complex.exp (z*(Real.log (hA.eigenvalues i) : ℂ))) := by
    by_cases hi : hA.eigenvalues i=0
    · simp only [if_pos hi]
      exact differentiable_const _
    · simp only [if_neg hi]
      fun_prop
  have hD : Differentiable ℂ (fun z : ℂ => RenyiLimitSupport.RecoveryDualFamily.diagonalCLM (n := n)
      (fun i => if hA.eigenvalues i=0 then 0 else Complex.exp (z*(Real.log (hA.eigenvalues i) : ℂ)))) :=
    (RenyiLimitSupport.RecoveryDualFamily.diagonalCLM (n := n)).differentiable.comp (differentiable_pi.mpr hcoeff)
  change Differentiable ℂ (fun z => supportPow A z)
  simp_rw [supportPow,RenyiLimitSupport.PetzSpectral.sf_eq A hA]
  exact (hD.const_mul (hA.eigenvectorUnitary : Matrix n n ℂ)).mul_const (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

end RenyiLimitSupport.RecoveryPowerCalculus

end

noncomputable section
open Matrix Set WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace RenyiLimitSupport.RecoveryMatrixCalculus
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
  [DecidableEq l] [DecidableEq m] [DecidableEq n]

def mulCLM : Matrix l m ℂ →L[ℂ] Matrix m n ℂ →L[ℂ] Matrix l n ℂ :=
  (mulLinearMap ℂ).mkContinuous₂ 1 (by intro A B; simpa using Matrix.l2_opNorm_mul A B)

lemma differentiable_mul {f : ℂ → Matrix l m ℂ} {g : ℂ → Matrix m n ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun z => f z*g z) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  change Differentiable ℂ (fun z => ∑ k, f z i k*g z k j)
  apply Differentiable.fun_sum
  intro k _
  exact ((differentiable_pi.mp (differentiable_pi.mp hf i)) k).mul
    ((differentiable_pi.mp (differentiable_pi.mp hg k)) j)

def tensorId : Matrix m m ℂ →⋆ₐ[ℂ] Matrix (m×n) (m×n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := one_kronecker_one
  map_mul' A B := by simpa using mul_kronecker_mul A B (1 : Matrix n n ℂ) 1
  map_zero' := by simp
  map_add' A B := add_kronecker A B 1
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change (z • (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix n n ℂ) = z • (1 : Matrix (m×n) (m×n) ℂ)
    rw [smul_kronecker,one_kronecker_one]
  map_star' A := by simp [star_eq_conjTranspose,conjTranspose_kronecker]

lemma tensorId_norm_le (A : Matrix m m ℂ) : ‖A ⊗ₖ (1 : Matrix n n ℂ)‖ ≤ ‖A‖ :=
  NonUnitalStarAlgHom.norm_apply_le (tensorId (m := m) (n := n)) A

def tensorIdCLM : Matrix m m ℂ →L[ℂ] Matrix (m×n) (m×n) ℂ :=
  (tensorId (m := m) (n := n)).toLinearMap.toContinuousLinearMap

@[simp] lemma tensorIdCLM_apply (A : Matrix m m ℂ) :
    tensorIdCLM (m := m) (n := n) A=A ⊗ₖ (1 : Matrix n n ℂ) := rfl

variable {a : Type} [Fintype a] [DecidableEq a]
lemma supportPow_norm_le_real (A : Matrix a a ℂ) (hA : A.IsHermitian) (z : ℂ) :
    ‖supportPow A z‖ ≤ ‖supportPow A (z.re : ℂ)‖ := by
  have hz : (z.re : ℂ)+(z.im : ℂ)*Complex.I=z := Complex.re_add_im z
  calc
    _ = ‖supportPow A (z.re : ℂ)*supportPow A ((z.im : ℂ)*Complex.I)‖ := by rw [RenyiLimitSupport.PetzSpectral.pow_add A hA,hz]
    _ ≤ ‖supportPow A (z.re : ℂ)‖*‖supportPow A ((z.im : ℂ)*Complex.I)‖ := norm_mul_le _ _
    _ ≤ ‖supportPow A (z.re : ℂ)‖*1 := mul_le_mul_of_nonneg_left
      (RenyiLimitSupport.RecoveryPowerCalculus.supportPow_imag_norm_le_one A hA z.im) (norm_nonneg _)
    _ = _ := mul_one _

lemma supportPow_strip_bounded (A : Matrix a a ℂ) (hA : A.IsHermitian) (u v : ℝ) :
    Bornology.IsBounded ((supportPow A) '' {z : ℂ | u ≤ z.re ∧ z.re ≤ v}) := by
  have hC : Continuous (fun r : ℝ => supportPow A (r : ℂ)) :=
    (RenyiLimitSupport.RecoveryPowerCalculus.supportPow_differentiable A hA).continuous.comp Complex.continuous_ofReal
  obtain ⟨B,hB⟩ := ((isCompact_Icc : IsCompact (Icc u v)).image hC).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨B,?_⟩
  rintro w ⟨z,hz,rfl⟩
  exact (supportPow_norm_le_real A hA z).trans (hB _ ⟨z.re,hz,rfl⟩)

end RenyiLimitSupport.RecoveryMatrixCalculus

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryStinespring
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma kraus_isometry (N : QChannel a b) : (isometricExt N)ᴴ*isometricExt N=1 := by
  classical
  calc
    _ = ∑ i, (N.K i)ᴴ*N.K i := by
      ext j k
      simp only [Matrix.mul_apply,conjTranspose_apply,isometricExt,Matrix.of_apply,
        Fintype.sum_prod_type,Matrix.sum_apply]
      exact Finset.sum_comm
    _ = _ := N.complete

lemma kron_left_isometry (N : QChannel a b) (Y : Matrix b b ℂ) (p : b×N.ι) (j : a) :
    ((Y ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*isometricExt N) p j=(Y*N.K p.2) p.1 j := by
  classical
  simp [Matrix.mul_apply,Fintype.sum_prod_type,kroneckerMap_apply,Matrix.one_apply,isometricExt]

lemma adjoint_dilation (N : QChannel a b) (Y : Matrix b b ℂ) :
    (isometricExt N)ᴴ*(Y ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*isometricExt N=adjointMap N Y := by
  classical
  rw [Matrix.mul_assoc]
  have hY : ((Y ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*isometricExt N) =
      Matrix.of (fun p k => (Y*N.K p.2) p.1 k) := by
    ext p k
    exact kron_left_isometry N Y p k
  rw [hY]
  ext j k
  change (∑ p : b×N.ι, conj (N.K p.2 p.1 j)*(Y*N.K p.2) p.1 k) = _
  rw [Fintype.sum_prod_type]
  simp only [adjointMap,Matrix.sum_apply,Prod.fst,Prod.snd,Matrix.mul_assoc,Matrix.mul_apply,conjTranspose_apply]
  exact Finset.sum_comm

end RenyiLimitSupport.RecoveryStinespring

end

noncomputable section
open Matrix Set WildeQIT WildeQIT.Recover RenyiLimitSupport.RecoveryMatrixCalculus
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryCurve
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def curve (ρ σ : Matrix a a ℂ) (N : QChannel a b) (z : ℂ) : Matrix (b×N.ι) a ℂ :=
  ((supportPow (N.apply ρ) (z/2)*supportPow (N.apply σ) (-(z/2))) ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*
    isometricExt N*supportPow σ (z/2)*supportPow ρ (1/2)

lemma differentiable (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : Differentiable ℂ (curve ρ σ N) := by
  have hd : Differentiable ℂ (fun z : ℂ => z/2) := by fun_prop
  have hP := (RenyiLimitSupport.RecoveryPowerCalculus.supportPow_differentiable (N.apply ρ)
    (RenyiLimitSupport.PetzChannel.map_positive N ρ hρ).isHermitian).comp hd
  have hQ := (RenyiLimitSupport.RecoveryPowerCalculus.supportPow_differentiable (N.apply σ)
    (RenyiLimitSupport.PetzChannel.map_positive N σ hσ).isHermitian).comp hd.neg
  have hS := (RenyiLimitSupport.RecoveryPowerCalculus.supportPow_differentiable σ hσ.isHermitian).comp hd
  have hT := (tensorIdCLM (m := b) (n := N.ι)).differentiable.comp (hP.mul hQ)
  exact differentiable_mul (differentiable_mul (differentiable_mul hT (differentiable_const _)) hS)
    (differentiable_const _)

lemma renyiOp_eq (ρ σ : Matrix a a ℂ) (N : QChannel a b) (α : ℝ) :
    renyiOp ρ σ N α=curve ρ σ N (((1-α)/α : ℝ) : ℂ) := by
  unfold renyiOp curve
  congr 4 <;> push_cast <;> ring

lemma bounded_mul {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n]
    {S : Set ℂ} {f : ℂ → Matrix l m ℂ} {g : ℂ → Matrix m n ℂ}
    (hf : Bornology.IsBounded (f '' S)) (hg : Bornology.IsBounded (g '' S)) :
    Bornology.IsBounded ((fun z => f z*g z) '' S) := by
  obtain ⟨B,hB⟩ := hf.exists_norm_le
  obtain ⟨C,hC⟩ := hg.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max 0 B*max 0 C,?_⟩
  rintro w ⟨z,hz,rfl⟩
  exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul
    ((hB _ ⟨z,hz,rfl⟩).trans (le_max_right _ _))
    ((hC _ ⟨z,hz,rfl⟩).trans (le_max_right _ _)) (norm_nonneg _) (le_max_left _ _))

lemma bounded (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    Bornology.IsBounded ((curve ρ σ N) '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}) := by
  let S : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}
  have hP : Bornology.IsBounded ((fun z : ℂ => supportPow (N.apply ρ) (z/2)) '' S) := by
    apply (supportPow_strip_bounded (N.apply ρ) (RenyiLimitSupport.PetzChannel.map_positive N ρ hρ).isHermitian 0 (1/2)).subset
    rintro w ⟨z,hz,rfl⟩
    refine ⟨z/2,?_,rfl⟩
    dsimp [S] at hz
    constructor <;> simp only [Complex.div_ofNat_re] <;> linarith [hz.1,hz.2]
  have hQ : Bornology.IsBounded ((fun z : ℂ => supportPow (N.apply σ) (-(z/2))) '' S) := by
    apply (supportPow_strip_bounded (N.apply σ) (RenyiLimitSupport.PetzChannel.map_positive N σ hσ).isHermitian (-(1/2)) 0).subset
    rintro w ⟨z,hz,rfl⟩
    refine ⟨-(z/2),?_,rfl⟩
    dsimp [S] at hz
    constructor <;> simp only [Complex.neg_re,Complex.div_ofNat_re] <;> linarith [hz.1,hz.2]
  have hT : Bornology.IsBounded ((fun z =>
      ((supportPow (N.apply ρ) (z/2)*supportPow (N.apply σ) (-(z/2))) ⊗ₖ (1 : Matrix N.ι N.ι ℂ))) '' S) := by
    simpa only [Set.image_image,Function.comp_def,tensorIdCLM_apply] using
      (tensorIdCLM (m := b) (n := N.ι)).lipschitz.isBounded_image (bounded_mul hP hQ)
  have hS : Bornology.IsBounded ((fun z : ℂ => supportPow σ (z/2)) '' S) := by
    apply (supportPow_strip_bounded σ hσ.isHermitian 0 (1/2)).subset
    rintro w ⟨z,hz,rfl⟩
    refine ⟨z/2,?_,rfl⟩
    dsimp [S] at hz
    constructor <;> simp only [Complex.div_ofNat_re] <;> linarith [hz.1,hz.2]
  have hconst (A : Matrix a a ℂ) : Bornology.IsBounded ((fun _ : ℂ => A) '' S) :=
    (Bornology.isBounded_singleton (x := A)).subset (by rintro _ ⟨_,_,rfl⟩; rfl)
  have hU : Bornology.IsBounded ((fun _ : ℂ => isometricExt N) '' S) :=
    (Bornology.isBounded_singleton (x := isometricExt N)).subset (by rintro _ ⟨_,_,rfl⟩; rfl)
  exact bounded_mul (bounded_mul (bounded_mul hT hU) hS) (hconst (supportPow ρ (1/2)))

end RenyiLimitSupport.RecoveryCurve

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.RecoveryCurve RenyiLimitSupport.PetzSpectral RenyiLimitSupport.PetzChannel
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryCurveGram
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma curve_gram (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (z : ℂ) :
    (curve ρ σ N z)ᴴ*curve ρ σ N z =
      supportPow ρ (1/2)*supportPow σ (conj (z/2))*
        adjointMap N (supportPow (N.apply σ) (-conj (z/2))*
          supportPow (N.apply ρ) (conj (z/2)+z/2)*supportPow (N.apply σ) (-(z/2)))*
        supportPow σ (z/2)*supportPow ρ (1/2) := by
  have hP := (map_positive N ρ hρ).isHermitian
  have hQ := (map_positive N σ hσ).isHermitian
  let X := supportPow (N.apply ρ) (z/2)*supportPow (N.apply σ) (-(z/2))
  have hX : Xᴴ*X=supportPow (N.apply σ) (-conj (z/2))*
      supportPow (N.apply ρ) (conj (z/2)+z/2)*supportPow (N.apply σ) (-(z/2)) := by
    dsimp [X]
    simp only [conjTranspose_mul,pow_star _ hP,pow_star _ hQ,map_neg,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (supportPow (N.apply ρ) (conj (z/2)))
      (supportPow (N.apply ρ) (z/2)),pow_add _ hP]
  have hT : (X ⊗ₖ (1 : Matrix N.ι N.ι ℂ))ᴴ*(X ⊗ₖ (1 : Matrix N.ι N.ι ℂ)) =
      (Xᴴ*X) ⊗ₖ (1 : Matrix N.ι N.ι ℂ) := by
    rw [conjTranspose_kronecker,conjTranspose_one,← mul_kronecker_mul,Matrix.one_mul]
  calc
    _ = supportPow ρ (1/2)*supportPow σ (conj (z/2))*
        ((isometricExt N)ᴴ*((Xᴴ*X) ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*isometricExt N)*
          supportPow σ (z/2)*supportPow ρ (1/2) := by
      change (((X ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*isometricExt N*supportPow σ (z/2)*supportPow ρ (1/2))ᴴ*
        ((X ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*isometricExt N*supportPow σ (z/2)*supportPow ρ (1/2))) = _
      simp only [conjTranspose_mul,half_star ρ hρ,pow_star σ hσ.isHermitian,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (X ⊗ₖ (1 : Matrix N.ι N.ι ℂ))ᴴ
        (X ⊗ₖ (1 : Matrix N.ι N.ι ℂ)),hT]
    _ = _ := by rw [RenyiLimitSupport.RecoveryStinespring.adjoint_dilation,hX]

end RenyiLimitSupport.RecoveryCurveGram

end

noncomputable section
open Matrix
open scoped MatrixOrder
namespace RenyiLimitSupport.RecoveryCurveRight
variable {a : Type} [Fintype a] [DecidableEq a]
lemma sqrt_star (A : Matrix a a ℂ) : (CFC.sqrt A)ᴴ=CFC.sqrt A := by
  change star (CFC.sqrt A)=CFC.sqrt A
  exact (CFC.sqrt_nonneg A).star_eq
end RenyiLimitSupport.RecoveryCurveRight
end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.PetzSpectral RenyiLimitSupport.PetzChannel
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoverySupport
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma mul_eq_zero_of_supp {ρ σ : Matrix a a ℂ} (h : SuppSubset ρ σ)
    {m : Type} [Fintype m] (C : Matrix a m ℂ) (hC : σ*C=0) : ρ*C=0 := by
  ext i j
  have hj : (fun k => C k j) ∈ LinearMap.ker (Matrix.toLin' σ) := by
    change σ*ᵥ(fun k => C k j)=0
    funext k
    exact congrFun (congrFun hC k) j
  have hj' := h hj
  change ρ*ᵥ(fun k => C k j)=0 at hj'
  exact congrFun hj' i

lemma pow_mul_support (ρ σ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) (z : ℂ) : supportPow ρ z*supportProj σ=supportPow ρ z := by
  have hσP : σ*supportProj σ=σ := by
    simpa only [pow_one σ hσ] using support_pow_right σ hσ.isHermitian 1
  have hC : σ*(1-supportProj σ)=0 := by rw [Matrix.mul_sub,Matrix.mul_one,hσP,sub_self]
  have hρC := mul_eq_zero_of_supp hsupp (1-supportProj σ) hC
  have he : supportPow ρ (z-1)*ρ=supportPow ρ z := by
    calc
      _ = supportPow ρ (z-1)*supportPow ρ 1 := by rw [pow_one ρ hρ]
      _ = _ := by rw [pow_add ρ hρ.isHermitian,sub_add_cancel]
  have hzC : supportPow ρ z*(1-supportProj σ)=0 := by
    rw [← he,Matrix.mul_assoc,hρC,Matrix.mul_zero]
  rw [Matrix.mul_sub,Matrix.mul_one] at hzC
  exact (sub_eq_zero.mp hzC).symm

lemma support_mul_pow (ρ σ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) (z : ℂ) : supportProj σ*supportPow ρ z=supportPow ρ z := by
  have hh := congrArg Matrix.conjTranspose (pow_mul_support ρ σ hρ hσ hsupp (conj z))
  simpa only [conjTranspose_mul,support_star σ hσ.isHermitian,pow_star ρ hρ.isHermitian,
    map_star,star_star,Complex.conj_conj] using hh

lemma map_supp (ρ σ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) (N : QChannel a b) : SuppSubset (N.apply ρ) (N.apply σ) := by
  intro x hx
  change N.apply σ*ᵥx=0 at hx
  change N.apply ρ*ᵥx=0
  have hsum : ∑ i, star ((N.K i)ᴴ*ᵥx) ⬝ᵥ σ*ᵥ((N.K i)ᴴ*ᵥx)=0 := by
    have hh : star x ⬝ᵥ N.apply σ*ᵥx=0 := by rw [hx,dotProduct_zero]
    simpa only [QChannel.apply,Matrix.sum_mulVec,dotProduct_sum,← Matrix.mulVec_mulVec,
      dotProduct_mulVec,← Matrix.vecMul_vecMul,star_mulVec,conjTranspose_conjTranspose] using hh
  have hz (i : N.ι) : σ*ᵥ((N.K i)ᴴ*ᵥx)=0 := by
    apply (hσ.dotProduct_mulVec_zero_iff _).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hσ.dotProduct_mulVec_nonneg _)).mp hsum i (Finset.mem_univ _)
  have hρz (i : N.ι) : ρ*ᵥ((N.K i)ᴴ*ᵥx)=0 := hsupp (hz i)
  simp only [QChannel.apply,Matrix.sum_mulVec,← Matrix.mulVec_mulVec,hρz,Matrix.mulVec_zero,Finset.sum_const_zero]

end RenyiLimitSupport.RecoverySupport

end

noncomputable section
open Matrix WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryPowerDerivative
variable {n : Type} [Fintype n] [DecidableEq n]

def logNat (A : Matrix n n ℂ) : Matrix n n ℂ := spectralFun (fun x => (Real.log x : ℂ)) A

lemma hasDerivAt_power_zero (A : Matrix n n ℂ) (hA : A.IsHermitian) (c : ℝ) :
    HasDerivAt (fun t : ℝ => supportPow A ((c*t : ℝ) : ℂ)) (c • logNat A) 0 := by
  let U := hA.eigenvectorUnitary
  let f (t : ℝ) (i : n) : ℂ := if hA.eigenvalues i=0 then 0 else
    Complex.exp (((c*t : ℝ) : ℂ)*(Real.log (hA.eigenvalues i) : ℂ))
  let d (i : n) : ℂ := c • (Real.log (hA.eigenvalues i) : ℂ)
  have hf (i : n) : HasDerivAt (fun t : ℝ => f t i) (d i) 0 := by
    by_cases hi : hA.eigenvalues i=0
    · simp only [f,if_pos hi,d,hi,Real.log_zero,Complex.ofReal_zero,smul_zero]
      exact hasDerivAt_const _ _
    · have hh := (((hasDerivAt_id (0 : ℝ)).const_mul c).ofReal_comp.mul_const
        (Real.log (hA.eigenvalues i) : ℂ)).cexp
      simpa [f,if_neg hi,d,Complex.real_smul,mul_comm] using hh
  have hD : HasDerivAt (fun t : ℝ => diagonal (f t)) (diagonal d) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    by_cases hij : i=j
    · subst j
      simpa only [diagonal_apply_eq] using hf i
    · simp only [diagonal_apply_ne _ hij]
      exact hasDerivAt_const _ _
  have hU := (hD.const_mul (U : Matrix n n ℂ)).mul_const (U : Matrix n n ℂ)ᴴ
  have he (t : ℝ) : supportPow A ((c*t : ℝ) : ℂ)=(U : Matrix n n ℂ)*diagonal (f t)*(U : Matrix n n ℂ)ᴴ := by
    rw [supportPow,RenyiLimitSupport.PetzSpectral.sf_eq A hA]
  have hd : (U : Matrix n n ℂ)*diagonal d*(U : Matrix n n ℂ)ᴴ=c • logNat A := by
    have hdD : diagonal d=c • diagonal (fun i => (Real.log (hA.eigenvalues i) : ℂ)) :=
      diagonal_smul c _
    rw [hdD,Matrix.mul_smul,Matrix.smul_mul]
    simp only [logNat,RenyiLimitSupport.PetzSpectral.sf_eq A hA]
    rfl
  simpa only [← he,hd] using hU

end RenyiLimitSupport.RecoveryPowerDerivative

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.PetzSpectral RenyiLimitSupport.PetzChannel RenyiLimitSupport.RecoverySupport RenyiLimitSupport.RecoveryPowerDerivative
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryChannelSupport
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma logNat_mul_support (A : Matrix a a ℂ) (hA : A.IsHermitian) : logNat A*supportProj A=logNat A := by
  unfold logNat supportProj
  rw [sf_mul A hA]
  apply sf_congr A hA
  intro i
  by_cases hi : hA.eigenvalues i=0 <;> simp [hi]

lemma logNat_star (A : Matrix a a ℂ) (hA : A.IsHermitian) : (logNat A)ᴴ=logNat A := by
  unfold logNat
  rw [sf_star A hA]
  apply sf_congr A hA
  intro i
  simp

lemma support_mul_logNat (A : Matrix a a ℂ) (hA : A.IsHermitian) : supportProj A*logNat A=logNat A := by
  have hh := congrArg Matrix.conjTranspose (logNat_mul_support A hA)
  simpa only [conjTranspose_mul,logNat_star A hA,support_star A hA] using hh

lemma logNat_mul_support_of_supp (ρ σ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) : logNat ρ*supportProj σ=logNat ρ := by
  have hp : supportProj ρ*supportProj σ=supportProj ρ := by
    simpa only [RenyiLimitSupport.PetzSpectral.pow_zero] using pow_mul_support ρ σ hρ hσ hsupp 0
  calc
    _ = (logNat ρ*supportProj ρ)*supportProj σ := by rw [logNat_mul_support ρ hρ.isHermitian]
    _ = _ := by rw [Matrix.mul_assoc,hp,logNat_mul_support ρ hρ.isHermitian]

lemma support_mul_logNat_of_supp (ρ σ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) : supportProj σ*logNat ρ=logNat ρ := by
  have hh := congrArg Matrix.conjTranspose (logNat_mul_support_of_supp ρ σ hρ hσ hsupp)
  simpa only [conjTranspose_mul,logNat_star ρ hρ.isHermitian,support_star σ hσ.isHermitian] using hh

lemma adjoint_support_fixes (ρ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (N : QChannel a b) :
    adjointMap N (supportProj (N.apply ρ))*ρ=ρ := by
  let D := adjointMap N (1-supportProj (N.apply ρ))
  have hD : D.PosSemidef := adjoint_positive N _ (support_complement_pos _ (map_positive N ρ hρ))
  have hd : D=1-adjointMap N (supportProj (N.apply ρ)) := by dsimp [D]; rw [adjoint_sub,adjoint_one]
  have hs : supportPow ρ (1/2)*D*supportPow ρ (1/2)=0 := by
    rw [← petz_defect N ρ hρ,petz_perfect N ρ hρ,sub_self]
  let C := CFC.sqrt D
  have hC : Cᴴ=C := RenyiLimitSupport.RecoveryCurveRight.sqrt_star D
  have hCC : C*C=D := CFC.sqrt_mul_sqrt_self D hD.nonneg
  have hx : C*supportPow ρ (1/2)=0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [conjTranspose_mul,hC,half_star ρ hρ,Matrix.mul_assoc,
      ← Matrix.mul_assoc C C,hCC,← Matrix.mul_assoc,hs]
  have hDh : D*supportPow ρ (1/2)=0 := by rw [← hCC,Matrix.mul_assoc,hx,Matrix.mul_zero]
  have hDρ : D*ρ=0 := by rw [← pow_half_square ρ hρ,← Matrix.mul_assoc,hDh,Matrix.zero_mul]
  rw [hd,Matrix.sub_mul,Matrix.one_mul] at hDρ
  exact (sub_eq_zero.mp hDρ).symm

lemma support_adjoint_fixes (ρ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (N : QChannel a b) :
    ρ*adjointMap N (supportProj (N.apply ρ))=ρ := by
  have hp : (supportProj (N.apply ρ)).PosSemidef := by
    have hi : supportProj (N.apply ρ)*supportProj (N.apply ρ)=supportProj (N.apply ρ) :=
      support_square _ (map_positive N ρ hρ).isHermitian
    have hh := posSemidef_conjTranspose_mul_self (supportProj (N.apply ρ))
    rwa [support_star _ (map_positive N ρ hρ).isHermitian,hi] at hh
  have hA := (adjoint_positive N _ hp).isHermitian
  have hh := congrArg Matrix.conjTranspose (adjoint_support_fixes ρ hρ N)
  simpa only [conjTranspose_mul,hA.eq,hρ.isHermitian.eq] using hh

end RenyiLimitSupport.RecoveryChannelSupport

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.PetzSpectral RenyiLimitSupport.PetzChannel RenyiLimitSupport.RecoverySupport RenyiLimitSupport.RecoveryCurve
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryRenyiBase
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma gram_zero (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    (curve ρ σ N 0)ᴴ*curve ρ σ N 0=ρ := by
  have hP := map_positive N ρ hρ
  have hQ := map_positive N σ hσ
  have hPQ := map_supp ρ σ hρ hσ hsupp N
  have hqp : supportProj (N.apply σ)*supportProj (N.apply ρ)=supportProj (N.apply ρ) := by
    simpa only [RenyiLimitSupport.PetzSpectral.pow_zero] using support_mul_pow _ _ hP hQ hPQ 0
  have hpq : supportProj (N.apply ρ)*supportProj (N.apply σ)=supportProj (N.apply ρ) := by
    simpa only [RenyiLimitSupport.PetzSpectral.pow_zero] using pow_mul_support _ _ hP hQ hPQ 0
  rw [RenyiLimitSupport.RecoveryCurveGram.curve_gram ρ σ N hρ hσ 0]
  simp only [zero_div,map_zero,neg_zero,zero_add,RenyiLimitSupport.PetzSpectral.pow_zero,hqp,hpq]
  rw [pow_mul_support ρ σ hρ hσ hsupp (1/2)]
  simp only [Matrix.mul_assoc]
  rw [support_mul_pow ρ σ hρ hσ hsupp (1/2)]
  rw [← Matrix.mul_assoc,← petz_input N ρ hρ,petz_perfect N ρ hρ]

lemma renyiOp_one_gram (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    (renyiOp ρ σ N 1)ᴴ*renyiOp ρ σ N 1=ρ := by
  rw [renyiOp_eq]
  norm_num only [sub_self,zero_div,Complex.ofReal_zero]
  exact gram_zero ρ σ N hρ hσ hsupp

lemma renyiQ_one (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) : renyiQ ρ σ N 1=1 := by
  unfold renyiQ
  rw [renyiOp_one_gram ρ σ N hρ.1 hσ hsupp,Complex.ofReal_one,pow_one ρ hρ.1,hρ.2]
  rfl

end RenyiLimitSupport.RecoveryRenyiBase

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.PetzSpectral RenyiLimitSupport.PetzChannel RenyiLimitSupport.RecoverySupport RenyiLimitSupport.RecoveryPowerDerivative RenyiLimitSupport.RecoveryChannelSupport RenyiLimitSupport.RecoveryCurve
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryTraceFamily
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma hasDerivAt_mul_rect {l m n : Type} [Fintype l] [Fintype m] [Fintype n]
    {f : ℝ → Matrix l m ℂ} {g : ℝ → Matrix m n ℂ}
    {f' : Matrix l m ℂ} {g' : Matrix m n ℂ}
    (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0) :
    HasDerivAt (fun t => f t*g t) (f'*g 0+f 0*g') 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k) j))
  simpa only [Matrix.add_apply,Matrix.mul_apply,Finset.sum_add_distrib,Pi.mul_apply] using hh

lemma hasDerivAt_adjoint (N : QChannel a b) (f : ℝ → Matrix b b ℂ) (f' : Matrix b b ℂ)
    (hf : HasDerivAt f f' 0) : HasDerivAt (fun t => adjointMap N (f t)) (adjointMap N f') 0 := by
  unfold adjointMap
  have hi (i : N.ι) := hasDerivAt_mul_rect
    (hasDerivAt_mul_rect (hasDerivAt_const (0 : ℝ) (N.K i)ᴴ) hf)
    (hasDerivAt_const (0 : ℝ) (N.K i))
  simpa only [Matrix.zero_mul,zero_add,Matrix.mul_zero,add_zero] using HasDerivAt.fun_sum (fun i _ => hi i)

lemma hasDerivAt_trace (f : ℝ → Matrix a a ℂ) (f' : Matrix a a ℂ)
    (hf : HasDerivAt f f' 0) : HasDerivAt (fun t => (f t).trace) f'.trace 0 := by
  unfold Matrix.trace Matrix.diag
  exact HasDerivAt.fun_sum (fun i _ => hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) i)

def X (σ : Matrix a a ℂ) (t : ℝ) := supportPow σ (((1/2 : ℝ)*t : ℝ) : ℂ)
def Y (σ : Matrix a a ℂ) (N : QChannel a b) (t : ℝ) := supportPow (N.apply σ) (((-1/2 : ℝ)*t : ℝ) : ℂ)
def Z (ρ : Matrix a a ℂ) (N : QChannel a b) (t : ℝ) := supportPow (N.apply ρ) (t : ℂ)
def input (ρ σ : Matrix a a ℂ) (t : ℝ) := X σ t*ρ*X σ t
def output (ρ σ : Matrix a a ℂ) (N : QChannel a b) (t : ℝ) := Y σ N t*Z ρ N t*Y σ N t

def traceFamily (ρ σ : Matrix a a ℂ) (N : QChannel a b) (t : ℝ) : ℂ :=
  (input ρ σ t*adjointMap N (output ρ σ N t)).trace

lemma input_zero (ρ σ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) : input ρ σ 0=ρ := by
  unfold input X
  simp only [mul_zero,Complex.ofReal_zero,RenyiLimitSupport.PetzSpectral.pow_zero]
  have hl : supportProj σ*ρ=ρ := by simpa only [RenyiLimitSupport.PetzSpectral.pow_one ρ hρ] using support_mul_pow ρ σ hρ hσ hsupp 1
  have hr : ρ*supportProj σ=ρ := by simpa only [RenyiLimitSupport.PetzSpectral.pow_one ρ hρ] using pow_mul_support ρ σ hρ hσ hsupp 1
  rw [hl,hr]

lemma output_zero (ρ σ : Matrix a a ℂ) (N : QChannel a b) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) : output ρ σ N 0=supportProj (N.apply ρ) := by
  unfold output Y Z
  simp only [mul_zero,Complex.ofReal_zero,RenyiLimitSupport.PetzSpectral.pow_zero]
  have hPQ := map_supp ρ σ hρ hσ hsupp N
  have hl : supportProj (N.apply σ)*supportProj (N.apply ρ)=supportProj (N.apply ρ) := by
    simpa only [RenyiLimitSupport.PetzSpectral.pow_zero] using support_mul_pow _ _ (map_positive N ρ hρ) (map_positive N σ hσ) hPQ 0
  have hr : supportProj (N.apply ρ)*supportProj (N.apply σ)=supportProj (N.apply ρ) := by
    simpa only [RenyiLimitSupport.PetzSpectral.pow_zero] using pow_mul_support _ _ (map_positive N ρ hρ) (map_positive N σ hσ) hPQ 0
  rw [hl,hr]

lemma hasDerivAt_input (ρ σ : Matrix a a ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) : HasDerivAt (input ρ σ)
      ((1/2 : ℝ) • (logNat σ*ρ+ρ*logNat σ)) 0 := by
  change HasDerivAt (fun t => X σ t*ρ*X σ t) _ 0
  have hX : HasDerivAt (X σ) ((1/2 : ℝ) • logNat σ) 0 := hasDerivAt_power_zero σ hσ.isHermitian _
  have hh := hasDerivAt_mul_rect (hasDerivAt_mul_rect hX (hasDerivAt_const (0 : ℝ) ρ)) hX
  have hl : supportProj σ*ρ=ρ := by simpa only [RenyiLimitSupport.PetzSpectral.pow_one ρ hρ] using support_mul_pow ρ σ hρ hσ hsupp 1
  have hr : ρ*supportProj σ=ρ := by simpa only [RenyiLimitSupport.PetzSpectral.pow_one ρ hρ] using pow_mul_support ρ σ hρ hσ hsupp 1
  simpa only [input,X,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,mul_zero,Complex.ofReal_zero,RenyiLimitSupport.PetzSpectral.pow_zero,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc,hl,hr,smul_add] using hh

lemma hasDerivAt_output (ρ σ : Matrix a a ℂ) (N : QChannel a b) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : SuppSubset ρ σ) : HasDerivAt (output ρ σ N)
      ((-1/2 : ℝ) • (logNat (N.apply σ)*supportProj (N.apply ρ)) + logNat (N.apply ρ) +
        (-1/2 : ℝ) • (supportProj (N.apply ρ)*logNat (N.apply σ))) 0 := by
  change HasDerivAt (fun t => Y σ N t*Z ρ N t*Y σ N t) _ 0
  have hP := map_positive N ρ hρ
  have hQ := map_positive N σ hσ
  have hPQ := map_supp ρ σ hρ hσ hsupp N
  have hY : HasDerivAt (Y σ N) ((-1/2 : ℝ) • logNat (N.apply σ)) 0 := hasDerivAt_power_zero _ hQ.isHermitian _
  have hZ : HasDerivAt (Z ρ N) (logNat (N.apply ρ)) 0 := by
    change HasDerivAt (fun t : ℝ => supportPow (N.apply ρ) (t : ℂ)) _ 0
    simpa only [one_mul,one_smul] using hasDerivAt_power_zero (N.apply ρ) hP.isHermitian 1
  have hh := hasDerivAt_mul_rect (hasDerivAt_mul_rect hY hZ) hY
  have hl : supportProj (N.apply σ)*supportProj (N.apply ρ)=supportProj (N.apply ρ) := by
    simpa only [RenyiLimitSupport.PetzSpectral.pow_zero] using support_mul_pow _ _ hP hQ hPQ 0
  have hr : supportProj (N.apply ρ)*supportProj (N.apply σ)=supportProj (N.apply ρ) := by
    simpa only [RenyiLimitSupport.PetzSpectral.pow_zero] using pow_mul_support _ _ hP hQ hPQ 0
  have hL := support_mul_logNat_of_supp _ _ hP hQ hPQ
  have hR := logNat_mul_support_of_supp _ _ hP hQ hPQ
  simpa only [output,Y,Z,mul_zero,Complex.ofReal_zero,RenyiLimitSupport.PetzSpectral.pow_zero,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,
    Matrix.mul_assoc,hl,hr,hL,hR] using hh

end RenyiLimitSupport.RecoveryTraceFamily

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.PetzSpectral RenyiLimitSupport.PetzChannel RenyiLimitSupport.RecoverySupport RenyiLimitSupport.RecoveryPowerDerivative RenyiLimitSupport.RecoveryChannelSupport RenyiLimitSupport.RecoveryCurve RenyiLimitSupport.RecoveryTraceFamily
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryEntropyTrace
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma trace_gram_sandwich (H X A : Matrix a a ℂ) :
    (H*X*A*X*H).trace=(X*(H*H)*X*A).trace := by
  rw [trace_mul_comm (H*X*A*X) H]
  simpa only [Matrix.mul_assoc] using trace_mul_cycle (H*H*X) A X

lemma adjoint_add (N : QChannel a b) (A B : Matrix b b ℂ) : adjointMap N (A+B)=adjointMap N A+adjointMap N B := by
  simp only [adjointMap,Matrix.mul_add,Matrix.add_mul,Finset.sum_add_distrib]
lemma adjoint_smul (N : QChannel a b) (r : ℝ) (A : Matrix b b ℂ) : adjointMap N (r • A)=r • adjointMap N A := by
  simp only [adjointMap,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum]

lemma trace_gram_eq (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (t : ℝ) :
    ((curve ρ σ N (t : ℂ))ᴴ*curve ρ σ N (t : ℂ)).trace=traceFamily ρ σ N t := by
  rw [RenyiLimitSupport.RecoveryCurveGram.curve_gram ρ σ N hρ hσ]
  have hc : conj ((t : ℂ)/2)=(t : ℂ)/2 := by simp [map_ofNat]
  have ht : (t : ℂ)/2+(t : ℂ)/2=(t : ℂ) := by ring
  have hX : supportPow σ ((t : ℂ)/2)=X σ t := by unfold X; congr 1; push_cast; ring
  have hY : supportPow (N.apply σ) (-((t : ℂ)/2))=Y σ N t := by unfold Y; congr 1; push_cast; ring
  rw [hc,ht]
  simp only [hX,hY]
  change (supportPow ρ (1/2)*X σ t*adjointMap N (output ρ σ N t)*X σ t*supportPow ρ (1/2)).trace =
    (X σ t*ρ*X σ t*adjointMap N (output ρ σ N t)).trace
  rw [trace_gram_sandwich,pow_half_square ρ hρ]

lemma hasDerivAt_traceFamily (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    HasDerivAt (traceFamily ρ σ N)
      ((ρ*logNat σ).trace+(N.apply ρ*logNat (N.apply ρ)).trace-
        (N.apply ρ*logNat (N.apply σ)).trace) 0 := by
  let P := N.apply ρ
  let Q := N.apply σ
  let PP := supportProj P
  let W := adjointMap N PP
  have hPP : PP*P=P := support_mul P (map_positive N ρ hρ)
  have hPP' : P*PP=P := by
    simpa only [RenyiLimitSupport.PetzSpectral.pow_one P (map_positive N ρ hρ)] using support_pow_right P (map_positive N ρ hρ).isHermitian 1
  have h1 : (logNat σ*ρ*W).trace=(ρ*logNat σ).trace := by
    rw [Matrix.mul_assoc,support_adjoint_fixes ρ hρ N,trace_mul_comm]
  have h2 : (ρ*logNat σ*W).trace=(ρ*logNat σ).trace := by
    rw [trace_mul_cycle,adjoint_support_fixes ρ hρ N]
  have h3 : (ρ*adjointMap N (logNat Q*PP)).trace=(P*logNat Q).trace := by
    rw [trace_dual,← Matrix.mul_assoc,trace_mul_cycle,hPP]
  have h4 : (ρ*adjointMap N (logNat P)).trace=(P*logNat P).trace := trace_dual N ρ (logNat P)
  have h5 : (ρ*adjointMap N (PP*logNat Q)).trace=(P*logNat Q).trace := by
    rw [trace_dual,← Matrix.mul_assoc,hPP']
  have hi := hasDerivAt_input ρ σ hρ hσ hsupp
  have ho := hasDerivAt_output ρ σ N hρ hσ hsupp
  have ha := hasDerivAt_adjoint N _ _ ho
  have hh := hasDerivAt_trace _ _ (hi.mul ha)
  rw [input_zero ρ σ hρ hσ hsupp,output_zero ρ σ N hρ hσ hsupp] at hh
  have he : (((1/2 : ℝ) • (logNat σ*ρ+ρ*logNat σ))*W+
      ρ*adjointMap N ((-1/2 : ℝ) • (logNat Q*PP)+logNat P+(-1/2 : ℝ) • (PP*logNat Q))).trace =
      (ρ*logNat σ).trace+(P*logNat P).trace-(P*logNat Q).trace := by
    simp only [adjoint_add,adjoint_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,
      trace_add,trace_smul,h1,h2,h3,h4,h5]
    simp only [Complex.real_smul]
    push_cast
    ring
  change HasDerivAt (traceFamily ρ σ N) _ 0 at hh
  rw [he] at hh
  exact hh

end RenyiLimitSupport.RecoveryEntropyTrace

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.PetzSpectral RenyiLimitSupport.PetzChannel RenyiLimitSupport.RecoverySupport RenyiLimitSupport.RecoveryPowerDerivative
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryEntropyUnits
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma sf_smul (A : Matrix a a ℂ) (hA : A.IsHermitian) (r : ℝ) (f : ℝ → ℂ) :
    spectralFun (fun x => r • f x) A=r • spectralFun f A := by
  rw [sf_eq A hA,sf_eq A hA]
  have hd : diagonal (fun i => r • f (hA.eigenvalues i))=r • diagonal (fun i => f (hA.eigenvalues i)) := diagonal_smul r _
  rw [hd,Matrix.mul_smul,Matrix.smul_mul]

lemma log2Op_eq (A : Matrix a a ℂ) (hA : A.IsHermitian) : log2Op A=(Real.log 2)⁻¹ • logNat A := by
  unfold log2Op logNat
  rw [← sf_smul A hA]
  apply sf_congr A hA
  intro i
  by_cases hi : hA.eigenvalues i=0
  · simp [hi]
  · simp only [if_neg hi,Real.logb,Complex.ofReal_div,Complex.real_smul,Complex.ofReal_inv]
    ring

lemma entropy_cfc (A : Matrix a a ℂ) (hA : A.IsHermitian) : cfc (fun x : ℝ => x*Real.log x) A=A*logNat A := by
  rw [← RenyiLimitSupport.RecoveryPowerCalculus.spectral_real_eq_cfc A hA]
  unfold logNat
  conv_rhs => lhs; rw [← sf_id A hA]
  rw [sf_mul A hA]
  apply sf_congr A hA
  intro i
  simp

def naturalLoss (ρ σ : Matrix a a ℂ) (N : QChannel a b) : ℝ :=
  (ρ*logNat ρ).trace.re-(ρ*logNat σ).trace.re-
    (N.apply ρ*logNat (N.apply ρ)).trace.re+(N.apply ρ*logNat (N.apply σ)).trace.re

lemma entropy_difference (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    ((naturalLoss ρ σ N / Real.log 2 : ℝ) : EReal)=qRelEntropy ρ σ-qRelEntropy (N.apply ρ) (N.apply σ) := by
  have hm := map_supp ρ σ hρ hσ hsupp N
  rw [qRelEntropy,qRelEntropy,if_pos hsupp,if_pos hm]
  rw [log2Op_eq ρ hρ.isHermitian,log2Op_eq σ hσ.isHermitian,
    log2Op_eq (N.apply ρ) (map_positive N ρ hρ).isHermitian,
    log2Op_eq (N.apply σ) (map_positive N σ hσ).isHermitian]
  simp only [← smul_sub,Matrix.mul_smul,trace_smul,Complex.smul_re,smul_eq_mul]
  rw [← EReal.coe_sub]
  congr 1
  simp only [naturalLoss,Matrix.mul_sub,trace_sub,Complex.sub_re,div_eq_mul_inv]
  ring

end RenyiLimitSupport.RecoveryEntropyUnits

end

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder Topology Matrix.Norms.L2Operator
namespace RenyiLimitSupport.RecoveryTracePowerDeriv
variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
lemma hasDerivAt_trace_power (H : ℝ → Matrix n n ℂ) (hH : ContinuousAt H 1)
    (hPSD : ∀ α, (H α).PosSemidef) (d : ℝ)
    (hD : HasDerivAt (fun α => (H α).trace.re) d 1) :
    HasDerivAt (fun α => (cfc (fun x : ℝ => x^α) (H α)).trace.re)
      (d+(cfc (fun x : ℝ => x*Real.log x) (H 1)).trace.re) 1 := by
  exact Matrix.hasDerivAt_trace_rpow_at_one H hH hPSD d hD
end RenyiLimitSupport.RecoveryTracePowerDeriv
end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.RecoveryPowerDerivative RenyiLimitSupport.RecoveryEntropyUnits RenyiLimitSupport.RecoveryCurve RenyiLimitSupport.RecoveryTraceFamily RenyiLimitSupport.RecoveryEntropyTrace
open scoped MatrixOrder ComplexOrder ComplexConjugate Topology Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace RenyiLimitSupport.RecoveryRenyiDerivative
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def gram (ρ σ : Matrix a a ℂ) (N : QChannel a b) (α : ℝ) := (renyiOp ρ σ N α)ᴴ*renyiOp ρ σ N α

def theta (α : ℝ) : ℝ := (1-α)/α
lemma theta_one : theta 1=0 := by norm_num [theta]
lemma theta_deriv : HasDerivAt theta (-1) 1 := by
  change HasDerivAt (fun x : ℝ => (1-x)/x) (-1) 1
  have hh := ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (1 : ℝ))).div
    (hasDerivAt_id (1 : ℝ)) (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [Pi.div_def,Pi.sub_def,Pi.div_apply,Pi.sub_apply,id_eq,one_div,sub_self,zero_mul,sub_zero,one_pow,div_one,zero_sub,one_mul,mul_one] using hh

lemma gram_continuousAt (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : ContinuousAt (gram ρ σ N) 1 := by
  have ht : ContinuousAt (fun α : ℝ => (theta α : ℂ)) 1 :=
    Complex.continuous_ofReal.continuousAt.comp theta_deriv.continuousAt
  have hC : Continuous (curve ρ σ N) := (differentiable ρ σ N hρ hσ).continuous
  have hGram : Continuous (fun z : ℂ => (curve ρ σ N z)ᴴ*curve ρ σ N z) :=
    hC.matrix_conjTranspose.matrix_mul hC
  change ContinuousAt (fun α : ℝ => (renyiOp ρ σ N α)ᴴ*renyiOp ρ σ N α) 1
  simp_rw [renyiOp_eq]
  exact hGram.continuousAt.comp ht

lemma trace_gram_theta (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    (gram ρ σ N α).trace=traceFamily ρ σ N (theta α) := by
  unfold gram
  rw [renyiOp_eq]
  exact trace_gram_eq ρ σ N hρ hσ (theta α)

lemma hasDerivAt_trace_gram (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    HasDerivAt (fun α => (gram ρ σ N α).trace.re)
      (-((ρ*logNat σ).trace+(N.apply ρ*logNat (N.apply ρ)).trace-
        (N.apply ρ*logNat (N.apply σ)).trace)).re 1 := by
  let d : ℂ := (ρ*logNat σ).trace+(N.apply ρ*logNat (N.apply ρ)).trace-
        (N.apply ρ*logNat (N.apply σ)).trace
  have hd : HasDerivAt (traceFamily ρ σ N) d (theta 1) := by
    rw [theta_one]
    exact hasDerivAt_traceFamily ρ σ N hρ hσ hsupp
  have hc : HasDerivAt (fun α => (gram ρ σ N α).trace) (-d) 1 := by
    simp_rw [trace_gram_theta ρ σ N hρ hσ]
    simpa only [Function.comp_def,neg_one_smul] using hd.scomp 1 theta_deriv
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 1 hc
  exact hr

lemma hasDerivAt_renyiQ (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    HasDerivAt (renyiQ ρ σ N) (naturalLoss ρ σ N) 1 := by
  haveI : Nonempty a := by
    by_contra hn
    haveI : IsEmpty a := not_nonempty_iff.mp hn
    have ht : ρ.trace=0 := by simp [Matrix.trace,Matrix.diag]
    have hh := hρ.2
    rw [ht] at hh
    exact zero_ne_one hh
  let H := gram ρ σ N
  have hPSD (α : ℝ) : (H α).PosSemidef := posSemidef_conjTranspose_mul_self _
  have hH := gram_continuousAt ρ σ N hρ.1 hσ
  have hD := hasDerivAt_trace_gram ρ σ N hρ.1 hσ hsupp
  have hT := RenyiLimitSupport.RecoveryTracePowerDeriv.hasDerivAt_trace_power H hH hPSD _ hD
  have hbase : H 1=ρ := RenyiLimitSupport.RecoveryRenyiBase.renyiOp_one_gram ρ σ N hρ.1 hσ hsupp
  rw [hbase,entropy_cfc ρ hρ.1.isHermitian] at hT
  have hd : (-((ρ*logNat σ).trace+(N.apply ρ*logNat (N.apply ρ)).trace-
      (N.apply ρ*logNat (N.apply σ)).trace)).re+(ρ*logNat ρ).trace.re=naturalLoss ρ σ N := by
    simp only [naturalLoss,Complex.neg_re,Complex.add_re,Complex.sub_re]
    ring
  rw [hd] at hT
  apply hT.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with α hα
  change (supportPow (H α) (α : ℂ)).trace.re = (cfc (fun x : ℝ => x^α) (H α)).trace.re
  rw [RenyiLimitSupport.RecoveryPowerCalculus.supportPow_pos_eq_cfc _ (hPSD α) hα]

end RenyiLimitSupport.RecoveryRenyiDerivative

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover RenyiLimitSupport.RecoveryEntropyUnits RenyiLimitSupport.RecoveryRenyiDerivative Filter
open scoped MatrixOrder ComplexOrder ComplexConjugate Topology Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RenyiLimitSupport.RecoveryRenyiLimit
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma delta_limit (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    Tendsto (renyiDelta ρ σ N) (𝓝[≠] 1) (𝓝 (naturalLoss ρ σ N)) := by
  have hQ := hasDerivAt_renyiQ ρ σ N hρ hσ hsupp
  have hbase := RenyiLimitSupport.RecoveryRenyiBase.renyiQ_one ρ σ N hρ hσ hsupp
  have hlog := hQ.log (by rw [hbase]; exact one_ne_zero)
  rw [hbase,div_one] at hlog
  have ht := hlog.tendsto_slope
  have he : (slope (fun α => Real.log (renyiQ ρ σ N α)) 1)=renyiDelta ρ σ N := by
    funext α
    rw [slope_def_field,hbase,Real.log_one,sub_zero]
    unfold renyiDelta
    ring
  rw [he] at ht
  exact ht

lemma entropy_limit (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    Tendsto (fun α : ℝ => ((renyiDelta ρ σ N α / Real.log 2 : ℝ) : EReal)) (𝓝[≠] 1)
      (𝓝 (qRelEntropy ρ σ-qRelEntropy (N.apply ρ) (N.apply σ))) := by
  have ht := (delta_limit ρ σ N hρ hσ hsupp).div_const (Real.log 2)
  have he := EReal.tendsto_coe.mpr ht
  rw [entropy_difference ρ σ N hρ.1 hσ hsupp] at he
  exact he

end RenyiLimitSupport.RecoveryRenyiLimit

end

open Matrix WildeQIT WildeQIT.Recover Filter
open scoped MatrixOrder ComplexOrder ComplexConjugate Topology ENNReal Matrix.Norms.L2Operator Kronecker

set_option autoImplicit false



/-- **Lemma 12.4.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Lemma 12.4.1, (12.58), p. 374). For `ρ`, `σ`, `𝒩` as in Definition 12.1.1,
`(1/ln 2) lim_{α→1} Δ̃_α(ρ, σ, 𝒩) = D(ρ‖σ) − D(𝒩(ρ)‖𝒩(σ))`.

**Formalization Note** The limit is two-sided, `α → 1` with `α ≠ 1`; the factor `1/ln 2` is moved
inside the limit. The limit is taken in `EReal`, where the relative entropies live; the right side
is finite under the hypotheses. `Δ̃_α` uses the canonical isometric extension of the Kraus form. -/
theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    Tendsto (fun α : ℝ => ((renyiDelta ρ σ N α / Real.log 2 : ℝ) : EReal)) (𝓝[≠] 1)
      (𝓝 (qRelEntropy ρ σ - qRelEntropy (N.apply ρ) (N.apply σ))) := by
  exact RenyiLimitSupport.RecoveryRenyiLimit.entropy_limit ρ σ N hρ hσ hsupp