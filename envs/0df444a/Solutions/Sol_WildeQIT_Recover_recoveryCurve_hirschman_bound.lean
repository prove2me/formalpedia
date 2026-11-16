-- Prove2me | solution 1 for WildeQIT.Recover.recoveryCurve_hirschman_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-16T01:44:53.849908+00:00
-- url     : https://prove2.me/submissions/3ade0841-16b8-4a1f-ab33-2c0fe0695fef

import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_WildeQIT_Recover_renyiDelta
import Definitions.Def_WildeQIT_Recover_rotatedPetz
import Theorems.Thm_WildeQIT_Recover_hirschman_rectangular_two_one
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_hirschmanDensities
import Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open Matrix WildeQIT.Recover
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.PetzSpectral
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
end PetzPrelimitSupport.PetzSpectral

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover
open scoped ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.PetzChannel
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
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using PetzPrelimitSupport.PetzSpectral.pow_real_star A hA.isHermitian (1/2)
lemma petz_input (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    petzMap A N (N.apply A) = supportPow A (1/2)*adjointMap N (supportProj (N.apply A))*supportPow A (1/2) := by
  rw [petzMap,PetzPrelimitSupport.PetzSpectral.inverse_sandwich _ (map_positive N A hA)]
lemma petz_defect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    A-petzMap A N (N.apply A) = supportPow A (1/2)*adjointMap N (1-supportProj (N.apply A))*supportPow A (1/2) := by
  rw [adjoint_sub,adjoint_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,PetzPrelimitSupport.PetzSpectral.pow_half_square A hA,petz_input N A hA]
lemma petz_perfect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) : petzMap A N (N.apply A)=A := by
  have hd : (A-petzMap A N (N.apply A)).PosSemidef := by
    rw [petz_defect N A hA]
    have hh := (adjoint_positive N _ (PetzPrelimitSupport.PetzSpectral.support_complement_pos _ (map_positive N A hA))).mul_mul_conjTranspose_same (supportPow A (1/2))
    rwa [half_star A hA] at hh
  have ht : (A-petzMap A N (N.apply A)).trace=0 := by
    rw [trace_sub,petz_input N A hA]
    have hh : trace (supportPow A (1/2)*adjointMap N (supportProj (N.apply A))*supportPow A (1/2)) = A.trace := by
      rw [trace_mul_cycle,PetzPrelimitSupport.PetzSpectral.pow_half_square A hA,trace_dual,trace_mul_comm,PetzPrelimitSupport.PetzSpectral.support_mul _ (map_positive N A hA),trace_preserved]
    rw [hh,sub_self]
  exact (sub_eq_zero.mp (hd.trace_eq_zero_iff.mp ht)).symm
lemma rotated_perfect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) (t : ℝ) :
    rotatedPetz A N t (N.apply A)=A := by
  unfold rotatedPetz rotU
  rw [PetzPrelimitSupport.PetzSpectral.rotation_self _ (map_positive N A hA),petz_perfect N A hA,PetzPrelimitSupport.PetzSpectral.rotation_self A hA]
end PetzPrelimitSupport.PetzChannel

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover PetzPrelimitSupport.PetzSpectral PetzPrelimitSupport.PetzChannel
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.PetzCompletion
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def petzKraus (A : Matrix a a ℂ) (N : QChannel a b) (t : ℝ) (i : N.ι) : Matrix a b ℂ :=
  supportPow A (1/2 - (t : ℂ)*Complex.I) * (N.K i)ᴴ *
    supportPow (N.apply A) (-(1/2) + (t : ℂ)*Complex.I)

lemma kraus_apply (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) (Q : Matrix b b ℂ) :
    (∑ i, petzKraus A N t i * Q * (petzKraus A N t i)ᴴ) = rotatedPetz A N t Q := by
  have hB := (map_positive N A hA).isHermitian
  have h1 : conj (-(1/2 : ℂ) + (t : ℂ)*Complex.I) = -(1/2) - (t : ℂ)*Complex.I := by simp [map_ofNat,sub_eq_add_neg]
  have h2 : conj (1/2 - (t : ℂ)*Complex.I) = 1/2 + (t : ℂ)*Complex.I := by simp [map_ofNat]
  simp only [petzKraus,conjTranspose_mul,conjTranspose_conjTranspose,
    pow_star A hA.isHermitian,pow_star (N.apply A) hB,h1,h2]
  unfold rotatedPetz rotU petzMap adjointMap
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.ofReal_neg,neg_mul]
  have hL : supportPow A (1/2-(t : ℂ)*Complex.I) =
      supportPow A (-((t : ℂ)*Complex.I)) * supportPow A (1/2) := by
    rw [pow_add A hA.isHermitian]
    congr 1 <;> ring
  have hR : supportPow (N.apply A) (-(1/2)-(t : ℂ)*Complex.I) =
      supportPow (N.apply A) (-((t : ℂ)*Complex.I)) * supportPow (N.apply A) (-(1/2)) := by
    rw [pow_add (N.apply A) hB]
    congr 1 <;> ring
  rw [hL, ← pow_add (N.apply A) hB,hR, ← pow_add A hA.isHermitian]
  simp only [neg_neg,Matrix.mul_assoc]

end PetzPrelimitSupport.PetzCompletion

end

noncomputable section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryMatrixSVD
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

end PetzPrelimitSupport.RecoveryMatrixSVD

end

noncomputable section
namespace PetzPrelimitSupport.RecoveryDualFamily
variable {n : Type*} [Fintype n] [DecidableEq n]
def diagonalCLM : (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  (Matrix.diagonalLinearMap n ℂ ℂ).toContinuousLinearMap
end PetzPrelimitSupport.RecoveryDualFamily
end

noncomputable section
open Matrix Unitary WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryPowerCalculus
variable {n : Type} [Fintype n] [DecidableEq n]

lemma spectral_real_eq_cfc (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    spectralFun (fun x => (f x : ℂ)) A=cfc f A := by
  rw [PetzPrelimitSupport.PetzSpectral.sf_eq A hA,hA.cfc_eq,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  rfl

lemma supportPow_pos_eq_cfc (A : Matrix n n ℂ) (hA : A.PosSemidef) {r : ℝ} (hr : 0 < r) :
    supportPow A r=cfc (fun x : ℝ => x^r) A := by
  calc
    _ = spectralFun (fun x => ((x^r : ℝ) : ℂ)) A := by
      unfold supportPow
      apply PetzPrelimitSupport.PetzSpectral.sf_congr A hA.isHermitian
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
  rw [supportPow,PetzPrelimitSupport.PetzSpectral.sf_eq A hA]
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
  have hD : Differentiable ℂ (fun z : ℂ => PetzPrelimitSupport.RecoveryDualFamily.diagonalCLM (n := n)
      (fun i => if hA.eigenvalues i=0 then 0 else Complex.exp (z*(Real.log (hA.eigenvalues i) : ℂ)))) :=
    (PetzPrelimitSupport.RecoveryDualFamily.diagonalCLM (n := n)).differentiable.comp (differentiable_pi.mpr hcoeff)
  change Differentiable ℂ (fun z => supportPow A z)
  simp_rw [supportPow,PetzPrelimitSupport.PetzSpectral.sf_eq A hA]
  exact (hD.const_mul (hA.eigenvectorUnitary : Matrix n n ℂ)).mul_const (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

end PetzPrelimitSupport.RecoveryPowerCalculus

end

noncomputable section
open Matrix Set WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PetzPrelimitSupport.RecoveryMatrixCalculus
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
    _ = ‖supportPow A (z.re : ℂ)*supportPow A ((z.im : ℂ)*Complex.I)‖ := by rw [PetzPrelimitSupport.PetzSpectral.pow_add A hA,hz]
    _ ≤ ‖supportPow A (z.re : ℂ)‖*‖supportPow A ((z.im : ℂ)*Complex.I)‖ := norm_mul_le _ _
    _ ≤ ‖supportPow A (z.re : ℂ)‖*1 := mul_le_mul_of_nonneg_left
      (PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_imag_norm_le_one A hA z.im) (norm_nonneg _)
    _ = _ := mul_one _

lemma supportPow_strip_bounded (A : Matrix a a ℂ) (hA : A.IsHermitian) (u v : ℝ) :
    Bornology.IsBounded ((supportPow A) '' {z : ℂ | u ≤ z.re ∧ z.re ≤ v}) := by
  have hC : Continuous (fun r : ℝ => supportPow A (r : ℂ)) :=
    (PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_differentiable A hA).continuous.comp Complex.continuous_ofReal
  obtain ⟨B,hB⟩ := ((isCompact_Icc : IsCompact (Icc u v)).image hC).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨B,?_⟩
  rintro w ⟨z,hz,rfl⟩
  exact (supportPow_norm_le_real A hA z).trans (hB _ ⟨z.re,hz,rfl⟩)

end PetzPrelimitSupport.RecoveryMatrixCalculus

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryStinespring
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

end PetzPrelimitSupport.RecoveryStinespring

end

noncomputable section
open Matrix
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator
namespace PetzPrelimitSupport.RecoveryRectInterpolation
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def rSchatten (p : ℝ) (A : Matrix m n ℂ) : ℝ :=
  ((cfc (fun x : ℝ => x^(p/2)) (Aᴴ*A)).trace.re)^(1/p)

theorem rectangular_two_one (G : ℂ → Matrix m n ℂ)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog (rSchatten (2/(1+θ)) (G θ)) ≤ upperLogIntegral (fun t =>
      (alphaDensity θ t : EReal)*extendedLog ((rSchatten 2 (G ((t : ℂ)*Complex.I)))^(1-θ)) +
      (betaDensity θ t : EReal)*extendedLog ((rSchatten 1 (G (1+(t : ℂ)*Complex.I)))^θ)) := by
  exact WildeQIT.Recover.hirschman_rectangular_two_one G hbounded hholomorphic hcontinuous θ hθ0 hθ1
end PetzPrelimitSupport.RecoveryRectInterpolation
end

noncomputable section
open Matrix Set WildeQIT WildeQIT.Recover PetzPrelimitSupport.RecoveryMatrixCalculus
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryCurve
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def curve (ρ σ : Matrix a a ℂ) (N : QChannel a b) (z : ℂ) : Matrix (b×N.ι) a ℂ :=
  ((supportPow (N.apply ρ) (z/2)*supportPow (N.apply σ) (-(z/2))) ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*
    isometricExt N*supportPow σ (z/2)*supportPow ρ (1/2)

lemma differentiable (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : Differentiable ℂ (curve ρ σ N) := by
  have hd : Differentiable ℂ (fun z : ℂ => z/2) := by fun_prop
  have hP := (PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_differentiable (N.apply ρ)
    (PetzPrelimitSupport.PetzChannel.map_positive N ρ hρ).isHermitian).comp hd
  have hQ := (PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_differentiable (N.apply σ)
    (PetzPrelimitSupport.PetzChannel.map_positive N σ hσ).isHermitian).comp hd.neg
  have hS := (PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_differentiable σ hσ.isHermitian).comp hd
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
    apply (supportPow_strip_bounded (N.apply ρ) (PetzPrelimitSupport.PetzChannel.map_positive N ρ hρ).isHermitian 0 (1/2)).subset
    rintro w ⟨z,hz,rfl⟩
    refine ⟨z/2,?_,rfl⟩
    dsimp [S] at hz
    constructor <;> simp only [Complex.div_ofNat_re] <;> linarith [hz.1,hz.2]
  have hQ : Bornology.IsBounded ((fun z : ℂ => supportPow (N.apply σ) (-(z/2))) '' S) := by
    apply (supportPow_strip_bounded (N.apply σ) (PetzPrelimitSupport.PetzChannel.map_positive N σ hσ).isHermitian (-(1/2)) 0).subset
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

end PetzPrelimitSupport.RecoveryCurve

end

noncomputable section
open Matrix PetzPrelimitSupport.RecoveryRectInterpolation
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryRectHilbert
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
  [DecidableEq l] [DecidableEq m] [DecidableEq n]

lemma gram_trace (A : Matrix m n ℂ) : (Aᴴ*A).trace.re=∑ j, ∑ i, ‖A i j‖^2 := by
  change (∑ j, ∑ i, star (A i j)*A i j).re=∑ j, ∑ i, ‖A i j‖^2
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change (conj (A i j)*A i j).re=‖A i j‖^2
  rw [← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.normSq_eq_norm_sq]

lemma rSchatten_two (A : Matrix m n ℂ) : rSchatten 2 A=Real.sqrt ((Aᴴ*A).trace.re) := by
  unfold rSchatten
  norm_num only [show (2 : ℝ)/2=1 by norm_num,Real.rpow_one]
  change (cfc id (Aᴴ*A)).trace.re^(1/2 : ℝ)=Real.sqrt ((Aᴴ*A).trace.re)
  have hG : IsSelfAdjoint (Aᴴ*A) := (posSemidef_conjTranspose_mul_self A).isHermitian
  rw [cfc_id ℝ (Aᴴ*A)]
  exact (Real.sqrt_eq_rpow _).symm

lemma gram_trace_mul_le (A : Matrix l m ℂ) (B : Matrix m n ℂ) (hA : ‖A‖ ≤ 1) :
    ((A*B)ᴴ*(A*B)).trace.re ≤ (Bᴴ*B).trace.re := by
  rw [gram_trace,gram_trace]
  apply Finset.sum_le_sum
  intro j _
  let v : EuclideanSpace ℂ m := WithLp.toLp 2 (fun i => B i j)
  have hv : ‖WithLp.toLp 2 (A*ᵥv.ofLp)‖ ≤ ‖v‖ := by
    apply (Matrix.l2_opNorm_mulVec A v).trans
    exact (mul_le_mul_of_nonneg_right hA (norm_nonneg v)).trans_eq (one_mul _)
  have hv2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hv
  simpa only [EuclideanSpace.norm_sq_eq,v,Matrix.mul_apply,Matrix.mulVec,dotProduct] using hv2

lemma rSchatten_two_mul_le (A : Matrix l m ℂ) (B : Matrix m n ℂ) (hA : ‖A‖ ≤ 1) :
    rSchatten 2 (A*B) ≤ rSchatten 2 B := by
  rw [rSchatten_two,rSchatten_two]
  exact Real.sqrt_le_sqrt (gram_trace_mul_le A B hA)

end PetzPrelimitSupport.RecoveryRectHilbert

end

noncomputable section
open Matrix Unitary WildeQIT WildeQIT.Recover
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryTraceNorm
variable {n : Type} [Fintype n] [DecidableEq n]

lemma sqrt_eq_cfc_real (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    CFC.sqrt A=cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_rpow,CFC.rpow_eq_cfc_real hA.nonneg]
  congr 1
  funext x
  exact (Real.sqrt_eq_rpow x).symm

lemma cfc_trace_conj (A : Matrix n n ℂ) (hA : A.IsHermitian) (U : unitary (Matrix n n ℂ))
    (f : ℝ → ℝ) (hf : Continuous f) :
    (cfc f ((U : Matrix n n ℂ)*A*(U : Matrix n n ℂ)ᴴ)).trace=(cfc f A).trace := by
  let φ := (conjStarAlgAut ℂ (Matrix n n ℂ) U).toStarAlgHom
  have hφ : Continuous φ := φ.toLinearMap.toContinuousLinearMap.continuous
  have hφA : IsSelfAdjoint (φ A) := (show IsSelfAdjoint A from hA).map φ
  have he := φ.map_cfc f A hf.continuousOn hφ hA hφA
  change (cfc f (φ A)).trace=(cfc f A).trace
  rw [← he]
  change ((U : Matrix n n ℂ)*(cfc f A)*(U : Matrix n n ℂ)ᴴ).trace=(cfc f A).trace
  have hU : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  rw [trace_mul_cycle,hU,Matrix.one_mul]

lemma traceNorm_adjoint (A : Matrix n n ℂ) : traceNorm Aᴴ=traceNorm A := by
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := PetzPrelimitSupport.RecoveryMatrixSVD.gram_svd A
  let D : Matrix n n ℂ := diagonal (fun i => (s i : ℂ))
  have hD : Dᴴ=D := by simp [D,diagonal_conjTranspose]
  have hG : A*Aᴴ=(U : Matrix n n ℂ)*(D*D)*(U : Matrix n n ℂ)ᴴ := by
    rw [hA]
    change (((U : Matrix n n ℂ)*D*(V : Matrix n n ℂ))*
      ((U : Matrix n n ℂ)*D*(V : Matrix n n ℂ))ᴴ) = _
    simp only [conjTranspose_mul,hD,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V : Matrix n n ℂ) (V : Matrix n n ℂ)ᴴ,show (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 from Unitary.coe_mul_star_self V,Matrix.one_mul]
  have hG' : Aᴴ*A=(V : Matrix n n ℂ)ᴴ*(D*D)*(V : Matrix n n ℂ) := by
    rw [hA]
    change (((U : Matrix n n ℂ)*D*(V : Matrix n n ℂ))ᴴ*
      ((U : Matrix n n ℂ)*D*(V : Matrix n n ℂ))) = _
    simp only [conjTranspose_mul,hD,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),show (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 from Unitary.coe_star_mul_self U,Matrix.one_mul]
  have hDD : (D*D).IsHermitian := by
    change (D*D)ᴴ=D*D
    rw [conjTranspose_mul,hD]
  unfold traceNorm
  rw [conjTranspose_conjTranspose,sqrt_eq_cfc_real _ (show (A*Aᴴ).PosSemidef by simpa using posSemidef_conjTranspose_mul_self Aᴴ),
    sqrt_eq_cfc_real _ (posSemidef_conjTranspose_mul_self A),hG,hG']
  have hh := cfc_trace_conj (D*D) hDD (star V) Real.sqrt Real.continuous_sqrt
  simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_conjTranspose] at hh
  rw [cfc_trace_conj (D*D) hDD U Real.sqrt Real.continuous_sqrt,hh]

variable {m : Type} [Fintype m] [DecidableEq m] {a : Type} [Fintype a] [DecidableEq a]
lemma rSchatten_one_traceNorm (A : Matrix m a ℂ) : PetzPrelimitSupport.RecoveryRectInterpolation.rSchatten 1 A=traceNorm A := by
  unfold PetzPrelimitSupport.RecoveryRectInterpolation.rSchatten traceNorm
  norm_num only [one_div_one,Real.rpow_one]
  rw [sqrt_eq_cfc_real _ (posSemidef_conjTranspose_mul_self A)]
  congr 3
  funext x
  exact (Real.sqrt_eq_rpow x).symm

lemma half_eq_sqrt (A : Matrix a a ℂ) (hA : A.PosSemidef) : supportPow A (1/2)=CFC.sqrt A := by
  rw [← Complex.ofReal_one,← Complex.ofReal_ofNat 2,← Complex.ofReal_div,
    PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_pos_eq_cfc A hA (by norm_num),sqrt_eq_cfc_real A hA]
  congr 3
  funext x
  exact (Real.sqrt_eq_rpow x).symm

end PetzPrelimitSupport.RecoveryTraceNorm

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover PetzPrelimitSupport.RecoveryCurve PetzPrelimitSupport.PetzSpectral PetzPrelimitSupport.PetzChannel
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryCurveGram
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
    _ = _ := by rw [PetzPrelimitSupport.RecoveryStinespring.adjoint_dilation,hX]

lemma right_gram (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (t : ℝ) :
    (curve ρ σ N (1+(t : ℂ)*Complex.I))ᴴ*curve ρ σ N (1+(t : ℂ)*Complex.I) =
      supportPow ρ (1/2)*rotatedPetz σ N (t/2) (N.apply ρ)*supportPow ρ (1/2) := by
  rw [curve_gram ρ σ N hρ hσ]
  have hc : conj ((1+(t : ℂ)*Complex.I)/2) = 1/2-(t : ℂ)*Complex.I/2 := by
    simp [map_ofNat]; ring
  have he : conj ((1+(t : ℂ)*Complex.I)/2)+(1+(t : ℂ)*Complex.I)/2=1 := by rw [hc]; ring
  rw [he,pow_one _ (map_positive N ρ hρ),hc]
  have hR := PetzPrelimitSupport.PetzCompletion.kraus_apply σ hσ N (t/2) (N.apply ρ)
  rw [← hR]
  simp only [PetzPrelimitSupport.PetzCompletion.petzKraus,conjTranspose_mul,conjTranspose_conjTranspose,
    pow_star σ hσ.isHermitian,pow_star (N.apply σ) (map_positive N σ hσ).isHermitian,
    Finset.mul_sum,Finset.sum_mul]
  have hL : 1/2-(t : ℂ)*Complex.I/2=1/2-((t/2 : ℝ) : ℂ)*Complex.I := by push_cast; ring
  have hRi : -((1+(t : ℂ)*Complex.I)/2)=conj (-(1/2 : ℂ)+((t/2 : ℝ) : ℂ)*Complex.I) := by
    simp [map_ofNat]; ring
  have hLp : (1+(t : ℂ)*Complex.I)/2=conj ((1/2 : ℂ)-((t/2 : ℝ) : ℂ)*Complex.I) := by
    simp [map_ofNat]; ring
  have hLi : -(1/2-(t : ℂ)*Complex.I/2)=-(1/2 : ℂ)+((t/2 : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [hL,hRi,hLp]
  unfold adjointMap
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show -(1/2-((t/2 : ℝ) : ℂ)*Complex.I)=-(1/2 : ℂ)+((t/2 : ℝ) : ℂ)*Complex.I by ring]
  simp only [Matrix.mul_assoc]

end PetzPrelimitSupport.RecoveryCurveGram

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover PetzPrelimitSupport.RecoveryCurve PetzPrelimitSupport.RecoveryMatrixCalculus PetzPrelimitSupport.RecoveryRectInterpolation
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryCurveLeft
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma isometricExt_norm_le_one (N : QChannel a b) : ‖isometricExt N‖ ≤ 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (isometricExt N)
  rw [PetzPrelimitSupport.RecoveryStinespring.kraus_isometry] at hh
  have h1 : ‖(1 : Matrix a a ℂ)‖ ≤ 1 := by
    by_cases h : Nonempty a
    · letI := h; simp
    · haveI : IsEmpty a := not_nonempty_iff.mp h
      have hz : (1 : Matrix a a ℂ)=0 := Subsingleton.elim _ _
      simp [hz]
  nlinarith [norm_nonneg (isometricExt N)]

lemma left_norm (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (t : ℝ) :
    rSchatten 2 (curve ρ σ N ((t : ℂ)*Complex.I)) ≤ 1 := by
  let u : ℂ := (t : ℂ)*Complex.I/2
  have hu : u=((t/2 : ℝ) : ℂ)*Complex.I := by dsimp [u]; push_cast; ring
  have hnu : -u=((-t/2 : ℝ) : ℂ)*Complex.I := by rw [hu]; push_cast; ring
  have hP : ‖supportPow (N.apply ρ) u‖ ≤ 1 := by
    rw [hu]
    exact PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_imag_norm_le_one _ (PetzPrelimitSupport.PetzChannel.map_positive N ρ hρ.1).isHermitian _
  have hQ : ‖supportPow (N.apply σ) (-u)‖ ≤ 1 := by
    rw [hnu]
    exact PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_imag_norm_le_one _ (PetzPrelimitSupport.PetzChannel.map_positive N σ hσ).isHermitian _
  have hS : ‖supportPow σ u‖ ≤ 1 := by
    rw [hu]
    exact PetzPrelimitSupport.RecoveryPowerCalculus.supportPow_imag_norm_le_one _ hσ.isHermitian _
  let T := ((supportPow (N.apply ρ) u*supportPow (N.apply σ) (-u)) ⊗ₖ (1 : Matrix N.ι N.ι ℂ))
  have hT : ‖T‖ ≤ 1 := by
    apply (tensorId_norm_le (n := N.ι) _).trans
    exact (norm_mul_le _ _).trans ((mul_le_mul hP hQ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hTU : ‖T*isometricExt N‖ ≤ 1 :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hT (isometricExt_norm_le_one N) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hA : ‖T*isometricExt N*supportPow σ u‖ ≤ 1 :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hTU hS (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  change rSchatten 2 ((T*isometricExt N*supportPow σ u)*supportPow ρ (1/2)) ≤ 1
  apply (PetzPrelimitSupport.RecoveryRectHilbert.rSchatten_two_mul_le _ _ hA).trans
  rw [PetzPrelimitSupport.RecoveryRectHilbert.rSchatten_two,PetzPrelimitSupport.PetzChannel.half_star ρ hρ.1,
    PetzPrelimitSupport.PetzSpectral.pow_half_square ρ hρ.1,hρ.2]
  norm_num

end PetzPrelimitSupport.RecoveryCurveLeft

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover PetzPrelimitSupport.RecoveryCurve PetzPrelimitSupport.RecoveryTraceNorm PetzPrelimitSupport.RecoveryRectInterpolation
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryCurveRight
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma rotated_positive (σ : Matrix a a ℂ) (N : QChannel a b) (hσ : σ.PosSemidef)
    (Q : Matrix b b ℂ) (hQ : Q.PosSemidef) (t : ℝ) : (rotatedPetz σ N t Q).PosSemidef := by
  rw [← PetzPrelimitSupport.PetzCompletion.kraus_apply σ hσ N t Q]
  exact posSemidef_sum _ (fun i _ => hQ.mul_mul_conjTranspose_same _)

lemma sqrt_star (A : Matrix a a ℂ) : (CFC.sqrt A)ᴴ=CFC.sqrt A := by
  change star (CFC.sqrt A)=CFC.sqrt A
  exact (CFC.sqrt_nonneg A).star_eq

lemma right_norm (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (t : ℝ) :
    rSchatten 1 (curve ρ σ N (1+(t : ℂ)*Complex.I)) =
      rootFidelity ρ (rotatedPetz σ N (t/2) (N.apply ρ)) := by
  let R := rotatedPetz σ N (t/2) (N.apply ρ)
  have hR : R.PosSemidef := rotated_positive σ N hσ _ (PetzPrelimitSupport.PetzChannel.map_positive N ρ hρ) _
  rw [rSchatten_one_traceNorm]
  change traceNorm (curve ρ σ N (1+(t : ℂ)*Complex.I))=traceNorm (CFC.sqrt ρ*CFC.sqrt R)
  rw [← traceNorm_adjoint (CFC.sqrt ρ*CFC.sqrt R)]
  simp only [conjTranspose_mul,sqrt_star]
  unfold traceNorm
  have hG : (curve ρ σ N (1+(t : ℂ)*Complex.I))ᴴ*curve ρ σ N (1+(t : ℂ)*Complex.I) =
      (CFC.sqrt R*CFC.sqrt ρ)ᴴ*(CFC.sqrt R*CFC.sqrt ρ) := by
    rw [PetzPrelimitSupport.RecoveryCurveGram.right_gram ρ σ N hρ hσ t,half_eq_sqrt ρ hρ]
    simp only [conjTranspose_mul,sqrt_star,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt R) (CFC.sqrt R),CFC.sqrt_mul_sqrt_self R hR.nonneg]
  rw [hG]

end PetzPrelimitSupport.RecoveryCurveRight

end

noncomputable section
open Matrix Unitary Set Filter MeasureTheory
open QAlgorithms.Papers.Independent.Information100.P50
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped Topology ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryInterpolation
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma extendedLog_mono {a b : ℝ} (h : a ≤ b) : extendedLog a ≤ extendedLog b := by
  simpa only [ENNReal.log_ofReal,extendedLog] using ENNReal.log_monotone (ENNReal.ofReal_le_ofReal h)

lemma upperLogIntegral_mono {u v : ℝ → EReal} (h : ∀ t, u t ≤ v t) :
    upperLogIntegral u ≤ upperLogIntegral v := by
  apply EReal.sub_le_sub
  · exact_mod_cast lintegral_mono (fun t => EReal.toENNReal_le_toENNReal (h t))
  · exact_mod_cast (lintegral_mono (μ := volume)
      (fun t => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (h t))))

end PetzPrelimitSupport.RecoveryInterpolation

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover PetzPrelimitSupport.RecoveryCurve PetzPrelimitSupport.RecoveryRectInterpolation
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzPrelimitSupport.RecoveryPrelimit
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma curve_bound (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog (rSchatten (2/(1+θ)) (curve ρ σ N θ)) ≤ upperLogIntegral (fun t =>
      (betaDensity θ t : EReal)*extendedLog ((rootFidelity ρ (rotatedPetz σ N (t/2) (N.apply ρ)))^θ)) := by
  have hh := rectangular_two_one (curve ρ σ N) (bounded ρ σ N hρ.1 hσ)
    (differentiable ρ σ N hρ.1 hσ).differentiableOn
    (differentiable ρ σ N hρ.1 hσ).continuous.continuousOn θ hθ0 hθ1
  apply hh.trans
  apply PetzPrelimitSupport.RecoveryInterpolation.upperLogIntegral_mono
  intro t
  rw [PetzPrelimitSupport.RecoveryCurveRight.right_norm ρ σ N hρ.1 hσ t]
  have hleft : extendedLog ((rSchatten 2 (curve ρ σ N ((t : ℂ)*Complex.I)))^(1-θ)) ≤ 0 := by
    have hn : 0 ≤ rSchatten 2 (curve ρ σ N ((t : ℂ)*Complex.I)) := by
      rw [PetzPrelimitSupport.RecoveryRectHilbert.rSchatten_two]
      exact Real.sqrt_nonneg _
    have hle := Real.rpow_le_one hn (PetzPrelimitSupport.RecoveryCurveLeft.left_norm ρ σ N hρ hσ t) (by linarith : 0 ≤ 1-θ)
    have hl := PetzPrelimitSupport.RecoveryInterpolation.extendedLog_mono hle
    have hlog : extendedLog 1=0 := by norm_num [extendedLog]
    rwa [hlog] at hl
  have hα := ((hirschmanDensities.1 θ hθ0 hθ1).1 t).1
  have ha : (0 : EReal) ≤ (alphaDensity θ t : EReal) := by exact_mod_cast hα
  have hp : (alphaDensity θ t : EReal)*extendedLog ((rSchatten 2 (curve ρ σ N ((t : ℂ)*Complex.I)))^(1-θ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha hleft
  exact add_le_of_nonpos_left hp

end PetzPrelimitSupport.RecoveryPrelimit

end

open Matrix WildeQIT WildeQIT.Recover
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker

set_option autoImplicit false


theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    let G : ℂ → Matrix (b×N.ι) a ℂ := fun z =>
      letI : DecidableEq N.ι := Classical.decEq _
      ((supportPow (N.apply ρ) (z/2)*supportPow (N.apply σ) (-(z/2))) ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*
        isometricExt N*supportPow σ (z/2)*supportPow ρ (1/2)
    let p : ℝ := 2/(1+θ)
    extendedLog (((cfc (fun x : ℝ => x^(p/2)) ((G θ)ᴴ*G θ)).trace.re)^(1/p)) ≤
      upperLogIntegral (fun t => (betaDensity θ t : EReal)*
        extendedLog ((rootFidelity ρ (rotatedPetz σ N (t/2) (N.apply ρ)))^θ)) := by
  exact PetzPrelimitSupport.RecoveryPrelimit.curve_bound ρ σ N hρ hσ θ hθ0 hθ1