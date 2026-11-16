-- Prove2me | solution 1 for WildeQIT.Recover.theorem_12_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-16T02:38:30.757575+00:00
-- url     : https://prove2.me/submissions/57823839-e973-4e1a-bc9a-328c9a1c5996

import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_WildeQIT_Recover_spectralFun
import Definitions.Def_WildeQIT_Recover_renyiDelta
import Definitions.Def_WildeQIT_Recover_rotatedPetz
import Definitions.Def_WildeQIT_Recover_qRelEntropy
import Definitions.Def_WildeQIT_Recover_negLog2
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Theorems.Thm_WildeQIT_Recover_recoveryCurve_hirschman_bound
import Theorems.Thm_WildeQIT_Recover_lemma_12_4_1
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_hirschmanDensities
import Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.EReal.Inv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open Matrix WildeQIT.Recover
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.PetzSpectral
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
end QuantRecoverySupport.PetzSpectral

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover
open scoped ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.PetzChannel
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
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using QuantRecoverySupport.PetzSpectral.pow_real_star A hA.isHermitian (1/2)
lemma petz_input (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    petzMap A N (N.apply A) = supportPow A (1/2)*adjointMap N (supportProj (N.apply A))*supportPow A (1/2) := by
  rw [petzMap,QuantRecoverySupport.PetzSpectral.inverse_sandwich _ (map_positive N A hA)]
lemma petz_defect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    A-petzMap A N (N.apply A) = supportPow A (1/2)*adjointMap N (1-supportProj (N.apply A))*supportPow A (1/2) := by
  rw [adjoint_sub,adjoint_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,QuantRecoverySupport.PetzSpectral.pow_half_square A hA,petz_input N A hA]
lemma petz_perfect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) : petzMap A N (N.apply A)=A := by
  have hd : (A-petzMap A N (N.apply A)).PosSemidef := by
    rw [petz_defect N A hA]
    have hh := (adjoint_positive N _ (QuantRecoverySupport.PetzSpectral.support_complement_pos _ (map_positive N A hA))).mul_mul_conjTranspose_same (supportPow A (1/2))
    rwa [half_star A hA] at hh
  have ht : (A-petzMap A N (N.apply A)).trace=0 := by
    rw [trace_sub,petz_input N A hA]
    have hh : trace (supportPow A (1/2)*adjointMap N (supportProj (N.apply A))*supportPow A (1/2)) = A.trace := by
      rw [trace_mul_cycle,QuantRecoverySupport.PetzSpectral.pow_half_square A hA,trace_dual,trace_mul_comm,QuantRecoverySupport.PetzSpectral.support_mul _ (map_positive N A hA),trace_preserved]
    rw [hh,sub_self]
  exact (sub_eq_zero.mp (hd.trace_eq_zero_iff.mp ht)).symm
lemma rotated_perfect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) (t : ℝ) :
    rotatedPetz A N t (N.apply A)=A := by
  unfold rotatedPetz rotU
  rw [QuantRecoverySupport.PetzSpectral.rotation_self _ (map_positive N A hA),petz_perfect N A hA,QuantRecoverySupport.PetzSpectral.rotation_self A hA]
end QuantRecoverySupport.PetzChannel

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.PetzSpectral QuantRecoverySupport.PetzChannel
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.PetzCompletion
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

lemma kraus_complete_support (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) : ∑ i, (petzKraus A N t i)ᴴ * petzKraus A N t i = supportProj (N.apply A) := by
  let L := supportPow A (1/2 - (t : ℂ)*Complex.I)
  let R := supportPow (N.apply A) (-(1/2) + (t : ℂ)*Complex.I)
  have hl : Lᴴ * L = A := by
    dsimp [L]
    rw [pow_star A hA.isHermitian,pow_add A hA.isHermitian]
    convert pow_one A hA using 1 <;> simp [map_ofNat] <;> ring
  calc
    _ = Rᴴ * (N.apply A) * R := by
      simp only [petzKraus,QChannel.apply,Finset.mul_sum,Finset.sum_mul,conjTranspose_mul,
        conjTranspose_conjTranspose]
      apply Finset.sum_congr rfl
      intro i _
      change (Rᴴ * (N.K i * Lᴴ)) * (L * (N.K i)ᴴ * R) = Rᴴ * (N.K i * A * (N.K i)ᴴ) * R
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Lᴴ L,hl]
    _ = supportProj (N.apply A) := by
      dsimp [R]
      have hB := map_positive N A hA
      rw [pow_star _ hB.isHermitian]
      calc
        _ = supportPow (N.apply A) (conj (-(1/2 : ℂ)+(t : ℂ)*Complex.I)) * supportPow (N.apply A) 1 *
          supportPow (N.apply A) (-(1/2)+(t : ℂ)*Complex.I) := by rw [pow_one _ hB]
        _ = _ := by
          rw [pow_add _ hB.isHermitian,pow_add _ hB.isHermitian]
          convert QuantRecoverySupport.PetzSpectral.pow_zero (N.apply A) using 1 <;> simp [map_ofNat] <;> ring

lemma rotated_trace (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) (Q : Matrix b b ℂ) :
    trace (rotatedPetz A N t Q)=trace (supportProj (N.apply A)*Q) := by
  rw [← kraus_apply A hA N t Q,trace_sum,← kraus_complete_support A hA N t,
    Finset.sum_mul,trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact trace_mul_cycle _ _ _

end QuantRecoverySupport.PetzCompletion

end

noncomputable section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryMatrixSVD
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

end QuantRecoverySupport.RecoveryMatrixSVD

end

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoverySchatten
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
  obtain ⟨U,V,s,hs,_,hcalc⟩ := QuantRecoverySupport.RecoveryMatrixSVD.gram_svd A
  rw [schatten_one_svd A V s hs hcalc]
  exact Finset.sum_nonneg fun i _ => hs i

end QuantRecoverySupport.RecoverySchatten

end

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryTraceBounds
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
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := QuantRecoverySupport.RecoveryMatrixSVD.gram_svd A
  rw [QuantRecoverySupport.RecoverySchatten.schatten_one_svd A V s hs hcalc]
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
  rw [QuantRecoverySupport.RecoverySchatten.schatten_two,QuantRecoverySupport.RecoverySchatten.schatten_two,gram_trace,gram_trace]
  have ht : (X*A).trace = ∑ p : n×n, X p.1 p.2*A p.2 p.1 := by
    simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type]
  rw [ht]
  calc
    _ ≤ ∑ p : n×n, ‖X p.1 p.2*A p.2 p.1‖ := norm_sum_le _ _
    _ = ∑ p : n×n, ‖X p.1 p.2‖*‖A p.2 p.1‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ p : n×n, ‖X p.1 p.2‖^2)*Real.sqrt (∑ p : n×n, ‖A p.2 p.1‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp only [Fintype.sum_prod_type]; rw [Finset.sum_comm (f := fun i j => ‖A j i‖^2)]

end QuantRecoverySupport.RecoveryTraceBounds

end

noncomputable section
namespace QuantRecoverySupport.RecoveryDualFamily
variable {n : Type*} [Fintype n] [DecidableEq n]
def diagonalCLM : (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  (Matrix.diagonalLinearMap n ℂ ℂ).toContinuousLinearMap
end QuantRecoverySupport.RecoveryDualFamily
end

noncomputable section
open Matrix Unitary WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryPowerCalculus
variable {n : Type} [Fintype n] [DecidableEq n]

lemma spectral_real_eq_cfc (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    spectralFun (fun x => (f x : ℂ)) A=cfc f A := by
  rw [QuantRecoverySupport.PetzSpectral.sf_eq A hA,hA.cfc_eq,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  rfl

lemma supportPow_pos_eq_cfc (A : Matrix n n ℂ) (hA : A.PosSemidef) {r : ℝ} (hr : 0 < r) :
    supportPow A r=cfc (fun x : ℝ => x^r) A := by
  calc
    _ = spectralFun (fun x => ((x^r : ℝ) : ℂ)) A := by
      unfold supportPow
      apply QuantRecoverySupport.PetzSpectral.sf_congr A hA.isHermitian
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
  rw [supportPow,QuantRecoverySupport.PetzSpectral.sf_eq A hA]
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
  have hD : Differentiable ℂ (fun z : ℂ => QuantRecoverySupport.RecoveryDualFamily.diagonalCLM (n := n)
      (fun i => if hA.eigenvalues i=0 then 0 else Complex.exp (z*(Real.log (hA.eigenvalues i) : ℂ)))) :=
    (QuantRecoverySupport.RecoveryDualFamily.diagonalCLM (n := n)).differentiable.comp (differentiable_pi.mpr hcoeff)
  change Differentiable ℂ (fun z => supportPow A z)
  simp_rw [supportPow,QuantRecoverySupport.PetzSpectral.sf_eq A hA]
  exact (hD.const_mul (hA.eigenvectorUnitary : Matrix n n ℂ)).mul_const (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

end QuantRecoverySupport.RecoveryPowerCalculus

end

noncomputable section
open Matrix Set WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QuantRecoverySupport.RecoveryMatrixCalculus
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
    _ = ‖supportPow A (z.re : ℂ)*supportPow A ((z.im : ℂ)*Complex.I)‖ := by rw [QuantRecoverySupport.PetzSpectral.pow_add A hA,hz]
    _ ≤ ‖supportPow A (z.re : ℂ)‖*‖supportPow A ((z.im : ℂ)*Complex.I)‖ := norm_mul_le _ _
    _ ≤ ‖supportPow A (z.re : ℂ)‖*1 := mul_le_mul_of_nonneg_left
      (QuantRecoverySupport.RecoveryPowerCalculus.supportPow_imag_norm_le_one A hA z.im) (norm_nonneg _)
    _ = _ := mul_one _

lemma supportPow_strip_bounded (A : Matrix a a ℂ) (hA : A.IsHermitian) (u v : ℝ) :
    Bornology.IsBounded ((supportPow A) '' {z : ℂ | u ≤ z.re ∧ z.re ≤ v}) := by
  have hC : Continuous (fun r : ℝ => supportPow A (r : ℂ)) :=
    (QuantRecoverySupport.RecoveryPowerCalculus.supportPow_differentiable A hA).continuous.comp Complex.continuous_ofReal
  obtain ⟨B,hB⟩ := ((isCompact_Icc : IsCompact (Icc u v)).image hC).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨B,?_⟩
  rintro w ⟨z,hz,rfl⟩
  exact (supportPow_norm_le_real A hA z).trans (hB _ ⟨z.re,hz,rfl⟩)

end QuantRecoverySupport.RecoveryMatrixCalculus

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryStinespring
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

end QuantRecoverySupport.RecoveryStinespring

end

noncomputable section
open Matrix Set Filter MeasureTheory
open QAlgorithms.Papers.Independent.Information100.P50
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped Topology ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryRectInterpolation
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def rSchatten (p : ℝ) (A : Matrix m n ℂ) : ℝ :=
  ((cfc (fun x : ℝ => x^(p/2)) (Aᴴ*A)).trace.re)^(1/p)

end QuantRecoverySupport.RecoveryRectInterpolation

end

noncomputable section
open Matrix Set WildeQIT WildeQIT.Recover QuantRecoverySupport.RecoveryMatrixCalculus
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryCurve
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def curve (ρ σ : Matrix a a ℂ) (N : QChannel a b) (z : ℂ) : Matrix (b×N.ι) a ℂ :=
  ((supportPow (N.apply ρ) (z/2)*supportPow (N.apply σ) (-(z/2))) ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*
    isometricExt N*supportPow σ (z/2)*supportPow ρ (1/2)

lemma differentiable (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : Differentiable ℂ (curve ρ σ N) := by
  have hd : Differentiable ℂ (fun z : ℂ => z/2) := by fun_prop
  have hP := (QuantRecoverySupport.RecoveryPowerCalculus.supportPow_differentiable (N.apply ρ)
    (QuantRecoverySupport.PetzChannel.map_positive N ρ hρ).isHermitian).comp hd
  have hQ := (QuantRecoverySupport.RecoveryPowerCalculus.supportPow_differentiable (N.apply σ)
    (QuantRecoverySupport.PetzChannel.map_positive N σ hσ).isHermitian).comp hd.neg
  have hS := (QuantRecoverySupport.RecoveryPowerCalculus.supportPow_differentiable σ hσ.isHermitian).comp hd
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
    apply (supportPow_strip_bounded (N.apply ρ) (QuantRecoverySupport.PetzChannel.map_positive N ρ hρ).isHermitian 0 (1/2)).subset
    rintro w ⟨z,hz,rfl⟩
    refine ⟨z/2,?_,rfl⟩
    dsimp [S] at hz
    constructor <;> simp only [Complex.div_ofNat_re] <;> linarith [hz.1,hz.2]
  have hQ : Bornology.IsBounded ((fun z : ℂ => supportPow (N.apply σ) (-(z/2))) '' S) := by
    apply (supportPow_strip_bounded (N.apply σ) (QuantRecoverySupport.PetzChannel.map_positive N σ hσ).isHermitian (-(1/2)) 0).subset
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

end QuantRecoverySupport.RecoveryCurve

end

noncomputable section
open Matrix Unitary WildeQIT WildeQIT.Recover
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryTraceNorm
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
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := QuantRecoverySupport.RecoveryMatrixSVD.gram_svd A
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
lemma rSchatten_one_traceNorm (A : Matrix m a ℂ) : QuantRecoverySupport.RecoveryRectInterpolation.rSchatten 1 A=traceNorm A := by
  unfold QuantRecoverySupport.RecoveryRectInterpolation.rSchatten traceNorm
  norm_num only [one_div_one,Real.rpow_one]
  rw [sqrt_eq_cfc_real _ (posSemidef_conjTranspose_mul_self A)]
  congr 3
  funext x
  exact (Real.sqrt_eq_rpow x).symm

lemma half_eq_sqrt (A : Matrix a a ℂ) (hA : A.PosSemidef) : supportPow A (1/2)=CFC.sqrt A := by
  rw [← Complex.ofReal_one,← Complex.ofReal_ofNat 2,← Complex.ofReal_div,
    QuantRecoverySupport.RecoveryPowerCalculus.supportPow_pos_eq_cfc A hA (by norm_num),sqrt_eq_cfc_real A hA]
  congr 3
  funext x
  exact (Real.sqrt_eq_rpow x).symm

end QuantRecoverySupport.RecoveryTraceNorm

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.RecoveryCurve QuantRecoverySupport.PetzSpectral QuantRecoverySupport.PetzChannel
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryCurveGram
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
    _ = _ := by rw [QuantRecoverySupport.RecoveryStinespring.adjoint_dilation,hX]

end QuantRecoverySupport.RecoveryCurveGram

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.RecoveryCurve QuantRecoverySupport.RecoveryTraceNorm QuantRecoverySupport.RecoveryRectInterpolation
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryCurveRight
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma rotated_positive (σ : Matrix a a ℂ) (N : QChannel a b) (hσ : σ.PosSemidef)
    (Q : Matrix b b ℂ) (hQ : Q.PosSemidef) (t : ℝ) : (rotatedPetz σ N t Q).PosSemidef := by
  rw [← QuantRecoverySupport.PetzCompletion.kraus_apply σ hσ N t Q]
  exact posSemidef_sum _ (fun i _ => hQ.mul_mul_conjTranspose_same _)

lemma sqrt_star (A : Matrix a a ℂ) : (CFC.sqrt A)ᴴ=CFC.sqrt A := by
  change star (CFC.sqrt A)=CFC.sqrt A
  exact (CFC.sqrt_nonneg A).star_eq

end QuantRecoverySupport.RecoveryCurveRight

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.PetzSpectral QuantRecoverySupport.PetzChannel
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoverySupport
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

end QuantRecoverySupport.RecoverySupport

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.PetzSpectral QuantRecoverySupport.PetzChannel QuantRecoverySupport.RecoverySupport QuantRecoverySupport.RecoveryCurve
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryRenyiBase
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma gram_zero (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    (curve ρ σ N 0)ᴴ*curve ρ σ N 0=ρ := by
  have hP := map_positive N ρ hρ
  have hQ := map_positive N σ hσ
  have hPQ := map_supp ρ σ hρ hσ hsupp N
  have hqp : supportProj (N.apply σ)*supportProj (N.apply ρ)=supportProj (N.apply ρ) := by
    simpa only [QuantRecoverySupport.PetzSpectral.pow_zero] using support_mul_pow _ _ hP hQ hPQ 0
  have hpq : supportProj (N.apply ρ)*supportProj (N.apply σ)=supportProj (N.apply ρ) := by
    simpa only [QuantRecoverySupport.PetzSpectral.pow_zero] using pow_mul_support _ _ hP hQ hPQ 0
  rw [QuantRecoverySupport.RecoveryCurveGram.curve_gram ρ σ N hρ hσ 0]
  simp only [zero_div,map_zero,neg_zero,zero_add,QuantRecoverySupport.PetzSpectral.pow_zero,hqp,hpq]
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

end QuantRecoverySupport.RecoveryRenyiBase

end

noncomputable section
open Matrix WildeQIT.Recover
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryPowerDerivative
variable {n : Type} [Fintype n] [DecidableEq n]

def logNat (A : Matrix n n ℂ) : Matrix n n ℂ := spectralFun (fun x => (Real.log x : ℂ)) A

end QuantRecoverySupport.RecoveryPowerDerivative

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.PetzSpectral QuantRecoverySupport.PetzChannel QuantRecoverySupport.RecoverySupport QuantRecoverySupport.RecoveryPowerDerivative
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryEntropyUnits
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
  rw [← QuantRecoverySupport.RecoveryPowerCalculus.spectral_real_eq_cfc A hA]
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

end QuantRecoverySupport.RecoveryEntropyUnits

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.RecoveryCurve
open scoped MatrixOrder ComplexOrder ComplexConjugate Topology Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace QuantRecoverySupport.RecoveryRenyiDerivative
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

end QuantRecoverySupport.RecoveryRenyiDerivative

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.RecoveryRenyiDerivative Filter
open scoped MatrixOrder ComplexOrder ComplexConjugate Topology Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryRenyiPositivity
variable {n : Type} [Fintype n] [DecidableEq n]

lemma trace_power_pos (A : Matrix n n ℂ) (hA : A.PosSemidef) (hne : A ≠ 0) {r : ℝ} (hr : 0 < r) :
    (cfc (fun x : ℝ => x^r) A).trace.re > 0 := by
  rw [← CFC.rpow_eq_cfc_real hA.nonneg]
  let B := A^r
  have hB : B.PosSemidef := (CFC.rpow_nonneg : 0 ≤ A^r).posSemidef
  have htr := Complex.nonneg_iff.mp hB.trace_nonneg
  apply lt_of_le_of_ne htr.1
  intro hz
  have htz : B.trace=0 := by apply Complex.ext; exact hz.symm; simpa using htr.2.symm
  have hBz := hB.trace_eq_zero_iff.mp htz
  have hn := CFC.norm_rpow A hr hA.nonneg
  have hab : ‖A‖^r=0 := by rw [← hn]; change ‖B‖=0; rw [hBz,norm_zero]
  exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr hne) r).ne' hab

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma eventually_renyiQ_pos (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    ∀ᶠ α : ℝ in 𝓝 1, 0 < renyiQ ρ σ N α := by
  have hρne : ρ ≠ 0 := by intro h; have hh := hρ.2; rw [h,trace_zero] at hh; exact zero_ne_one hh
  have hGne : gram ρ σ N 1 ≠ 0 := by
    change (renyiOp ρ σ N 1)ᴴ*renyiOp ρ σ N 1 ≠ 0
    rwa [QuantRecoverySupport.RecoveryRenyiBase.renyiOp_one_gram ρ σ N hρ.1 hσ hsupp]
  have hG : ∀ᶠ α : ℝ in 𝓝 1, gram ρ σ N α ≠ 0 :=
    (gram_continuousAt ρ σ N hρ.1 hσ).tendsto.eventually
      ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hGne)
  filter_upwards [hG,eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with α hne hα
  unfold renyiQ
  rw [QuantRecoverySupport.RecoveryPowerCalculus.supportPow_pos_eq_cfc _ (posSemidef_conjTranspose_mul_self _) hα]
  exact trace_power_pos _ (posSemidef_conjTranspose_mul_self _) hne hα

end QuantRecoverySupport.RecoveryRenyiPositivity

end

noncomputable section
open Matrix Unitary WildeQIT
open QuantRecoverySupport.RecoveryTraceNorm
open QAlgorithms.Papers.Independent.Information100.P50
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryFidelityBound
variable {n : Type} [Fintype n] [DecidableEq n]

lemma schatten_one_traceNorm (A : Matrix n n ℂ) : schattenNorm 1 A=traceNorm A := by
  rw [schattenNorm,if_neg (by simp),ENNReal.toReal_one]
  change QuantRecoverySupport.RecoveryRectInterpolation.rSchatten 1 A=traceNorm A
  exact rSchatten_one_traceNorm A

lemma schatten_two_unitary_mul (W : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    schattenNorm 2 ((W : Matrix n n ℂ)*X)=schattenNorm 2 X := by
  have hW : (W : Matrix n n ℂ)ᴴ*(W : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self W
  rw [QuantRecoverySupport.RecoverySchatten.schatten_two,QuantRecoverySupport.RecoverySchatten.schatten_two]
  congr 2
  rw [conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (W : Matrix n n ℂ)ᴴ (W : Matrix n n ℂ),hW,Matrix.one_mul]

lemma traceNorm_mul_le_two (X Y : Matrix n n ℂ) :
    traceNorm (X*Y) ≤ schattenNorm 2 X*schattenNorm 2 Y := by
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := QuantRecoverySupport.RecoveryMatrixSVD.gram_svd (X*Y)
  let W : unitary (Matrix n n ℂ) := star V*star U
  have hD : (W : Matrix n n ℂ)*(X*Y)=
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ) := by
    rw [hA]
    change (((V : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)ᴴ)*
      ((U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ))) = _
    have hU : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),hU,Matrix.one_mul]
  have htr : ((W : Matrix n n ℂ)*(X*Y)).trace=(∑ i, s i : ℝ) := by
    rw [hD,trace_mul_cycle]
    have hV : (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 := Unitary.coe_mul_star_self V
    rw [hV,Matrix.one_mul,trace_diagonal]
    simp
  have hn : ‖((W : Matrix n n ℂ)*X*Y).trace‖=traceNorm (X*Y) := by
    rw [Matrix.mul_assoc,htr,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => hs i)),← schatten_one_traceNorm,
      QuantRecoverySupport.RecoverySchatten.schatten_one_svd (X*Y) V s hs hcalc]
  have hh := QuantRecoverySupport.RecoveryTraceBounds.trace_hilbert_schmidt_bound ((W : Matrix n n ℂ)*X) Y
  rwa [hn,schatten_two_unitary_mul] at hh

lemma sqrt_schatten_two (ρ : Matrix n n ℂ) (hρ : IsDensityOperator ρ) : schattenNorm 2 (CFC.sqrt ρ)=1 := by
  rw [QuantRecoverySupport.RecoverySchatten.schatten_two,QuantRecoverySupport.RecoveryCurveRight.sqrt_star,CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg,hρ.2]
  norm_num

lemma rootFidelity_le_one (ρ σ : Matrix n n ℂ) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    rootFidelity ρ σ ≤ 1 := by
  have hh := traceNorm_mul_le_two (CFC.sqrt ρ) (CFC.sqrt σ)
  rwa [sqrt_schatten_two ρ hρ,sqrt_schatten_two σ hσ,one_mul] at hh

lemma traceNorm_nonneg {m : Type} [Fintype m] (A : Matrix m n ℂ) : 0 ≤ traceNorm A := by
  exact (Complex.nonneg_iff.mp ((CFC.sqrt_nonneg (Aᴴ*A)).posSemidef.trace_nonneg)).1

lemma rootFidelity_nonneg (ρ σ : Matrix n n ℂ) : 0 ≤ rootFidelity ρ σ := traceNorm_nonneg _

end QuantRecoverySupport.RecoveryFidelityBound

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.PetzSpectral QuantRecoverySupport.PetzChannel QuantRecoverySupport.RecoverySupport
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryFidelityRegularity
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma rotated_density (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) (t : ℝ) :
    IsDensityOperator (rotatedPetz σ N t (N.apply ρ)) := by
  refine ⟨QuantRecoverySupport.RecoveryCurveRight.rotated_positive σ N hσ _ (map_positive N ρ hρ.1) t,?_⟩
  have hs := map_supp ρ σ hρ.1 hσ hsupp N
  have hp : supportProj (N.apply σ)*N.apply ρ=N.apply ρ := by
    simpa only [QuantRecoverySupport.PetzSpectral.pow_one _ (map_positive N ρ hρ.1)] using
      support_mul_pow _ _ (map_positive N ρ hρ.1) (map_positive N σ hσ) hs 1
  rw [QuantRecoverySupport.PetzCompletion.rotated_trace σ hσ N t (N.apply ρ),hp,trace_preserved,hρ.2]

lemma continuous_rotated (σ : Matrix a a ℂ) (N : QChannel a b)
    (hσ : σ.PosSemidef) (Q : Matrix b b ℂ) : Continuous (fun t : ℝ => rotatedPetz σ N (t/2) Q) := by
  have hS := (QuantRecoverySupport.RecoveryPowerCalculus.supportPow_differentiable σ hσ.isHermitian).continuous
  have hT := (QuantRecoverySupport.RecoveryPowerCalculus.supportPow_differentiable (N.apply σ) (map_positive N σ hσ).isHermitian).continuous
  have hK (i : N.ι) : Continuous (fun t : ℝ => QuantRecoverySupport.PetzCompletion.petzKraus σ N (t/2) i) := by
    have hL : Continuous (fun t : ℝ => supportPow σ (1/2-((t/2 : ℝ) : ℂ)*Complex.I)) := hS.comp (by fun_prop)
    have hR : Continuous (fun t : ℝ => supportPow (N.apply σ) (-(1/2)+((t/2 : ℝ) : ℂ)*Complex.I)) := hT.comp (by fun_prop)
    exact (hL.matrix_mul continuous_const).matrix_mul hR
  simp_rw [← QuantRecoverySupport.PetzCompletion.kraus_apply σ hσ N]
  exact continuous_finsetSum _ (fun i _ => ((hK i).matrix_mul continuous_const).matrix_mul (hK i).matrix_conjTranspose)

lemma continuous_rootFidelity {R : ℝ → Matrix a a ℂ} (hR : Continuous R) (hP : ∀ t, (R t).PosSemidef)
    (ρ : Matrix a a ℂ) : Continuous (fun t => rootFidelity ρ (R t)) := by
  have hSR : Continuous (fun t => CFC.sqrt (R t)) :=
    CFC.continuousOn_sqrt.comp_continuous hR (fun t => (hP t).nonneg)
  have hA : Continuous (fun t => CFC.sqrt ρ*CFC.sqrt (R t)) := continuous_const.matrix_mul hSR
  have hG := hA.matrix_conjTranspose.matrix_mul hA
  have hS : Continuous (fun t => CFC.sqrt ((CFC.sqrt ρ*CFC.sqrt (R t))ᴴ*(CFC.sqrt ρ*CFC.sqrt (R t)))) :=
    CFC.continuousOn_sqrt.comp_continuous hG (fun t => (posSemidef_conjTranspose_mul_self _).nonneg)
  exact Complex.continuous_re.comp hS.matrix_trace

lemma measurable_negLog2 {f : ℝ → ℝ} (hf : Measurable f) : Measurable (fun t => negLog2 (f t)) := by
  unfold negLog2
  apply Measurable.ite (measurableSet_le hf measurable_const) measurable_const
  apply ENNReal.measurable_ofReal.comp
  unfold Real.logb
  exact ((Real.measurable_log.comp hf).div_const _).neg

end QuantRecoverySupport.RecoveryFidelityRegularity

end

noncomputable section
open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P21 WildeQIT.Recover
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QuantRecoverySupport.RecoveryNegativeLog

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
lemma root_log_eq (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hθ : 0 < θ) :
    extendedLog (r^θ) = -(((θ*Real.log 2/2 : ℝ) : EReal)*(negLog2 (r^2) : EReal)) := by
  have hc : 0 < θ*Real.log 2/2 := by positivity [log_two_pos]
  by_cases hr : r=0
  · simp only [hr,Real.zero_rpow hθ.ne',extendedLog,le_refl,if_true,zero_pow (by norm_num : (2 : ℕ) ≠ 0),negLog2]
    rw [EReal.coe_ennreal_top,EReal.coe_mul_top_of_pos hc,EReal.neg_top]
  · have hp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hsq : 0 < r^2 := sq_pos_of_pos hp
    have hsq1 : r^2 ≤ 1 := by nlinarith
    have hn : 0 ≤ -Real.logb 2 (r^2) := by
      unfold Real.logb
      rw [← neg_div]
      exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hsq.le hsq1)) log_two_pos.le
    rw [extendedLog,if_neg (not_le.mpr (Real.rpow_pos_of_pos hp θ)),Real.log_rpow hp,
      negLog2,if_neg (not_le.mpr hsq),EReal.coe_ennreal_ofReal,max_eq_left (by exact_mod_cast hn),
      ← EReal.coe_mul,← EReal.coe_neg]
    congr 1
    rw [Real.logb,Real.log_pow]
    field_simp [log_two_pos.ne']
    <;> ring

lemma upperLogIntegral_neg_coe (f : ℝ → ℝ≥0∞) :
    upperLogIntegral (fun t => -(f t : EReal)) = -((∫⁻ t, f t) : EReal) := by
  unfold upperLogIntegral
  have hp (t : ℝ) : (-(f t : EReal)).toENNReal=0 :=
    EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _))
  simp only [hp,lintegral_zero,neg_neg,EReal.toENNReal_coe,EReal.coe_ennreal_zero,zero_sub]

lemma upper_weighted_rootLog (r w : ℝ → ℝ) (θ : ℝ)
    (hr0 : ∀ t, 0 ≤ r t) (hr1 : ∀ t, r t ≤ 1) (hw : ∀ t, 0 ≤ w t) (hθ : 0 < θ) :
    upperLogIntegral (fun t => (w t : EReal)*extendedLog ((r t)^θ)) =
      -(((ENNReal.ofReal (θ*Real.log 2/2))*(∫⁻ t, ENNReal.ofReal (w t)*negLog2 ((r t)^2)) : ℝ≥0∞) : EReal) := by
  let c := θ*Real.log 2/2
  have hc : 0 ≤ c := by dsimp [c]; positivity [log_two_pos]
  have hcoe (x : ℝ) (hx : 0 ≤ x) : (ENNReal.ofReal x : EReal)=(x : EReal) := by
    rw [EReal.coe_ennreal_ofReal,max_eq_left (by exact_mod_cast hx)]
  have he (t : ℝ) : (w t : EReal)*extendedLog ((r t)^θ) =
      -((ENNReal.ofReal c*(ENNReal.ofReal (w t)*negLog2 ((r t)^2)) : ℝ≥0∞) : EReal) := by
    rw [root_log_eq _ _ (hr0 t) (hr1 t) hθ]
    rw [EReal.coe_ennreal_mul,EReal.coe_ennreal_mul,hcoe c hc,hcoe (w t) (hw t),mul_neg]
    simp only [c]
    congr 1
    ac_rfl
  simp_rw [he]
  rw [upperLogIntegral_neg_coe,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end QuantRecoverySupport.RecoveryNegativeLog

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.RecoveryCurve QuantRecoverySupport.RecoveryRectInterpolation
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker
namespace QuantRecoverySupport.RecoveryPrelimit
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma curve_bound (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog (rSchatten (2/(1+θ)) (curve ρ σ N θ)) ≤ upperLogIntegral (fun t =>
      (betaDensity θ t : EReal)*extendedLog ((rootFidelity ρ (rotatedPetz σ N (t/2) (N.apply ρ)))^θ)) := by
  exact WildeQIT.Recover.recoveryCurve_hirschman_bound ρ σ N hρ hσ θ hθ0 hθ1
end QuantRecoverySupport.RecoveryPrelimit
end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover Filter
open scoped MatrixOrder ComplexOrder Topology Matrix.Norms.L2Operator
namespace QuantRecoverySupport.RecoveryRenyiLimit
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma entropy_limit (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    Tendsto (fun α : ℝ => ((renyiDelta ρ σ N α / Real.log 2 : ℝ) : EReal)) (𝓝[≠] 1)
      (𝓝 (qRelEntropy ρ σ-qRelEntropy (N.apply ρ) (N.apply σ))) := by
  exact WildeQIT.Recover.lemma_12_4_1 ρ σ N hρ hσ hsupp
end QuantRecoverySupport.RecoveryRenyiLimit
end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.RecoveryCurve QuantRecoverySupport.RecoveryRectInterpolation QuantRecoverySupport.RecoveryNegativeLog QuantRecoverySupport.RecoveryFidelityRegularity
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Topology Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace QuantRecoverySupport.RecoveryPrelimitIntegral
attribute [local instance] Classical.decEq
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def penalty (ρ σ : Matrix a a ℂ) (N : QChannel a b) (t : ℝ) :=
  negLog2 (fidelity ρ (rotatedPetz σ N (t/2) (N.apply ρ)))
def weightedPenalty (ρ σ : Matrix a a ℂ) (N : QChannel a b) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ENNReal.ofReal (betaDensity θ t)*penalty ρ σ N t

lemma integral_bound (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ)
    (α : ℝ) (hα0 : 1/2 < α) (hα1 : α < 1) (hQ : 0 < renyiQ ρ σ N α) :
    (weightedPenalty ρ σ N ((1-α)/α) : EReal) ≤ ((renyiDelta ρ σ N α/Real.log 2 : ℝ) : EReal) := by
  let θ := (1-α)/α
  have ha : 0 < α := by linarith
  have hθ0 : 0 < θ := div_pos (by linarith) ha
  have hθ1 : θ < 1 := (div_lt_one ha).mpr (by linarith)
  have hp : 2/(1+θ)=2*α := by dsimp [θ]; field_simp; ring
  have hn : rSchatten (2/(1+θ)) (curve ρ σ N θ)=(renyiQ ρ σ N α)^(1/(2*α)) := by
    rw [hp,← renyiOp_eq ρ σ N α]
    unfold rSchatten renyiQ
    have he : (2*α)/2=α := by ring
    rw [he,← QuantRecoverySupport.RecoveryPowerCalculus.supportPow_pos_eq_cfc _ (posSemidef_conjTranspose_mul_self _) ha]
  have hnorm : 0 < (renyiQ ρ σ N α)^(1/(2*α)) := Real.rpow_pos_of_pos hQ _
  let r : ℝ → ℝ := fun t => rootFidelity ρ (rotatedPetz σ N (t/2) (N.apply ρ))
  have hr0 (t : ℝ) : 0 ≤ r t := QuantRecoverySupport.RecoveryFidelityBound.rootFidelity_nonneg _ _
  have hr1 (t : ℝ) : r t ≤ 1 := QuantRecoverySupport.RecoveryFidelityBound.rootFidelity_le_one _ _ hρ (rotated_density ρ σ N hρ hσ hsupp _)
  have hb (t : ℝ) : 0 ≤ betaDensity θ t := ((hirschmanDensities.1 θ hθ0 hθ1).1 t).2
  have hh := QuantRecoverySupport.RecoveryPrelimit.curve_bound ρ σ N hρ hσ θ hθ0 hθ1
  rw [hn,extendedLog,if_neg (not_le.mpr hnorm),Real.log_rpow hQ] at hh
  rw [upper_weighted_rootLog r (betaDensity θ) θ hr0 hr1 hb hθ0] at hh
  change ((1/(2*α)*Real.log (renyiQ ρ σ N α) : ℝ) : EReal) ≤
    -((ENNReal.ofReal (θ*Real.log 2/2)*weightedPenalty ρ σ N θ : ℝ≥0∞) : EReal) at hh
  have hc : 0 < θ*Real.log 2/2 := by positivity [log_two_pos]
  have hcoe : (ENNReal.ofReal (θ*Real.log 2/2) : EReal)=((θ*Real.log 2/2 : ℝ) : EReal) := by
    rw [EReal.coe_ennreal_ofReal,max_eq_left (by exact_mod_cast hc.le)]
  have hneg := EReal.neg_le_neg_iff.mpr hh
  rw [neg_neg,EReal.coe_ennreal_mul,hcoe] at hneg
  have hmul := mul_le_mul_of_nonneg_left hneg
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr hc.le))
  rw [← mul_assoc,← EReal.coe_mul,inv_mul_cancel₀ hc.ne',EReal.coe_one,one_mul,
    ← EReal.coe_neg,← EReal.coe_mul] at hmul
  have he : (θ*Real.log 2/2)⁻¹ * -(1/(2*α)*Real.log (renyiQ ρ σ N α)) = renyiDelta ρ σ N α/Real.log 2 := by
    unfold renyiDelta
    dsimp [θ]
    field_simp [ha.ne',sub_ne_zero.mpr hα1.ne,sub_ne_zero.mpr hα1.ne',log_two_pos.ne']
    <;> ring
  rwa [he] at hmul

end QuantRecoverySupport.RecoveryPrelimitIntegral

end

noncomputable section
open Matrix WildeQIT WildeQIT.Recover QuantRecoverySupport.RecoveryPrelimitIntegral QuantRecoverySupport.RecoveryFidelityRegularity
  QuantRecoverySupport.RecoveryEntropyUnits QuantRecoverySupport.RecoveryRenyiPositivity Filter MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Topology Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace QuantRecoverySupport.RecoveryQuantitative

def θn (n : ℕ) : ℝ := 1/((n : ℝ)+2)
def αn (n : ℕ) : ℝ := 1/(1+θn n)
lemma θn_bounds (n : ℕ) : 0 < θn n ∧ θn n < 1 := by
  unfold θn
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  constructor
  · exact div_pos zero_lt_one (by positivity)
  · exact (div_lt_one (by positivity)).mpr (by linarith)
lemma αn_bounds (n : ℕ) : 1/2 < αn n ∧ αn n < 1 := by
  have ht := θn_bounds n
  have hd : 0 < 1+θn n := by linarith
  constructor
  · exact (lt_div_iff₀ hd).mpr (by linarith)
  · exact (div_lt_one hd).mpr (by linarith)
lemma θ_αn (n : ℕ) : (1-αn n)/αn n=θn n := by
  have ht := θn_bounds n
  unfold αn
  field_simp [show (1 : ℝ)+θn n ≠ 0 by linarith]
  <;> ring
lemma θn_limit : Tendsto θn atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1/((n : ℝ)+2)) atTop (𝓝 0)
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
lemma θn_limit_gt : Tendsto θn atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨θn_limit,Eventually.of_forall (fun n => (θn_bounds n).1)⟩
lemma αn_limit : Tendsto αn atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).div ((tendsto_const_nhds (x := (1 : ℝ))).add θn_limit) (by norm_num : (1 : ℝ)+0 ≠ 0)
  change Tendsto (fun n : ℕ => 1/(1+θn n)) atTop (𝓝 1)
  simpa only [Pi.div_def,add_zero,div_one] using hh
lemma αn_limit_ne : Tendsto αn atTop (𝓝[≠] 1) :=
  tendsto_nhdsWithin_iff.mpr ⟨αn_limit,Eventually.of_forall (fun n => (αn_bounds n).2.ne)⟩

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma quantitative (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    (((∫⁻ t : ℝ, ENNReal.ofReal (betaZero t)*penalty ρ σ N t) : ℝ≥0∞) : EReal) ≤
      qRelEntropy ρ σ-qRelEntropy (N.apply ρ) (N.apply σ) := by
  let D := naturalLoss ρ σ N/Real.log 2
  let F : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (betaDensity (θn n) t)*penalty ρ σ N t
  have hp : Measurable (penalty ρ σ N) := by
    have hR := continuous_rotated σ N hσ (N.apply ρ)
    have hr := continuous_rootFidelity hR (fun t => (rotated_density ρ σ N hρ hσ hsupp (t/2)).1) ρ
    exact measurable_negLog2 (hr.pow 2).measurable
  have hFm (n : ℕ) : AEMeasurable (F n) := by
    have hb := (hirschmanDensities.1 (θn n) (θn_bounds n).1 (θn_bounds n).2).2.2.1
    exact (ENNReal.measurable_ofReal.comp_aemeasurable hb.aemeasurable).mul hp.aemeasurable
  have hpoint (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 (ENNReal.ofReal (betaZero t)*penalty ρ σ N t)) := by
    have hb := (hirschmanDensities.2.1 t).comp θn_limit_gt
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
    have hβ : 0 < betaZero t := by
      unfold betaZero
      have hh := Real.one_le_cosh (Real.pi*t)
      exact div_pos Real.pi_pos (by linarith)
    exact ENNReal.Tendsto.mul_const he (Or.inl (ENNReal.ofReal_pos.mpr hβ).ne')
  have hFatou := lintegral_liminf_le' (u := atTop) hFm
  have hEq (t : ℝ) : liminf (fun n => F n t) atTop=ENNReal.ofReal (betaZero t)*penalty ρ σ N t :=
    (hpoint t).liminf_eq
  simp_rw [hEq] at hFatou
  have hlimE := (QuantRecoverySupport.RecoveryRenyiLimit.entropy_limit ρ σ N hρ hσ hsupp).comp αn_limit_ne
  rw [← entropy_difference ρ σ N hρ.1 hσ hsupp] at hlimE
  have hlim : Tendsto (fun n => renyiDelta ρ σ N (αn n)/Real.log 2) atTop (𝓝 D) := EReal.tendsto_coe.mp hlimE
  have hQ : ∀ᶠ n : ℕ in atTop, 0 < renyiQ ρ σ N (αn n) :=
    αn_limit.eventually (eventually_renyiQ_pos ρ σ N hρ hσ hsupp)
  have hboundE : ∀ᶠ n : ℕ in atTop,
      (weightedPenalty ρ σ N (θn n) : EReal) ≤ ((renyiDelta ρ σ N (αn n)/Real.log 2 : ℝ) : EReal) := by
    filter_upwards [hQ] with n hn
    have hh := integral_bound ρ σ N hρ hσ hsupp (αn n) (αn_bounds n).1 (αn_bounds n).2 hn
    rwa [θ_αn n] at hh
  have hD : 0 ≤ D := by
    apply ge_of_tendsto hlim
    filter_upwards [hboundE] with n hn
    exact EReal.coe_nonneg.mp ((EReal.coe_ennreal_nonneg _).trans hn)
  have hbound : ∀ᶠ n : ℕ in atTop, weightedPenalty ρ σ N (θn n) ≤ ENNReal.ofReal (renyiDelta ρ σ N (αn n)/Real.log 2) := by
    filter_upwards [hboundE] with n hn
    simpa only [EReal.toENNReal_coe,EReal.real_coe_toENNReal] using EReal.toENNReal_le_toENNReal hn
  have hlimN : Tendsto (fun n => ENNReal.ofReal (renyiDelta ρ σ N (αn n)/Real.log 2)) atTop (𝓝 (ENNReal.ofReal D)) := by
    simpa only [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hupper := Filter.liminf_le_liminf hbound
  rw [hlimN.liminf_eq] at hupper
  have hfinal := hFatou.trans hupper
  have he := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hfinal
  rw [EReal.coe_ennreal_ofReal,max_eq_left hD] at he
  rwa [entropy_difference ρ σ N hρ.1 hσ hsupp] at he

end QuantRecoverySupport.RecoveryQuantitative

end

open Matrix WildeQIT WildeQIT.Recover Filter
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped MatrixOrder ComplexOrder ComplexConjugate Topology ENNReal Matrix.Norms.L2Operator Kronecker

set_option autoImplicit false



/-- **Theorem 12.5.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Theorem 12.5.1, (12.103), p. 378). Let `ρ` be a density operator, `σ` positive semi-definite with
`supp(ρ) ⊆ supp(σ)`, and `𝒩` a quantum channel (Definition 12.1.1). Then
`D(ρ‖σ) − D(𝒩(ρ)‖𝒩(σ)) ≥ −∫ dt β₀(t) log F(ρ, (ℛ^{t/2}_{σ,𝒩} ∘ 𝒩)(ρ))`,
with `β₀(t) = (π/2)[cosh(πt) + 1]⁻¹`.

**Formalization Note** Finite dimensions; `log` is base 2. `D` is `EReal`-valued
(Definition 11.8.2). The right side is the lower Lebesgue integral of the `[0, +∞]`-valued
integrand `β₀(t) · (−log₂ F)`, with `−log₂ 0 = +∞`, so no Bochner default value occurs. `β₀` is
`betaZero` of the published definitions of Junge–Renner–Sutter–Wilde–Winter (2018). -/
theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    qRelEntropy ρ σ - qRelEntropy (N.apply ρ) (N.apply σ) ≥
      (((∫⁻ t : ℝ, ENNReal.ofReal (betaZero t) *
          negLog2 (fidelity ρ (rotatedPetz σ N (t / 2) (N.apply ρ)))) : ℝ≥0∞) : EReal) := by
  exact QuantRecoverySupport.RecoveryQuantitative.quantitative ρ σ N hρ hσ hsupp