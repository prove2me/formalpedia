-- Prove2me | solution 1 for WildeQIT.Recover.proposition_12_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-15T20:52:02.012414+00:00
-- url     : https://prove2.me/submissions/fcaa9a66-f7cd-441e-8223-5d493fc3128e

import Definitions.Def_WildeQIT_Recover_rotatedPetz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
noncomputable section
open Matrix WildeQIT.Recover
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzSpectral
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
end PetzSpectral
noncomputable section
open Matrix WildeQIT WildeQIT.Recover
open scoped ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzChannel
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
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using PetzSpectral.pow_real_star A hA.isHermitian (1/2)
lemma petz_input (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    petzMap A N (N.apply A) = supportPow A (1/2)*adjointMap N (supportProj (N.apply A))*supportPow A (1/2) := by
  rw [petzMap,PetzSpectral.inverse_sandwich _ (map_positive N A hA)]
lemma petz_defect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    A-petzMap A N (N.apply A) = supportPow A (1/2)*adjointMap N (1-supportProj (N.apply A))*supportPow A (1/2) := by
  rw [adjoint_sub,adjoint_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,PetzSpectral.pow_half_square A hA,petz_input N A hA]
lemma petz_perfect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) : petzMap A N (N.apply A)=A := by
  have hd : (A-petzMap A N (N.apply A)).PosSemidef := by
    rw [petz_defect N A hA]
    have hh := (adjoint_positive N _ (PetzSpectral.support_complement_pos _ (map_positive N A hA))).mul_mul_conjTranspose_same (supportPow A (1/2))
    rwa [half_star A hA] at hh
  have ht : (A-petzMap A N (N.apply A)).trace=0 := by
    rw [trace_sub,petz_input N A hA]
    have hh : trace (supportPow A (1/2)*adjointMap N (supportProj (N.apply A))*supportPow A (1/2)) = A.trace := by
      rw [trace_mul_cycle,PetzSpectral.pow_half_square A hA,trace_dual,trace_mul_comm,PetzSpectral.support_mul _ (map_positive N A hA),trace_preserved]
    rw [hh,sub_self]
  exact (sub_eq_zero.mp (hd.trace_eq_zero_iff.mp ht)).symm
lemma rotated_perfect (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) (t : ℝ) :
    rotatedPetz A N t (N.apply A)=A := by
  unfold rotatedPetz rotU
  rw [PetzSpectral.rotation_self _ (map_positive N A hA),petz_perfect N A hA,PetzSpectral.rotation_self A hA]
end PetzChannel
set_option autoImplicit false
open WildeQIT.Recover


/-- **Proposition 12.3.1 (Perfect Recovery)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Proposition 12.3.1, (12.38), p. 372). Let `σ` be positive semi-definite and `𝒩`
a quantum channel. Every rotated Petz map recovers `σ` from `𝒩(σ)`: `ℛ^t_{σ,𝒩}(𝒩(σ)) = σ` for
every `t ∈ ℝ`.

**Formalization Note** Finite dimensions; channels in Choi–Kraus form. All powers of `σ` and
`𝒩(σ)` are taken on their supports (Definition 3.3.1). -/
theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix a a ℂ) (hσ : σ.PosSemidef) (N : QChannel a b) (t : ℝ) :
    rotatedPetz σ N t (N.apply σ) = σ := by
  exact PetzChannel.rotated_perfect N σ hσ t