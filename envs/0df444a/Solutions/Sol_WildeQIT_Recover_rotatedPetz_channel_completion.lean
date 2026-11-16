-- Prove2me | solution 1 for WildeQIT.Recover.rotatedPetz_channel_completion
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-15T21:01:57.610061+00:00
-- url     : https://prove2.me/submissions/533de8e2-d35f-4ae3-b385-6f853ee304b2

import Definitions.Def_WildeQIT_Recover_rotatedPetz
import Theorems.Thm_WildeQIT_Recover_proposition_12_3_1
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Matrix.Basis
open WildeQIT
noncomputable section
open Matrix WildeQIT.Recover
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzCompletionSpectral
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
end PetzCompletionSpectral
namespace PetzCompletionChannel
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma map_positive (N : QChannel a b) (A : Matrix a a ℂ) (hA : A.PosSemidef) : (N.apply A).PosSemidef := by
  unfold QChannel.apply
  exact posSemidef_sum _ (fun i _ => hA.mul_mul_conjTranspose_same (N.K i))
end PetzCompletionChannel

noncomputable section
open Matrix WildeQIT WildeQIT.Recover PetzCompletionSpectral PetzCompletionChannel
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PetzCompletion
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
          convert PetzCompletionSpectral.pow_zero (N.apply A) using 1 <;> simp [map_ofNat] <;> ring

def complementKraus (a0 : a) (E : Matrix b b ℂ) (j : b) : Matrix a b ℂ :=
  Matrix.single a0 j (1 : ℂ) * (1-E)

lemma complement_complete (a0 : a) (E : Matrix b b ℂ)
    (he : Eᴴ = E) (hi : E*E=E) :
    ∑ j, (complementKraus a0 E j)ᴴ * complementKraus a0 E j = 1-E := by
  have hsingle : ∀ j : b, (Matrix.single a0 j (1 : ℂ) : Matrix a b ℂ)ᴴ = Matrix.single j a0 1 := by
    intro j
    ext x y
    simp [Matrix.single,conjTranspose_apply,and_comm]
  simp only [complementKraus,conjTranspose_mul,conjTranspose_sub,conjTranspose_one,he,hsingle]
  simp only [← Matrix.mul_assoc]
  simp only [Matrix.mul_assoc (1-E) (Matrix.single _ _ _),single_mul_single_same,one_mul]
  rw [← Finset.mul_sum,← Finset.sum_mul,Matrix.sum_single_one,Matrix.one_mul]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_one,hi,sub_self,sub_zero]

def channel (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) (a0 : a) : QChannel b a where
  ι := Sum N.ι b
  K := Sum.elim (petzKraus A N t) (complementKraus a0 (supportProj (N.apply A)))
  complete := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr]
    rw [kraus_complete_support A hA N t,complement_complete a0 _
      (support_star _ (map_positive N A hA).isHermitian)
      (support_square _ (map_positive N A hA).isHermitian)]
    abel

lemma complement_apply (a0 : a) (E : Matrix b b ℂ)
    (he : Eᴴ = E) (hi : E*E=E) (Q : Matrix b b ℂ) :
    (∑ j, complementKraus a0 E j * Q * (complementKraus a0 E j)ᴴ) =
      trace ((1-E)*Q) • Matrix.single a0 a0 (1 : ℂ) := by
  have hd : (1-E)*(1-E)=1-E := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_one,hi,sub_self,sub_zero]
  calc
    _ = ∑ j : b, Matrix.single a0 a0 (((1-E)*Q*(1-E)) j j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [complementKraus,conjTranspose_mul,conjTranspose_sub,conjTranspose_one,he,
        conjTranspose_single,star_one]
      calc
        _ = Matrix.single a0 j (1 : ℂ) * ((1-E)*Q*(1-E)) * Matrix.single j a0 (1 : ℂ) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [single_mul_mul_single,one_mul,mul_one]
    _ = trace ((1-E)*Q*(1-E)) • Matrix.single a0 a0 (1 : ℂ) := by
      ext x y
      rw [Matrix.sum_apply]
      by_cases hx : a0=x <;> by_cases hy : a0=y <;>
        simp [Matrix.single,Matrix.of_apply,hx,hy,trace]
    _ = _ := by rw [trace_mul_cycle,hd]

lemma channel_apply (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) (a0 : a) (Q : Matrix b b ℂ) :
    (channel A hA N t a0).apply Q = rotatedPetz A N t Q +
      trace ((1-supportProj (N.apply A))*Q) • Matrix.single a0 a0 (1 : ℂ) := by
  change (∑ i : Sum N.ι b, (Sum.elim (petzKraus A N t) (complementKraus a0 (supportProj (N.apply A))) i) * Q *
    (Sum.elim (petzKraus A N t) (complementKraus a0 (supportProj (N.apply A))) i)ᴴ) = _
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  rw [kraus_apply A hA N t Q,complement_apply a0 _
    (support_star _ (map_positive N A hA).isHermitian)
    (support_square _ (map_positive N A hA).isHermitian)]

lemma channel_recovers (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) (a0 : a) : (channel A hA N t a0).apply (N.apply A)=A := by
  rw [channel_apply,WildeQIT.Recover.proposition_12_3_1 A hA N t,Matrix.sub_mul,Matrix.one_mul,
    support_mul _ (map_positive N A hA),sub_self,trace_zero,zero_smul,add_zero]

lemma channel_apply_supported (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) (a0 : a) (Q : Matrix b b ℂ) (hQ : supportProj (N.apply A)*Q=Q) :
    (channel A hA N t a0).apply Q = rotatedPetz A N t Q := by
  rw [channel_apply,Matrix.sub_mul,Matrix.one_mul,hQ,sub_self,trace_zero,zero_smul,add_zero]

lemma rotated_trace (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) (Q : Matrix b b ℂ) :
    trace (rotatedPetz A N t Q)=trace (supportProj (N.apply A)*Q) := by
  rw [← kraus_apply A hA N t Q,trace_sum,← kraus_complete_support A hA N t,
    Finset.sum_mul,trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact trace_mul_cycle _ _ _

theorem completion_exists (A : Matrix a a ℂ) (hA : A.PosSemidef) (N : QChannel a b)
    (t : ℝ) (a0 : a) : ∃ R : QChannel b a,
    (∀ Q : Matrix b b ℂ, R.apply Q = rotatedPetz A N t Q +
      trace ((1-supportProj (N.apply A))*Q) • Matrix.single a0 a0 (1 : ℂ)) ∧
    R.apply (N.apply A)=A ∧
    (∀ Q : Matrix b b ℂ, supportProj (N.apply A)*Q=Q → R.apply Q=rotatedPetz A N t Q) := by
  exact ⟨channel A hA N t a0,channel_apply A hA N t a0,channel_recovers A hA N t a0,
    channel_apply_supported A hA N t a0⟩

end PetzCompletion

set_option autoImplicit false
open WildeQIT.Recover

theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix a a ℂ) (hσ : σ.PosSemidef) (N : QChannel a b) (t : ℝ) (a0 : a) :
    ∃ R : QChannel b a,
      (∀ Q : Matrix b b ℂ, R.apply Q = rotatedPetz σ N t Q +
        Matrix.trace ((1-supportProj (N.apply σ))*Q) • Matrix.single a0 a0 (1 : ℂ)) ∧
      R.apply (N.apply σ)=σ ∧
      (∀ Q : Matrix b b ℂ, supportProj (N.apply σ)*Q=Q → R.apply Q=rotatedPetz σ N t Q) := by
  exact PetzCompletion.completion_exists σ hσ N t a0