-- Prove2me | solution 1 for SYKFastMix.FastMixing.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:53:02.658848+00:00
-- url     : https://prove2.me/submissions/4eff96da-c871-4092-b8a3-c6572fe9b922

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder NNReal ENNReal

namespace SYKFastMix.FastMixing
def subblock {I ι : Type} (M : Matrix (I × ι) (I × ι) ℂ) (i j : I) : Mat ι :=
  Matrix.of (fun a b ↦ M (i,a) (j,b))

lemma matrix_entry_norm_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Mat ι) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm x
  have he := PiLp.norm_apply_le ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x) i
  have hx : ‖x‖ = 1 := by simp [x, PiLp.norm_single]
  rw [hx, mul_one] at h
  change _ ≤ ‖A‖ at h
  apply le_trans ?_ h
  convert! he using 1
  simp [x, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def act (T : Super ι) : Mat ι →L[ℂ] Mat ι where
  toFun := applySuper T
  map_add' X Y := by ext a b; simp [applySuper, mul_add, Finset.sum_add_distrib]
  map_smul' z X := by ext a b; simp [applySuper, Finset.mul_sum, mul_left_comm]
  cont := by unfold applySuper; fun_prop

@[simp] lemma act_apply (T : Super ι) (X : Mat ι) : act T X = applySuper T X := rfl

lemma applySuper_mul (T U : Super ι) (X : Mat ι) :
    applySuper (T * U) X = applySuper T (applySuper U X) := by
  ext a b
  simp only [applySuper, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

def actAlgHom : Super ι →ₐ[ℂ] (Mat ι →L[ℂ] Mat ι) where
  toFun := act
  map_one' := by ext X a b; simp [act, applySuper, Matrix.one_apply]
  map_mul' T U := by ext1 X; exact applySuper_mul T U X
  map_zero' := by ext X a b; simp [act, applySuper]
  map_add' T U := by ext X a b; simp [act, applySuper, add_mul, Finset.sum_add_distrib]
  commutes' z := by
    ext X a b
    simp [act, applySuper, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

lemma act_exp (T : Super ι) : act (mexp T) = NormedSpace.exp (act T) := by
  letI : NormedAlgebra ℚ (Super ι) := .restrictScalars ℚ ℂ (Super ι)
  exact NormedSpace.map_exp (actAlgHom (ι := ι))
    (actAlgHom (ι := ι)).toLinearMap.continuous_of_finiteDimensional T

lemma applySuper_super (f : Mat ι →ₗ[ℂ] Mat ι) (X : Mat ι) :
    applySuper (super f) X = f X := by
  ext a b
  change (∑ p : ι × ι, f (Matrix.single p.1 p.2 1) a b * X p.1 p.2) = f X a b
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) by simp]
  rw [map_smul]
  change _ = X i j * f (Matrix.single i j 1) a b
  exact mul_comm _ _

def evalSuper (X : Mat ι) : Super ι →L[ℂ] Mat ι where
  toFun := fun T ↦ applySuper T X
  map_add' T U := by ext a b; simp [applySuper, add_mul, Finset.sum_add_distrib]
  map_smul' z T := by ext a b; simp [applySuper, Finset.mul_sum, mul_assoc]
  cont := by unfold applySuper; fun_prop

@[simp] lemma evalSuper_apply (X : Mat ι) (T : Super ι) : evalSuper X T = applySuper T X := rfl

lemma applySuper_smul (z : ℂ) (T : Super ι) (X : Mat ι) :
    applySuper (z • T) X = z • applySuper T X := (evalSuper X).map_smul z T

def leftAct (H : Mat ι) : Mat ι →L[ℂ] Mat ι := ContinuousLinearMap.mul ℂ (Mat ι) H
def rightAct (H : Mat ι) : Mat ι →L[ℂ] Mat ι := (ContinuousLinearMap.mul ℂ (Mat ι)).flip H

@[simp] lemma leftAct_apply (H X : Mat ι) : leftAct H X = H * X := rfl
@[simp] lemma rightAct_apply (H X : Mat ι) : rightAct H X = X * H := rfl

lemma act_ad (H : Mat ι) : act (ad H) = leftAct H - rightAct H := by
  ext1 X
  exact applySuper_super (leftAct H - rightAct H).toLinearMap X

lemma act_smul (s : ℂ) (T : Super ι) : act (s • T) = s • act T :=
  (actAlgHom (ι := ι)).toLinearMap.map_smul s T

lemma leftAct_smul (s : ℂ) (H : Mat ι) : leftAct (s • H) = s • leftAct H := by
  ext1 X
  simp only [leftAct_apply, _root_.smul_apply, smul_mul_assoc]

lemma rightAct_smul (s : ℂ) (H : Mat ι) : rightAct (s • H) = s • rightAct H := by
  ext1 X
  simp only [rightAct_apply, _root_.smul_apply, mul_smul_comm]

lemma leftAct_pow_apply (H X : Mat ι) (n : ℕ) : (leftAct H ^ n) X = H^n * X := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ']; simp [ih, mul_assoc]

lemma rightAct_pow_apply (H X : Mat ι) (n : ℕ) : (rightAct H ^ n) X = X * H^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ]; simp [ih, mul_assoc]

lemma exp_leftAct_apply (H X : Mat ι) : NormedSpace.exp (leftAct H) X = mexp H * X := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (leftAct H)).mapL
    (ContinuousLinearMap.apply ℂ (Mat ι) X)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H).mapL (rightAct X)
  apply HasSum.unique h1
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    leftAct_pow_apply, rightAct_apply, smul_mul_assoc, mexp] using h2

lemma exp_rightAct_apply (H X : Mat ι) : NormedSpace.exp (rightAct H) X = X * mexp H := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (rightAct H)).mapL
    (ContinuousLinearMap.apply ℂ (Mat ι) X)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H).mapL (leftAct X)
  apply HasSum.unique h1
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    rightAct_pow_apply, leftAct_apply, mul_smul_comm, mexp] using h2

lemma exp_ad_apply (H X : Mat ι) (s : ℂ) :
    applySuper (mexp (s • ad H)) X = mexp (s • H) * X * mexp ((-s) • H) := by
  letI : NormedAlgebra ℚ (Mat ι →L[ℂ] Mat ι) :=
    .restrictScalars ℚ ℂ (Mat ι →L[ℂ] Mat ι)
  have he : act (s • ad H) = leftAct (s • H) + rightAct ((-s) • H) := by
    rw [act_smul, act_ad, leftAct_smul, rightAct_smul]
    module
  have hcomm : Commute (leftAct (s • H)) (rightAct ((-s) • H)) := by
    apply ContinuousLinearMap.ext
    intro X
    change (s • H) * (X * ((-s) • H)) = ((s • H) * X) * ((-s) • H)
    exact (mul_assoc _ _ _).symm
  rw [← act_apply, act_exp, he]
  have hexp := NormedSpace.exp_add_of_commute (𝔸 := Mat ι →L[ℂ] Mat ι) hcomm
  have happ := congrArg (fun f : Mat ι →L[ℂ] Mat ι ↦ f X) hexp
  calc
    (NormedSpace.exp (leftAct (s • H) + rightAct ((-s) • H))) X =
        (NormedSpace.exp (leftAct (s • H)) * NormedSpace.exp (rightAct ((-s) • H))) X := happ
    _ = _ := by
      change NormedSpace.exp (leftAct (s • H)) (NormedSpace.exp (rightAct ((-s) • H)) X) = _
      rw [exp_leftAct_apply, exp_rightAct_apply]
      exact (mul_assoc _ _ _).symm

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SYKFastMix.FastMixing

lemma integrable_gaussian_power (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x^n) (gaussianReal 0 v) := by
  simpa only [id_eq] using integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal 0 v) (by simp [integrableExpSet_id_gaussianReal]) n

lemma gaussian_power_integral_nonneg (v : ℝ≥0) (n : ℕ) :
    0 ≤ ∫ x : ℝ, x^n ∂gaussianReal 0 v := by
  rcases Nat.even_or_odd n with he|ho
  · exact integral_nonneg (fun x ↦ he.pow_nonneg x)
  · have hh := integral_map (μ := gaussianReal 0 v) (φ := fun x : ℝ ↦ -x)
      (f := fun x : ℝ ↦ x^n) (by fun_prop) (by fun_prop)
    rw [gaussianReal_map_neg,neg_zero] at hh
    simp_rw [ho.neg_pow] at hh
    rw [integral_neg] at hh
    linarith

variable {N : ℕ}

def couplingMonomial (l : List (SYKEdge.KSet N 4)) (w : Disorder N) : ℝ :=
  ∏ A, (w A)^(l.count A)

lemma couplingMonomial_eq_list_prod (l : List (SYKEdge.KSet N 4)) (w : Disorder N) :
    couplingMonomial l w=(l.map w).prod := by
  induction l with
  | nil => simp [couplingMonomial]
  | cons A l ih =>
    rw [List.map_cons,List.prod_cons,← ih]
    unfold couplingMonomial
    have he (B : SYKEdge.KSet N 4) : w B^(List.count B (A::l))=
        (if A=B then w A else 1)*w B^(l.count B) := by
      by_cases h : A=B
      · subst B; simp [List.count_cons,pow_succ,mul_comm]
      · simp [List.count_cons,h,Ne.symm h]
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp

lemma integrable_couplingMonomial (Q : Model N) (l : List (SYKEdge.KSet N 4)) :
    Integrable (couplingMonomial l) (disorderLaw Q) := by
  exact Integrable.fintype_prod (fun A ↦ integrable_gaussian_power
    (Real.toNNReal (6*Q.J^2/(N : ℝ)^3)) (l.count A))

lemma couplingMonomial_integral_nonneg (Q : Model N) (l : List (SYKEdge.KSet N 4)) :
    0 ≤ ∫ w, couplingMonomial l w ∂disorderLaw Q := by
  unfold couplingMonomial disorderLaw
  rw [integral_fintype_prod_eq_prod (fun (A : SYKEdge.KSet N 4) (x : ℝ) ↦ x^(l.count A))]
  exact Finset.prod_nonneg (fun A hA ↦ gaussian_power_integral_nonneg _ _)

lemma couplingMonomial_nil (w : Disorder N) : couplingMonomial [] w=1 := by simp [couplingMonomial]

lemma couplingMonomial_cons (A : SYKEdge.KSet N 4) (l : List (SYKEdge.KSet N 4)) (w : Disorder N) :
    couplingMonomial (A::l) w=w A*couplingMonomial l w := by
  simp only [couplingMonomial_eq_list_prod,List.map_cons,List.prod_cons]

lemma couplingMonomial_append (l k : List (SYKEdge.KSet N 4)) (w : Disorder N) :
    couplingMonomial (l++k) w=couplingMonomial l w*couplingMonomial k w := by
  simp only [couplingMonomial_eq_list_prod,List.map_append,List.prod_append]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def realWord (l : List (Fin N)) (x : Fin N → ℝ) : ℝ := (l.map x).prod
def cliffordWord (Q : Model N) (l : List (Fin N)) : Mat (SiteHilbert N) := (l.map Q.γ).prod

def wordDifferential : List (Fin N) → (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] ℝ)
  | [], _ => 0
  | a::l, x => x a • wordDifferential l x+realWord l x • ContinuousLinearMap.proj a

lemma realWord_hasFDerivAt (l : List (Fin N)) (x : Fin N → ℝ) :
    HasFDerivAt (realWord l) (wordDifferential l x) x := by
  induction l with
  | nil =>
    change HasFDerivAt (fun _ : Fin N → ℝ ↦ (1 : ℝ)) 0 x
    exact hasFDerivAt_const (c := (1 : ℝ)) x
  | cons a l ih =>
    change HasFDerivAt (fun y : Fin N → ℝ ↦ y a*realWord l y)
      (x a • wordDifferential l x+realWord l x • ContinuousLinearMap.proj a) x
    convert! (hasFDerivAt_apply a x).mul ih using 1

lemma coordinateDerivative_realWord (l : List (Fin N)) (i : Fin N) (x : Fin N → ℝ) :
    coordinateDerivative (realWord l) i x=wordDifferential l x (Pi.single i 1) := by
  rw [coordinateDerivative,(realWord_hasFDerivAt l x).fderiv]

def realWordPartial (i : Fin N) : List (Fin N) → (Fin N → ℝ) → ℝ
  | [], _ => 0
  | a::l, x => (if a=i then realWord l x else 0)+x a*realWordPartial i l x

lemma wordDifferential_partial (l : List (Fin N)) (i : Fin N) (x : Fin N → ℝ) :
    wordDifferential l x (Pi.single i 1)=realWordPartial i l x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [wordDifferential,realWordPartial,_root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.proj_apply,smul_eq_mul,ih]
    by_cases h : a=i
    · subst a; simp [add_comm]
    · simp [Pi.single_apply,h,Ne.symm h]

structure WordDeletion (N : ℕ) where
  letter : Fin N
  position : ℕ
  remainder : List (Fin N)

def wordDeletions : List (Fin N) → List (WordDeletion N)
  | [] => []
  | a::l => ⟨a,0,l⟩::(wordDeletions l).map (fun d ↦ ⟨d.letter,d.position+1,a::d.remainder⟩)

lemma realWordPartial_deletions (l : List (Fin N)) (i : Fin N) (x : Fin N → ℝ) :
    realWordPartial i l x=((wordDeletions l).map
      (fun d ↦ if d.letter=i then realWord d.remainder x else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [realWordPartial,wordDeletions,List.map_cons,List.sum_cons,List.map_map,Function.comp_apply,realWord,List.map_cons,List.prod_cons]
    rw [ih]
    congr 1
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    by_cases h : d.letter=i <;> simp [h,realWord]

def cliffordWordPartial (Q : Model N) (i : Fin N) : List (Fin N) → Mat (SiteHilbert N)
  | [] => 0
  | a::l => (if a=i then cliffordWord Q l else 0)-Q.γ a*cliffordWordPartial Q i l

lemma cliffordWord_graded_derivative (Q : Model N) (i : Fin N) (l : List (Fin N)) :
    Q.γ i*cliffordWord Q l-(-1 : ℂ)^l.length • (cliffordWord Q l*Q.γ i)=
      (2 : ℂ) • cliffordWordPartial Q i l := by
  induction l with
  | nil => simp [cliffordWord,cliffordWordPartial]
  | cons a l ih =>
    have hcar : Q.γ i*Q.γ a+Q.γ a*Q.γ i=(if a=i then (2 : ℂ) • (1 : Mat (SiteHilbert N)) else 0) := by
      by_cases ha : a=i
      · subst a; rw [Q.car.sq]; simp; module
      · rw [Q.car.anticomm i a (Ne.symm ha)]; simp [ha]
    change Q.γ i*(Q.γ a*cliffordWord Q l)-(-1 : ℂ)^(l.length+1) •
      ((Q.γ a*cliffordWord Q l)*Q.γ i)=
        (2 : ℂ) • ((if a=i then cliffordWord Q l else 0)-Q.γ a*cliffordWordPartial Q i l)
    calc
      _=(Q.γ i*Q.γ a+Q.γ a*Q.γ i)*cliffordWord Q l-
          Q.γ a*(Q.γ i*cliffordWord Q l-(-1 : ℂ)^l.length • (cliffordWord Q l*Q.γ i)) := by
        rw [pow_succ]
        simp only [mul_neg_one,neg_smul,add_mul,mul_sub,mul_smul_comm,mul_assoc]
        module
      _=_ := by
        rw [hcar,ih]
        by_cases ha : a=i <;>
          simp only [ha,ite_true,ite_false,smul_mul_assoc,one_mul,zero_mul,mul_smul_comm,smul_sub] <;> module

lemma cliffordWordPartial_deletions (Q : Model N) (l : List (Fin N)) (i : Fin N) :
    cliffordWordPartial Q i l=((wordDeletions l).map
      (fun d ↦ if d.letter=i then (-1 : ℂ)^d.position • cliffordWord Q d.remainder else 0)).sum := by
  have htail (a : Fin N) (ds : List (WordDeletion N)) :
      (ds.map (fun d ↦ if d.letter=i then (-1 : ℂ)^(d.position+1) •
        (Q.γ a*cliffordWord Q d.remainder) else 0)).sum=
      -Q.γ a*(ds.map (fun d ↦ if d.letter=i then (-1 : ℂ)^d.position • cliffordWord Q d.remainder else 0)).sum := by
    induction ds with
    | nil => simp
    | cons d ds ih =>
      simp only [List.map_cons,List.sum_cons,ih,mul_add]
      by_cases h : d.letter=i <;>
        simp only [h,ite_true,ite_false,pow_succ,mul_neg_one,neg_smul,mul_smul_comm,mul_zero,zero_add] <;>
        noncomm_ring <;> module
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [cliffordWordPartial,wordDeletions,List.map_cons,List.sum_cons,List.map_map,
      Function.comp_apply,pow_zero,one_smul]
    rw [ih]
    have ht := htail a (wordDeletions l)
    change (if a=i then cliffordWord Q l else 0)-_=
      (if a=i then cliffordWord Q l else 0)+
        ((wordDeletions l).map (fun d ↦ if d.letter=i then (-1 : ℂ)^(d.position+1) •
          (Q.γ a*cliffordWord Q d.remainder) else 0)).sum
    rw [ht]
    simp only [neg_mul,sub_eq_add_neg]

lemma wordDeletion_length (l : List (Fin N)) (d : WordDeletion N) (hd : d∈wordDeletions l) :
    d.remainder.length+1=l.length := by
  induction l generalizing d with
  | nil => simp [wordDeletions] at hd
  | cons a l ih =>
    simp only [wordDeletions,List.mem_cons,List.mem_map] at hd
    rcases hd with rfl|⟨e,he,rfl⟩
    · rfl
    · have hh := ih e he
      simp only [List.length_cons]
      omega

lemma cliffordWord_norm (Q : Model N) (l : List (Fin N)) : ‖cliffordWord Q l‖=1 := by
  have hu : cliffordWord Q l∈unitary (Mat (SiteHilbert N)) := by
    unfold cliffordWord
    apply Submonoid.list_prod_mem
    intro X hX
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hX
    apply Unitary.mem_iff.mpr
    change (Q.γ i)ᴴ*Q.γ i=1 ∧ Q.γ i*(Q.γ i)ᴴ=1
    rw [(Q.car.herm i).eq]
    exact ⟨Q.car.sq i,Q.car.sq i⟩
  letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
  exact CStarRing.norm_coe_unitary ⟨cliffordWord Q l,hu⟩

lemma cliffordWord_odd_anticomm (Q : Model N) (i : Fin N) (l : List (Fin N)) (hl : Odd l.length) :
    (1/2 : ℂ) • anticomm (Q.γ i) (cliffordWord Q l)=cliffordWordPartial Q i l := by
  have he := cliffordWord_graded_derivative Q i l
  rw [hl.neg_one_pow] at he
  simp only [neg_one_smul,sub_neg_eq_add] at he
  unfold anticomm
  rw [he,smul_smul]
  norm_num

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

structure WordSlot (N : ℕ) where
  letter : Fin N
  before : List (Fin N)
  after : List (Fin N)

def wordSlots : List (Fin N) → List (WordSlot N)
  | [] => []
  | a::l => ⟨a,[],l⟩::(wordSlots l).map (fun s ↦ ⟨s.letter,a::s.before,s.after⟩)

def WordSlot.replace (s : WordSlot N) (l : List (Fin N)) := s.before++l++s.after

lemma realWord_append (a b : List (Fin N)) (x : Fin N → ℝ) :
    realWord (a++b) x=realWord a x*realWord b x := by
  simp [realWord]
lemma cliffordWord_append (Q : Model N) (a b : List (Fin N)) :
    cliffordWord Q (a++b)=cliffordWord Q a*cliffordWord Q b := by
  simp [cliffordWord]

lemma wordSlot_length (l : List (Fin N)) (s : WordSlot N) (hs : s∈wordSlots l) :
    s.before.length+1+s.after.length=l.length := by
  induction l generalizing s with
  | nil => simp [wordSlots] at hs
  | cons a l ih =>
    simp only [wordSlots,List.mem_cons,List.mem_map] at hs
    rcases hs with rfl|⟨t,ht,rfl⟩
    · simp [Nat.add_comm]
    · have he := ih t ht
      simp only [List.length_cons]
      omega

lemma realWordPartial_slots (l : List (Fin N)) (i : Fin N) (x : Fin N → ℝ) :
    realWordPartial i l x=((wordSlots l).map
      (fun s ↦ if s.letter=i then realWord (s.replace []) x else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [realWordPartial,wordSlots,List.map_cons,List.sum_cons,List.map_map,
      Function.comp_def,WordSlot.replace,List.nil_append,List.cons_append]
    rw [ih]
    congr 1
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    by_cases he : s.letter=i <;> simp [he,realWord,WordSlot.replace,mul_assoc]

lemma commutator_word_slots (Q : Model N) (H : Mat (SiteHilbert N)) (l : List (Fin N)) :
    cliffordWord Q l*H-H*cliffordWord Q l=
      ((wordSlots l).map (fun s ↦ cliffordWord Q s.before*
        (Q.γ s.letter*H-H*Q.γ s.letter)*cliffordWord Q s.after)).sum := by
  have hsum (a : Fin N) (ss : List (WordSlot N)) :
      (ss.map (fun s ↦ cliffordWord Q (a::s.before)*
        (Q.γ s.letter*H-H*Q.γ s.letter)*cliffordWord Q s.after)).sum=
      Q.γ a*(ss.map (fun s ↦ cliffordWord Q s.before*
        (Q.γ s.letter*H-H*Q.γ s.letter)*cliffordWord Q s.after)).sum := by
    induction ss with
    | nil => simp
    | cons s ss ih =>
      simp only [List.map_cons,List.sum_cons,ih,mul_add]
      congr 1
      change (Q.γ a*cliffordWord Q s.before)*_*_=Q.γ a*(cliffordWord Q s.before*_*_)
      simp only [mul_assoc]
  induction l with
  | nil => simp [cliffordWord,wordSlots]
  | cons a l ih =>
    simp only [wordSlots,List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
    rw [hsum,← ih]
    simp only [cliffordWord,List.map_nil,List.prod_nil,List.map_cons,List.prod_cons,one_mul]
    noncomm_ring

lemma realWord_generator_slots (w : Disorder N) (l : List (Fin N)) (x : Fin N → ℝ) :
    classicalGenerator w (realWord l) x=
      2*((wordSlots l).map (fun s ↦ coordinateDerivative (classicalG w) s.letter x*
        realWord (s.replace []) x)).sum := by
  unfold classicalGenerator
  simp_rw [coordinateDerivative_realWord,wordDifferential_partial,realWordPartial_slots]
  have hswap : (∑ i : Fin N, coordinateDerivative (classicalG w) i x*
      ((wordSlots l).map (fun s ↦ if s.letter=i then realWord (s.replace []) x else 0)).sum)=
      ((wordSlots l).map (fun s ↦ coordinateDerivative (classicalG w) s.letter x*
        realWord (s.replace []) x)).sum := by
    induction wordSlots l with
    | nil => simp
    | cons s ss ih =>
      simp only [List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib,ih]
      congr 1
      simp [mul_ite]
  rw [hswap]

lemma quarticWord_even (A : SYKEdge.KSet N 4) : Even (A.1.sort (· ≤ ·)).length := by
  simpa only [Finset.length_sort,A.2] using (show Even 4 by decide)

lemma majorana_hamiltonian_word_derivative (Q : Model N) (w : Disorder N) (i : Fin N) :
    Q.γ i*hamiltonian Q w-hamiltonian Q w*Q.γ i=
      (2 : ℂ) • ∑ A : SYKEdge.KSet N 4, (w A : ℂ) •
        cliffordWordPartial Q i (A.1.sort (· ≤ ·)) := by
  simp only [hamiltonian,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,
    smul_mul_assoc,← Finset.sum_sub_distrib,← smul_sub]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have he := cliffordWord_graded_derivative Q i (A.1.sort (· ≤ ·))
  rw [(quarticWord_even A).neg_one_pow] at he
  simp only [one_smul] at he
  change (w A : ℂ) • (Q.γ i*cliffordWord Q (A.1.sort (· ≤ ·))-
    cliffordWord Q (A.1.sort (· ≤ ·))*Q.γ i)=_
  rw [he,smul_comm]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma realWord_sort (A : Finset (Fin N)) (x : Fin N → ℝ) :
    realWord (A.sort (· ≤ ·)) x=∏ i∈A,x i := by
  unfold realWord
  rw [← List.prod_toFinset x (Finset.sort_nodup _ _)]
  simp

lemma classicalG_hasFDerivAt (w : Disorder N) (x : Fin N → ℝ) :
    HasFDerivAt (classicalG w)
      (∑ A : SYKEdge.KSet N 4, w A • wordDifferential (A.1.sort (· ≤ ·)) x) x := by
  have he : classicalG w=∑ A : SYKEdge.KSet N 4,
      fun y ↦ w A*realWord (A.1.sort (· ≤ ·)) y := by
    funext y
    simp [classicalG,realWord_sort]
  rw [he]
  apply HasFDerivAt.sum
  intro A hA
  exact (realWord_hasFDerivAt _ x).const_mul (w A)

lemma classicalG_derivative_words (w : Disorder N) (i : Fin N) (x : Fin N → ℝ) :
    coordinateDerivative (classicalG w) i x=
      ∑ A : SYKEdge.KSet N 4, w A*realWordPartial i (A.1.sort (· ≤ ·)) x := by
  rw [coordinateDerivative,(classicalG_hasFDerivAt w x).fderiv]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    wordDifferential_partial]

lemma hasFDerivAt_list_words {α : Type} (l : List α) (c : α → ℝ) (word : α → List (Fin N))
    (x : Fin N → ℝ) :
    HasFDerivAt (fun y ↦ (l.map (fun a ↦ c a*realWord (word a) y)).sum)
      (l.map (fun a ↦ c a • wordDifferential (word a) x)).sum x := by
  induction l with
  | nil => simpa using hasFDerivAt_const (c := (0 : ℝ)) x
  | cons a l ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      ((realWord_hasFDerivAt (word a) x).const_mul (c a)).add ih

lemma derivative_list_words {α : Type} (l : List α) (c : α → ℝ) (word : α → List (Fin N))
    (i : Fin N) (x : Fin N → ℝ) :
    coordinateDerivative (fun y ↦ (l.map (fun a ↦ c a*realWord (word a) y)).sum) i x=
      (l.map (fun a ↦ c a*realWordPartial i (word a) x)).sum := by
  rw [coordinateDerivative,(hasFDerivAt_list_words l c word x).fderiv]
  have hh : ∀ k : List α,
      (k.map (fun a ↦ c a • wordDifferential (word a) x)).sum (Pi.single i 1)=
      (k.map (fun a ↦ c a*realWordPartial i (word a) x)).sum := by
    intro k
    induction k with
    | nil => simp
    | cons a k ih =>
      simp only [List.map_cons,List.sum_cons,_root_.add_apply,_root_.smul_apply,
        smul_eq_mul,wordDifferential_partial,ih]
  exact hh l

lemma generator_list_words {α : Type} (w : Disorder N) (l : List α)
    (c : α → ℝ) (word : α → List (Fin N)) (x : Fin N → ℝ) :
    classicalGenerator w (fun y ↦ (l.map (fun a ↦ c a*realWord (word a) y)).sum) x=
      (l.map (fun a ↦ c a*classicalGenerator w (realWord (word a)) x)).sum := by
  simp only [classicalGenerator,derivative_list_words]
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib] at *
    rw [← ih]
    congr 1
    simp only [coordinateDerivative_realWord,wordDifferential_partial]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma list_sum_flatMap {α β M : Type} [AddMonoid M] (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum=(l.map (fun a ↦ ((f a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

lemma all_list_sum {α M : Type} [Fintype α] [DecidableEq α] [AddCommMonoid M] (f : α → M) :
    ((Finset.univ.toList).map f).sum=∑ a,f a := by
  rw [← List.sum_toFinset f (Finset.nodup_toList _)]
  simp

structure InteractionPath (N : ℕ) where
  couplings : List (SYKEdge.KSet N 4)
  word : List (Fin N)
  sign : ℝ

def InteractionPath.step (t : InteractionPath N) : List (InteractionPath N) :=
  (wordSlots t.word).flatMap (fun s ↦ (Finset.univ.toList : List (SYKEdge.KSet N 4)).flatMap
    (fun A ↦ ((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
      (fun d ↦ ⟨A::t.couplings,s.replace d.remainder,t.sign*(-1)^d.position⟩)))

def interactionPaths (j : Fin N) : ℕ → List (InteractionPath N)
  | 0 => [⟨[],[j],1⟩]
  | m+1 => (interactionPaths j m).flatMap InteractionPath.step

lemma interactionPath_lengths (j : Fin N) (m : ℕ) (t : InteractionPath N)
    (ht : t∈interactionPaths j m) : t.couplings.length=m ∧ t.word.length=2*m+1 ∧ |t.sign|=1 := by
  induction m generalizing t with
  | zero =>
    simp only [interactionPaths,List.mem_singleton] at ht
    subst t
    simp
  | succ m ih =>
    simp only [interactionPaths,List.mem_flatMap] at ht
    obtain ⟨u,hu,ht⟩ := ht
    rcases ih u hu with ⟨huc,huw,hus⟩
    simp only [InteractionPath.step,List.mem_flatMap,List.mem_map,List.mem_filter] at ht
    obtain ⟨s,hs,A,hA,d,⟨hd,hdi⟩,rfl⟩ := ht
    have hslot := wordSlot_length u.word s hs
    have hdel := wordDeletion_length (A.1.sort (· ≤ ·)) d hd
    rw [Finset.length_sort,A.2] at hdel
    simp only [List.length_cons,huc,WordSlot.replace,List.length_append,abs_mul,abs_pow,abs_neg,abs_one,
      one_pow,hus,mul_one]
    constructor
    · trivial
    constructor
    · omega
    · trivial

lemma wordDeletions_filter_sum {M : Type} [AddCommMonoid M] (l : List (Fin N))
    (i : Fin N) (f : WordDeletion N → M) :
    (((wordDeletions l).filter (fun d ↦ d.letter=i)).map f).sum=
      ((wordDeletions l).map (fun d ↦ if d.letter=i then f d else 0)).sum := by
  have hh : ∀ ds : List (WordDeletion N),
      ((ds.filter (fun d ↦ d.letter=i)).map f).sum=
      (ds.map (fun d ↦ if d.letter=i then f d else 0)).sum := by
    intro ds
    induction ds with
    | nil => rfl
    | cons d ds ih => by_cases he : d.letter=i <;> simp [he,ih]
  exact hh _

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma list_sum_smul_left {α K M : Type} [Semiring K] [AddCommMonoid M] [Module K M]
    (l : List α) (c : K) (f : α → M) :
    (l.map (fun a ↦ c • f a)).sum=c • (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih,smul_add]

lemma word_slot_quantum_children (Q : Model N) (w : Disorder N) (s : WordSlot N) :
    (∑ A : SYKEdge.KSet N 4, (w A : ℂ) •
      (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
        (fun d ↦ (-1 : ℂ)^d.position • cliffordWord Q (s.replace d.remainder))).sum)=
    (1/2 : ℂ) • (cliffordWord Q s.before*
      (Q.γ s.letter*hamiltonian Q w-hamiltonian Q w*Q.γ s.letter)*cliffordWord Q s.after) := by
  rw [majorana_hamiltonian_word_derivative]
  simp only [mul_smul_comm,smul_mul_assoc,smul_smul]
  norm_num
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  rw [cliffordWordPartial_deletions,wordDeletions_filter_sum]
  rw [← List.sum_map_mul_left,← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  by_cases he : d.letter=s.letter
  · simp only [he,ite_true,WordSlot.replace,cliffordWord_append,mul_smul_comm,smul_mul_assoc]
  · simp only [he,ite_false,mul_zero,zero_mul]

namespace InteractionPath
variable (t : InteractionPath N)
def qeval (Q : Model N) (w : Disorder N) :=
  ((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) • cliffordWord Q t.word

def reval (w : Disorder N) (x : Fin N → ℝ) :=
  couplingMonomial t.couplings w*realWord t.word x

lemma qeval_step (Q : Model N) (w : Disorder N) :
    (t.step.map (fun u ↦ u.qeval Q w)).sum=
      (1/2 : ℂ) • (t.qeval Q w*hamiltonian Q w-hamiltonian Q w*t.qeval Q w) := by
  unfold step
  simp only [list_sum_flatMap,List.map_map,Function.comp_def,qeval,couplingMonomial_cons,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  have hterm (s : WordSlot N) (A : SYKEdge.KSet N 4) :
      (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
        (fun d ↦ ((t.sign : ℂ)*(-1 : ℂ)^d.position*((w A : ℂ)*
          (couplingMonomial t.couplings w : ℂ))) • cliffordWord Q (s.replace d.remainder))).sum=
      ((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) • ((w A : ℂ) •
        ((((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
          (fun d ↦ (-1 : ℂ)^d.position • cliffordWord Q (s.replace d.remainder))).sum)) := by
    rw [← list_sum_smul_left,← list_sum_smul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    simp only [smul_smul,Complex.ofReal_mul]
    congr 1
    ring
  simp_rw [hterm]
  simp only [list_sum_smul_left]
  simp_rw [all_list_sum]
  rw [← list_sum_smul_left]
  simp_rw [word_slot_quantum_children]
  simp only [list_sum_smul_left]
  rw [← commutator_word_slots]
  simp only [qeval,Complex.ofReal_mul,smul_mul_assoc,mul_smul_comm,← smul_sub,smul_smul]
  congr 1
  ring
end InteractionPath

lemma quantum_paths_recur (Q : Model N) (w : Disorder N) (j : Fin N) (m : ℕ) :
    ((interactionPaths j (m+1)).map (fun t ↦ t.qeval Q w)).sum=
      (1/2 : ℂ) • ((((interactionPaths j m).map (fun t ↦ t.qeval Q w)).sum)*hamiltonian Q w-
        hamiltonian Q w*((interactionPaths j m).map (fun t ↦ t.qeval Q w)).sum) := by
  simp only [interactionPaths,list_sum_flatMap,InteractionPath.qeval_step,list_sum_smul_left]
  congr 1
  induction interactionPaths j m with
  | nil => simp
  | cons t l ih => simp only [List.map_cons,List.sum_cons,add_mul,mul_add] at *; rw [ih]; module

lemma quantum_ad_paths (Q : Model N) (w : Disorder N) (j : Fin N) (m : ℕ) :
    (-1 : ℂ)^m • applySuper ((ad (hamiltonian Q w))^m) (Q.γ j)=
      (2 : ℂ)^m • ((interactionPaths j m).map (fun t ↦ t.qeval Q w)).sum := by
  induction m with
  | zero =>
    simp only [pow_zero,one_smul,interactionPaths,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,InteractionPath.qeval,couplingMonomial_nil,mul_one,Complex.ofReal_one]
    have he : applySuper (1 : Super (SiteHilbert N)) (Q.γ j)=Q.γ j := by
      ext a b
      simp [applySuper,Matrix.one_apply]
    rw [he]
    simp [cliffordWord]
  | succ m ih =>
    rw [pow_succ' (ad (hamiltonian Q w)),applySuper_mul]
    have had (X : Mat (SiteHilbert N)) :
        applySuper (ad (hamiltonian Q w)) X=hamiltonian Q w*X-X*hamiltonian Q w :=
      applySuper_super (leftAct (hamiltonian Q w)-rightAct (hamiltonian Q w)).toLinearMap X
    rw [had,quantum_paths_recur]
    calc
      _=-(hamiltonian Q w*((-1 : ℂ)^m • applySuper ((ad (hamiltonian Q w))^m) (Q.γ j))-
          ((-1 : ℂ)^m • applySuper ((ad (hamiltonian Q w))^m) (Q.γ j))*hamiltonian Q w) := by
        rw [pow_succ]
        simp only [mul_neg_one,neg_smul,mul_smul_comm,smul_mul_assoc,smul_sub]
        module
      _=_ := by
        rw [ih,pow_succ]
        simp only [mul_smul_comm,smul_mul_assoc,smul_sub,smul_smul]
        have hc : (2 : ℂ)^m*2*(1/2)=(2 : ℂ)^m := by ring
        rw [hc]
        module

lemma gammaCoefficient_paths (Q : Model N) (w : Disorder N) (j : Fin N) (m : ℕ) :
    gammaCoefficient Q w m j=((2 : ℂ)^m/(m.factorial : ℂ)) •
      ((interactionPaths j m).map (fun t ↦ t.qeval Q w)).sum := by
  unfold gammaCoefficient
  calc
    _=(m.factorial : ℂ)⁻¹ • ((-1 : ℂ)^m • applySuper ((ad (hamiltonian Q w))^m) (Q.γ j)) := by
      rw [smul_smul]
      congr 1
      rw [div_eq_mul_inv,mul_comm]
    _=_ := by
      rw [quantum_ad_paths,smul_smul]
      congr 1
      rw [div_eq_mul_inv,mul_comm]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma word_slot_classical_children (w : Disorder N) (s : WordSlot N) (x : Fin N → ℝ) :
    (∑ A : SYKEdge.KSet N 4, w A*
      (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
        (fun d ↦ realWord (s.replace d.remainder) x)).sum)=
      coordinateDerivative (classicalG w) s.letter x*realWord (s.replace []) x := by
  rw [classicalG_derivative_words,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  rw [realWordPartial_deletions,wordDeletions_filter_sum,mul_assoc]
  congr 1
  rw [← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  by_cases he : d.letter=s.letter
  · simp only [he,ite_true,WordSlot.replace,realWord_append]
    simp [realWord]
    ring
  · simp only [he,ite_false,zero_mul]

namespace InteractionPath
variable (t : InteractionPath N)
lemma reval_step (w : Disorder N) (x : Fin N → ℝ) :
    2*(t.step.map (fun u ↦ u.reval w x)).sum=
      couplingMonomial t.couplings w*classicalGenerator w (realWord t.word) x := by
  unfold step
  simp only [list_sum_flatMap,List.map_map,Function.comp_def,reval,couplingMonomial_cons]
  have hterm (s : WordSlot N) (A : SYKEdge.KSet N 4) :
      (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
        (fun d ↦ (w A*couplingMonomial t.couplings w)*realWord (s.replace d.remainder) x)).sum=
      couplingMonomial t.couplings w*(w A*
        (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
          (fun d ↦ realWord (s.replace d.remainder) x)).sum) := by
    rw [← List.sum_map_mul_left,← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    ring
  simp_rw [hterm]
  simp only [List.sum_map_mul_left]
  simp_rw [all_list_sum,word_slot_classical_children]
  rw [realWord_generator_slots]
  ring
end InteractionPath

lemma classicalIterate_paths (w : Disorder N) (j : Fin N) (m : ℕ) (x : Fin N → ℝ) :
    classicalIterate w m j x=(2 : ℝ)^m*((interactionPaths j m).map (fun t ↦ t.reval w x)).sum := by
  induction m generalizing x with
  | zero => simp [classicalIterate,interactionPaths,InteractionPath.reval,couplingMonomial_nil,realWord]
  | succ m ih =>
    have he : classicalIterate w m j=fun y ↦ (2 : ℝ)^m*
        ((interactionPaths j m).map (fun t ↦ couplingMonomial t.couplings w*realWord t.word y)).sum := by
      funext y
      exact ih y
    have hrecur : classicalIterate w (m+1) j=classicalGenerator w (classicalIterate w m j) := by
      unfold classicalIterate
      rw [Function.iterate_succ_apply']
    rw [hrecur,he]
    have hscaled : (fun y ↦ (2 : ℝ)^m*
        ((interactionPaths j m).map (fun t ↦ couplingMonomial t.couplings w*realWord t.word y)).sum)=
        fun y ↦ ((interactionPaths j m).map (fun t ↦ ((2 : ℝ)^m*couplingMonomial t.couplings w)*realWord t.word y)).sum := by
      funext y
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      ring
    rw [hscaled,generator_list_words]
    simp only [interactionPaths,list_sum_flatMap,← InteractionPath.reval_step]
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    rw [mul_assoc,← InteractionPath.reval_step,pow_succ]
    ring

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] [Nonempty ι]

def BlockDominated (A : Mat (I×ι)) (B : Matrix I I ℝ) : Prop :=
  ∀ i j, ‖subblock A i j‖ ≤ B i j

lemma subblock_mul (A C : Mat (I×ι)) (i j : I) :
    subblock (A*C) i j=∑ k, subblock A i k*subblock C k j := by
  ext a b
  simp only [subblock,Matrix.of_apply,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.sum_apply]

lemma subblock_conjTranspose (A : Mat (I×ι)) (i j : I) :
    subblock Aᴴ i j=(subblock A j i)ᴴ := by rfl

lemma blockDominated_mul {A C : Mat (I×ι)} {B D : Matrix I I ℝ}
    (hAB : BlockDominated A B) (hCD : BlockDominated C D) :
    BlockDominated (A*C) (B*D) := by
  intro i j
  rw [subblock_mul]
  calc
    _ ≤ ∑ k, ‖subblock A i k*subblock C k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, B i k*D k j := by
      apply Finset.sum_le_sum
      intro k hk
      exact (norm_mul_le _ _).trans (mul_le_mul (hAB i k) (hCD k j)
        (norm_nonneg _) ((norm_nonneg _).trans (hAB i k)))
    _ = _ := rfl

lemma blockDominated_conjTranspose {A : Mat (I×ι)} {B : Matrix I I ℝ}
    (hAB : BlockDominated A B) : BlockDominated Aᴴ B.transpose := by
  intro i j
  rw [subblock_conjTranspose,Matrix.l2_opNorm_conjTranspose]
  exact hAB j i

lemma blockDominated_zero : BlockDominated (0 : Mat (I×ι)) (0 : Matrix I I ℝ) := by
  intro i j
  have he : subblock (0 : Mat (I×ι)) i j=0 := rfl
  rw [he,norm_zero]
  rfl

lemma blockDominated_one : BlockDominated (1 : Mat (I×ι)) (1 : Matrix I I ℝ) := by
  intro i j
  by_cases hij : i=j
  · subst j
    have he : subblock (1 : Mat (I×ι)) i i=1 := by
      ext a b
      simp [subblock,Matrix.one_apply]
    rw [he,Matrix.one_apply_eq]
    exact le_of_eq norm_one
  · have he : subblock (1 : Mat (I×ι)) i j=0 := by
      ext a b
      simp [subblock,Matrix.one_apply,hij]
    rw [he,norm_zero,Matrix.one_apply_ne hij]

lemma blockDominated_pow {A : Mat (I×ι)} {B : Matrix I I ℝ}
    (hAB : BlockDominated A B) (p : ℕ) : BlockDominated (A^p) (B^p) := by
  induction p with
  | zero => simpa using (blockDominated_one (I := I) (ι := ι))
  | succ p ih => simpa only [pow_succ] using blockDominated_mul ih hAB

lemma blockDominated_trace {A : Mat (I×ι)} {B : Matrix I I ℝ}
    (hAB : BlockDominated A B) :
    (Matrix.trace A).re ≤ (Fintype.card ι : ℝ)*Matrix.trace B := by
  simp only [Matrix.trace,Matrix.diag,Fintype.sum_prod_type,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ ∑ a : ι, ‖A (i,a) (i,a)‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact Complex.re_le_norm _
    _ ≤ ∑ a : ι, B i i := by
      apply Finset.sum_le_sum
      intro a ha
      exact (matrix_entry_norm_le (subblock A i i) a a).trans (hAB i i)
    _ = _ := by simp

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ} {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] [Nonempty ι]

structure GaussianBlockTerm (N : ℕ) (I ι : Type) [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] where
  monomial : List (SYKEdge.KSet N 4)
  quantum : Mat (I×ι)
  classical : Matrix I I ℝ
  dominated : BlockDominated quantum classical

namespace GaussianBlockTerm
variable (t u : GaussianBlockTerm N I ι)
def qeval (w : Disorder N) := couplingMonomial t.monomial w • t.quantum
def reval (w : Disorder N) := couplingMonomial t.monomial w • t.classical

def mul : GaussianBlockTerm N I ι :=
  ⟨t.monomial++u.monomial,t.quantum*u.quantum,t.classical*u.classical,
    blockDominated_mul t.dominated u.dominated⟩
def adjoint : GaussianBlockTerm N I ι :=
  ⟨t.monomial,t.quantumᴴ,t.classical.transpose,blockDominated_conjTranspose t.dominated⟩
def one : GaussianBlockTerm N I ι := ⟨[],1,1,blockDominated_one⟩

lemma qeval_mul (w : Disorder N) : (t.mul u).qeval w=t.qeval w*u.qeval w := by
  simp only [qeval,mul,couplingMonomial_append,smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm]
lemma reval_mul (w : Disorder N) : (t.mul u).reval w=t.reval w*u.reval w := by
  simp only [reval,mul,couplingMonomial_append,smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm]
lemma qeval_adjoint (w : Disorder N) : t.adjoint.qeval w=(t.qeval w)ᴴ := by
  simp only [qeval,adjoint,Matrix.conjTranspose_smul,star_trivial]
lemma reval_adjoint (w : Disorder N) : t.adjoint.reval w=(t.reval w).transpose := by
  simp only [reval,adjoint,Matrix.transpose_smul]
lemma qeval_one (w : Disorder N) : (one : GaussianBlockTerm N I ι).qeval w=1 := by
  simp [qeval,one,couplingMonomial_nil]
lemma reval_one (w : Disorder N) : (one : GaussianBlockTerm N I ι).reval w=1 := by
  simp [reval,one,couplingMonomial_nil]

lemma integrable_qtrace (Q : Model N) :
    Integrable (fun w ↦ (Matrix.trace (t.qeval w)).re) (disorderLaw Q) := by
  have he : (fun w ↦ (Matrix.trace (t.qeval w)).re)=
      fun w ↦ couplingMonomial t.monomial w*(Matrix.trace t.quantum).re := by
    funext w
    simp [qeval,Matrix.trace_smul]
  rw [he]
  exact (integrable_couplingMonomial Q t.monomial).mul_const _
lemma integrable_rtrace (Q : Model N) :
    Integrable (fun w ↦ Matrix.trace (t.reval w)) (disorderLaw Q) := by
  have he : (fun w ↦ Matrix.trace (t.reval w))=
      fun w ↦ couplingMonomial t.monomial w*Matrix.trace t.classical := by
    funext w
    simp [reval,Matrix.trace_smul]
  rw [he]
  exact (integrable_couplingMonomial Q t.monomial).mul_const _

lemma integral_trace_le (Q : Model N) :
    (∫ w, (Matrix.trace (t.qeval w)).re ∂disorderLaw Q) ≤
      (Fintype.card ι : ℝ)*∫ w, Matrix.trace (t.reval w) ∂disorderLaw Q := by
  have hq (w : Disorder N) : (Matrix.trace (t.qeval w)).re=
      couplingMonomial t.monomial w*(Matrix.trace t.quantum).re := by
    simp [qeval,Matrix.trace_smul]
  have hr (w : Disorder N) : Matrix.trace (t.reval w)=
      couplingMonomial t.monomial w*Matrix.trace t.classical := by
    simp [reval,Matrix.trace_smul]
  simp_rw [hq,hr]
  rw [integral_mul_const,integral_mul_const]
  have hh := mul_le_mul_of_nonneg_left (blockDominated_trace t.dominated)
    (couplingMonomial_integral_nonneg Q t.monomial)
  calc
    _ ≤ (∫ w, couplingMonomial t.monomial w ∂disorderLaw Q)*
        ((Fintype.card ι : ℝ)*Matrix.trace t.classical) := hh
    _ = _ := by ring
end GaussianBlockTerm

namespace GaussianBlockPolynomial
abbrev Poly (N : ℕ) (I ι : Type) [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] := List (GaussianBlockTerm N I ι)

def qeval (l : Poly N I ι) (w : Disorder N) := (l.map (fun t ↦ t.qeval w)).sum
def reval (l : Poly N I ι) (w : Disorder N) := (l.map (fun t ↦ t.reval w)).sum

def mul (l k : Poly N I ι) : Poly N I ι := l.flatMap (fun t ↦ k.map t.mul)
def adjoint (l : Poly N I ι) : Poly N I ι := l.map GaussianBlockTerm.adjoint
def one : Poly N I ι := [GaussianBlockTerm.one]
def pow (l : Poly N I ι) : ℕ → Poly N I ι
  | 0 => one
  | p+1 => mul (pow l p) l

lemma qeval_mul (l k : Poly N I ι) (w : Disorder N) :
    qeval (mul l k) w=qeval l w*qeval k w := by
  induction l with
  | nil => simp [mul,qeval]
  | cons t l ih =>
    simp only [mul,List.flatMap_cons,qeval,List.map_append,List.sum_append,List.map_cons,List.sum_cons,add_mul] at *
    rw [ih]
    congr 1
    simp only [List.map_map,Function.comp_def,GaussianBlockTerm.qeval_mul]
    exact List.sum_map_mul_left _ _ _

lemma reval_mul (l k : Poly N I ι) (w : Disorder N) :
    reval (mul l k) w=reval l w*reval k w := by
  induction l with
  | nil => simp [mul,reval]
  | cons t l ih =>
    simp only [mul,List.flatMap_cons,reval,List.map_append,List.sum_append,List.map_cons,List.sum_cons,add_mul] at *
    rw [ih]
    congr 1
    simp only [List.map_map,Function.comp_def,GaussianBlockTerm.reval_mul]
    exact List.sum_map_mul_left _ _ _

lemma qeval_adjoint (l : Poly N I ι) (w : Disorder N) :
    qeval (adjoint l) w=(qeval l w)ᴴ := by
  induction l with
  | nil => simp [adjoint,qeval]
  | cons t l ih =>
    simp only [adjoint,List.map_cons,qeval,List.map_cons,List.sum_cons,Matrix.conjTranspose_add] at *
    rw [GaussianBlockTerm.qeval_adjoint,ih]
lemma reval_adjoint (l : Poly N I ι) (w : Disorder N) :
    reval (adjoint l) w=(reval l w).transpose := by
  induction l with
  | nil => simp [adjoint,reval]
  | cons t l ih =>
    simp only [adjoint,List.map_cons,reval,List.map_cons,List.sum_cons,Matrix.transpose_add] at *
    rw [GaussianBlockTerm.reval_adjoint,ih]
lemma qeval_pow (l : Poly N I ι) (p : ℕ) (w : Disorder N) :
    qeval (pow l p) w=(qeval l w)^p := by
  induction p with
  | zero => simp [pow,one,qeval,GaussianBlockTerm.qeval_one]
  | succ p ih => rw [pow,qeval_mul,ih,pow_succ]
lemma reval_pow (l : Poly N I ι) (p : ℕ) (w : Disorder N) :
    reval (pow l p) w=(reval l w)^p := by
  induction p with
  | zero => simp [pow,one,reval,GaussianBlockTerm.reval_one]
  | succ p ih => rw [pow,reval_mul,ih,pow_succ]

lemma integrable_qtrace (Q : Model N) (l : Poly N I ι) :
    Integrable (fun w ↦ (Matrix.trace (qeval l w)).re) (disorderLaw Q) := by
  induction l with
  | nil => simp only [qeval,List.map_nil,List.sum_nil,Matrix.trace_zero,Complex.zero_re]; exact integrable_zero (Disorder N) ℝ (disorderLaw Q)
  | cons t l ih =>
    simpa only [qeval,List.map_cons,List.sum_cons,Matrix.trace_add,Complex.add_re] using!
      (t.integrable_qtrace Q).add ih

lemma integrable_rtrace (Q : Model N) (l : Poly N I ι) :
    Integrable (fun w ↦ Matrix.trace (reval l w)) (disorderLaw Q) := by
  induction l with
  | nil => simp only [reval,List.map_nil,List.sum_nil,Matrix.trace_zero]; exact integrable_zero (Disorder N) ℝ (disorderLaw Q)
  | cons t l ih =>
    simpa only [reval,List.map_cons,List.sum_cons,Matrix.trace_add] using!
      (t.integrable_rtrace Q).add ih

lemma integral_trace_le (Q : Model N) (l : Poly N I ι) :
    (∫ w, (Matrix.trace (qeval l w)).re ∂disorderLaw Q) ≤
      (Fintype.card ι : ℝ)*∫ w, Matrix.trace (reval l w) ∂disorderLaw Q := by
  induction l with
  | nil => simp [qeval,reval]
  | cons t l ih =>
    simp only [qeval,reval,List.map_cons,List.sum_cons,Matrix.trace_add,Complex.add_re]
    change (∫ w, (Matrix.trace (t.qeval w)).re+(Matrix.trace (qeval l w)).re ∂disorderLaw Q) ≤
      (Fintype.card ι : ℝ)*∫ w, Matrix.trace (t.reval w)+Matrix.trace (reval l w) ∂disorderLaw Q
    rw [integral_add (t.integrable_qtrace Q) (integrable_qtrace Q l),
      integral_add (t.integrable_rtrace Q) (integrable_rtrace Q l),mul_add]
    exact add_le_add (t.integral_trace_le Q) ih

lemma moment_comparison (Q : Model N) (l : Poly N I ι) (p : ℕ) :
    Integrable (fun w ↦ traceMoment p (qeval l w)) (disorderLaw Q) ∧
    Integrable (fun w ↦ Matrix.trace (((reval l w).transpose*reval l w)^p)) (disorderLaw Q) ∧
    (∫ w, traceMoment p (qeval l w) ∂disorderLaw Q) ≤ (Fintype.card ι : ℝ)*
      ∫ w, Matrix.trace (((reval l w).transpose*reval l w)^p) ∂disorderLaw Q := by
  let k := pow (mul (adjoint l) l) p
  have hq (w : Disorder N) : qeval k w=((qeval l w)ᴴ*qeval l w)^p := by
    simp only [k,qeval_pow,qeval_mul,qeval_adjoint]
  have hr (w : Disorder N) : reval k w=((reval l w).transpose*reval l w)^p := by
    simp only [k,reval_pow,reval_mul,reval_adjoint]
  have hiq := integrable_qtrace Q k
  have hir := integrable_rtrace Q k
  have hc := integral_trace_le Q k
  simp only [hq,hr] at hiq hir hc
  exact ⟨hiq,hir,hc⟩

end GaussianBlockPolynomial
end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] [Nonempty ι]

lemma subblock_single_kronecker (i j a b : I) (W : Mat ι) :
    subblock (Matrix.kronecker (Matrix.single i j (1 : ℂ)) W) a b=
      if a=i ∧ b=j then W else 0 := by
  ext x y
  by_cases hai : a=i <;> by_cases hbj : b=j <;>
    simp [subblock,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.single_apply,hai,hbj,
      Ne.symm,eq_comm] <;> aesop

lemma blockDominated_single_kronecker (i j : I) (W : Mat ι) (c : ℝ) (hc : ‖W‖≤c) :
    BlockDominated (Matrix.kronecker (Matrix.single i j (1 : ℂ)) W) (Matrix.single i j c) := by
  intro a b
  rw [subblock_single_kronecker]
  by_cases he : a=i ∧ b=j
  · simp only [he,ite_true]
    simpa [Matrix.single_apply,he.1,he.2] using hc
  · by_cases hai : a=i <;> by_cases hbj : b=j <;> simp_all [Matrix.single_apply,eq_comm]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma coefficient_scale_nonneg (m : ℕ) : 0 ≤ (2 : ℝ)^m/(m.factorial : ℝ) := by positivity

lemma path_block_norm (Q : Model N) (m : ℕ) (t : InteractionPath N) (d : WordDeletion N) :
    ‖(((2 : ℝ)^m/(m.factorial : ℝ)*t.sign : ℝ) : ℂ) •
      ((-1 : ℂ)^d.position • cliffordWord Q d.remainder)‖=
      ((2 : ℝ)^m/(m.factorial : ℝ))*|t.sign| := by
  rw [norm_smul,norm_smul,cliffordWord_norm,Complex.norm_real,norm_mul,
    Real.norm_eq_abs,abs_of_nonneg (coefficient_scale_nonneg m),norm_pow]
  norm_num

def fermionPathTerm (Q : Model N) (m : ℕ) (j : Fin N) (t : InteractionPath N)
    (d : WordDeletion N) : GaussianBlockTerm N (Fin N) (SiteHilbert N) :=
  ⟨t.couplings,
    Matrix.kronecker (Matrix.single j d.letter (1 : ℂ))
      ((((2 : ℝ)^m/(m.factorial : ℝ)*t.sign : ℝ) : ℂ) •
        ((-1 : ℂ)^d.position • cliffordWord Q d.remainder)),
    Matrix.single j d.letter (((2 : ℝ)^m/(m.factorial : ℝ))*|t.sign|),
    by
      letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
      exact blockDominated_single_kronecker _ _ _ _ (le_of_eq (path_block_norm Q m t d))⟩

def fermionPathPolynomial (Q : Model N) (m : ℕ) :
    GaussianBlockPolynomial.Poly N (Fin N) (SiteHilbert N) :=
  (Finset.univ.toList : List (Fin N)).flatMap (fun j ↦
    (interactionPaths j m).flatMap (fun t ↦ (wordDeletions t.word).map (fermionPathTerm Q m j t)))

lemma realWord_ones (l : List (Fin N)) : realWord l (fun _ ↦ 1)=1 := by simp [realWord]

lemma classicalCoefficient_paths (w : Disorder N) (m : ℕ) (j i : Fin N) :
    (classicalCoefficient w m 1) j i=
      (((2 : ℝ)^m/(m.factorial : ℝ))*
        ((interactionPaths j m).map (fun t ↦ couplingMonomial t.couplings w*
          ((wordDeletions t.word).map (fun d ↦ if d.letter=i then (1 : ℝ) else 0)).sum)).sum : ℝ) := by
  have he : classicalIterate w m j=fun y ↦
      ((interactionPaths j m).map (fun t ↦ ((2 : ℝ)^m*couplingMonomial t.couplings w)*realWord t.word y)).sum := by
    funext y
    rw [classicalIterate_paths,← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    simp only [InteractionPath.reval]
    ring
  unfold classicalCoefficient
  rw [he,derivative_list_words]
  simp only [realWordPartial_deletions]
  have hone (l : List (Fin N)) : realWord l (1 : Fin N → ℝ)=1 := by
    change (l.map (fun _ ↦ (1 : ℝ))).prod=1
    simp
  simp_rw [hone]
  have hs : ((interactionPaths j m).map (fun a ↦ (2 : ℝ)^m*couplingMonomial a.couplings w*
        ((wordDeletions a.word).map (fun d ↦ if d.letter=i then (1 : ℝ) else 0)).sum)).sum=
      (2 : ℝ)^m*((interactionPaths j m).map (fun a ↦ couplingMonomial a.couplings w*
        ((wordDeletions a.word).map (fun d ↦ if d.letter=i then (1 : ℝ) else 0)).sum)).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    ring
  rw [hs]
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]
  ring

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma half_anticomm_smul {ι : Type} [Fintype ι] (X Y : Mat ι) (c : ℂ) :
    (1/2 : ℂ) • anticomm X (c • Y)=c • ((1/2 : ℂ) • anticomm X Y) := by
  simp only [anticomm,mul_smul_comm,smul_mul_assoc,← smul_add,smul_smul]
  congr 1
  ring
lemma half_anticomm_list {ι α : Type} [Fintype ι] (X : Mat ι) (l : List α) (f : α → Mat ι) :
    (1/2 : ℂ) • anticomm X (l.map f).sum=
      (l.map (fun a ↦ (1/2 : ℂ) • anticomm X (f a))).sum := by
  induction l with
  | nil => simp [anticomm]
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,anticomm,mul_add,add_mul,smul_add] at *
    rw [← ih]
    module

lemma fermionCoefficient_paths_block (Q : Model N) (w : Disorder N) (m : ℕ) (j i : Fin N) :
    (1/2 : ℂ) • anticomm (Q.γ i) (gammaCoefficient Q w m j)=
      ((2 : ℂ)^m/(m.factorial : ℂ)) •
        ((interactionPaths j m).map (fun t ↦
          ((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) •
          (((wordDeletions t.word).map (fun d ↦ if d.letter=i then
            (-1 : ℂ)^d.position • cliffordWord Q d.remainder else 0)).sum))).sum := by
  rw [gammaCoefficient_paths,half_anticomm_smul,half_anticomm_list]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [InteractionPath.qeval,half_anticomm_smul]
  have hlen := (interactionPath_lengths j m t ht).2.1
  have hodd : Odd t.word.length := by rw [hlen]; exact ⟨m,by omega⟩
  rw [cliffordWord_odd_anticomm Q i t.word hodd,cliffordWordPartial_deletions]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma matrix_list_sum_apply {α I J R : Type} [AddMonoid R]
    (l : List α) (f : α → Matrix I J R) (i : I) (j : J) :
    (l.map f).sum i j=(l.map (fun a ↦ f a i j)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,List.sum_cons,Matrix.add_apply,ih]

lemma fermionPathTerm_reval (Q : Model N) (w : Disorder N) (m : ℕ) (j a b : Fin N)
    (t : InteractionPath N) (d : WordDeletion N) :
    (fermionPathTerm Q m j t d).reval w a b=
      if a=j ∧ b=d.letter then couplingMonomial t.couplings w*
        (((2 : ℝ)^m/(m.factorial : ℝ))*|t.sign|) else 0 := by
  simp only [fermionPathTerm,GaussianBlockTerm.reval,Matrix.smul_apply,smul_eq_mul,Matrix.single_apply]
  by_cases ha : a=j <;> by_cases hb : b=d.letter <;> simp_all [eq_comm]

lemma fermionPathPolynomial_reval (Q : Model N) (w : Disorder N) (m : ℕ) (a b : Fin N) :
    (GaussianBlockPolynomial.reval (fermionPathPolynomial Q m) w) a b=
      ((2 : ℝ)^m/(m.factorial : ℝ))*
        ((interactionPaths a m).map (fun t ↦ couplingMonomial t.couplings w*
          ((wordDeletions t.word).map (fun d ↦ if d.letter=b then (1 : ℝ) else 0)).sum)).sum := by
  unfold GaussianBlockPolynomial.reval fermionPathPolynomial
  rw [matrix_list_sum_apply]
  simp only [list_sum_flatMap,List.map_map,Function.comp_def,fermionPathTerm_reval]
  rw [all_list_sum]
  have hrow (j : Fin N) :
      ((interactionPaths j m).map (fun t ↦ ((wordDeletions t.word).map
        (fun d ↦ if a=j ∧ b=d.letter then couplingMonomial t.couplings w*
          (((2 : ℝ)^m/(m.factorial : ℝ))*|t.sign|) else 0)).sum)).sum=
      if j=a then ((2 : ℝ)^m/(m.factorial : ℝ))*
        ((interactionPaths a m).map (fun t ↦ couplingMonomial t.couplings w*
          ((wordDeletions t.word).map (fun d ↦ if d.letter=b then (1 : ℝ) else 0)).sum)).sum else 0 := by
    by_cases hj : j=a
    · subst j
      simp only [eq_self_iff_true,true_and,ite_true]
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      have hs := (interactionPath_lengths a m t ht).2.2
      rw [hs,← List.sum_map_mul_left,← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro d hd
      by_cases hb : d.letter=b <;> simp [hb,Ne.symm,mul_comm,mul_left_comm]
    · simp [hj,Ne.symm hj]
  simp_rw [hrow]
  simp

lemma subblock_list_sum {α I ι : Type} (l : List α) (f : α → Mat (I×ι)) (i j : I) :
    subblock (l.map f).sum i j=(l.map (fun a ↦ subblock (f a) i j)).sum := by
  ext x y
  simp only [subblock,Matrix.of_apply,matrix_list_sum_apply]

lemma subblock_real_smul {I ι : Type} (c : ℝ) (A : Mat (I×ι)) (i j : I) :
    subblock (c • A) i j=(c : ℂ) • subblock A i j := by
  ext x y
  simp [subblock,Matrix.smul_apply,Complex.real_smul]

lemma fermionPathTerm_qeval_block (Q : Model N) (w : Disorder N) (m : ℕ) (j a b : Fin N)
    (t : InteractionPath N) (d : WordDeletion N) :
    subblock ((fermionPathTerm Q m j t d).qeval w) a b=
      if a=j ∧ b=d.letter then ((2 : ℂ)^m/(m.factorial : ℂ)) •
        (((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) •
          ((-1 : ℂ)^d.position • cliffordWord Q d.remainder)) else 0 := by
  change subblock (couplingMonomial t.couplings w •
    Matrix.kronecker (Matrix.single j d.letter (1 : ℂ)) _) a b=_
  rw [subblock_real_smul,subblock_single_kronecker]
  by_cases he : a=j ∧ b=d.letter
  · simp only [he,true_and,and_true,ite_true,smul_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_ofNat,Complex.ofReal_natCast]
    congr 1
    ring
  · simp [he]

lemma fermionPathPolynomial_qeval_block (Q : Model N) (w : Disorder N) (m : ℕ) (a b : Fin N) :
    subblock (GaussianBlockPolynomial.qeval (fermionPathPolynomial Q m) w) a b=
      ((2 : ℂ)^m/(m.factorial : ℂ)) •
        ((interactionPaths a m).map (fun t ↦
          ((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) •
          (((wordDeletions t.word).map (fun d ↦ if d.letter=b then
            (-1 : ℂ)^d.position • cliffordWord Q d.remainder else 0)).sum))).sum := by
  letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
  unfold GaussianBlockPolynomial.qeval fermionPathPolynomial
  rw [subblock_list_sum]
  simp only [list_sum_flatMap,List.map_map,Function.comp_def,fermionPathTerm_qeval_block]
  rw [all_list_sum]
  have hrow (j : Fin N) :
      ((interactionPaths j m).map (fun t ↦ ((wordDeletions t.word).map
        (fun d ↦ if a=j ∧ b=d.letter then ((2 : ℂ)^m/(m.factorial : ℂ)) •
          (((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) •
            ((-1 : ℂ)^d.position • cliffordWord Q d.remainder)) else 0)).sum)).sum=
      if j=a then ((2 : ℂ)^m/(m.factorial : ℂ)) •
        ((interactionPaths a m).map (fun t ↦
          ((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) •
          (((wordDeletions t.word).map (fun d ↦ if d.letter=b then
            (-1 : ℂ)^d.position • cliffordWord Q d.remainder else 0)).sum))).sum else 0 := by
    by_cases hj : j=a
    · subst j
      simp only [eq_self_iff_true,true_and,ite_true]
      rw [← list_sum_smul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      rw [← list_sum_smul_left,← list_sum_smul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro d hd
      by_cases hb : d.letter=b <;> simp [hb,Ne.symm]
    · simp [hj,Ne.symm hj]
  simp_rw [hrow]
  simp

lemma fermionPathPolynomial_qeval (Q : Model N) (w : Disorder N) (m : ℕ) :
    GaussianBlockPolynomial.qeval (fermionPathPolynomial Q m) w=fermionCoefficient Q w m := by
  ext a b
  have hh := fermionPathPolynomial_qeval_block Q w m a.1 b.1
  rw [← fermionCoefficient_paths_block] at hh
  exact congrArg (fun X ↦ X a.2 b.2) hh

lemma fermionPathPolynomial_reval_complex (Q : Model N) (w : Disorder N) (m : ℕ) :
    ((GaussianBlockPolynomial.reval (fermionPathPolynomial Q m) w).map (algebraMap ℝ ℂ))=
      classicalCoefficient w m 1 := by
  ext a b
  rw [Matrix.map_apply,fermionPathPolynomial_reval,classicalCoefficient_paths]
  rfl

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma traceMoment_real_matrix {I : Type} [Fintype I] [DecidableEq I] (p : ℕ)
    (B : Matrix I I ℝ) :
    traceMoment p (B.map (algebraMap ℝ ℂ))=Matrix.trace ((B.transpose*B)^p) := by
  have hs : (B.map (algebraMap ℝ ℂ))ᴴ=B.transpose.map (algebraMap ℝ ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply,Matrix.map_apply]
  unfold traceMoment
  rw [hs,← Matrix.map_mul,← Matrix.map_pow]
  simp [Matrix.trace,Matrix.diag,Complex.re_sum]

lemma lemma9_proof {N : ℕ} (Q : Model N) (m p : ℕ) :
  Integrable (fun w => traceMoment p (fermionCoefficient Q w m)) (disorderLaw Q) ∧
  Integrable (fun w => traceMoment p (classicalCoefficient w m (fun _ => 1))) (disorderLaw Q) ∧
  (1 / (2 ^ (N / 2) : ℝ)) * (∫ w, traceMoment p (fermionCoefficient Q w m) ∂disorderLaw Q) ≤
    ∫ w, traceMoment p (classicalCoefficient w m (fun _ => 1)) ∂disorderLaw Q := by
  letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
  obtain ⟨hiq,hir,hc⟩ := GaussianBlockPolynomial.moment_comparison Q (fermionPathPolynomial Q m) p
  have hq (w : Disorder N) : GaussianBlockPolynomial.qeval (fermionPathPolynomial Q m) w=
      fermionCoefficient Q w m := fermionPathPolynomial_qeval Q w m
  have hr (w : Disorder N) :
      traceMoment p (classicalCoefficient w m (fun _ ↦ 1))=
      Matrix.trace (((GaussianBlockPolynomial.reval (fermionPathPolynomial Q m) w).transpose*
        GaussianBlockPolynomial.reval (fermionPathPolynomial Q m) w)^p) := by
    have he := fermionPathPolynomial_reval_complex Q w m
    have hσ : (1 : Fin N → ℝ)=(fun _ ↦ 1) := by ext i; rfl
    rw [hσ] at he
    rw [← he,traceMoment_real_matrix]
  simp only [hq,← hr] at hiq hir hc
  refine ⟨hiq,hir,?_⟩
  have hd : (0 : ℝ)<2^(N/2) := by positivity
  have hcard : (Fintype.card (SiteHilbert N) : ℝ)=(2 : ℝ)^(N/2) := by
    simp [SiteHilbert]
  rw [hcard] at hc
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using hc)

end SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : SYKFastMix.FastMixing.Model N) (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) :
  Integrable (fun w => SYKFastMix.FastMixing.traceMoment p (SYKFastMix.FastMixing.fermionCoefficient Q w m)) (SYKFastMix.FastMixing.disorderLaw Q) ∧
  Integrable (fun w => SYKFastMix.FastMixing.traceMoment p (SYKFastMix.FastMixing.classicalCoefficient w m (fun _ => 1))) (SYKFastMix.FastMixing.disorderLaw Q) ∧
  (1 / (2 ^ (N / 2) : ℝ)) * (∫ w, SYKFastMix.FastMixing.traceMoment p (SYKFastMix.FastMixing.fermionCoefficient Q w m) ∂SYKFastMix.FastMixing.disorderLaw Q) ≤
    ∫ w, SYKFastMix.FastMixing.traceMoment p (SYKFastMix.FastMixing.classicalCoefficient w m (fun _ => 1)) ∂SYKFastMix.FastMixing.disorderLaw Q :=
  SYKFastMix.FastMixing.lemma9_proof Q m p
