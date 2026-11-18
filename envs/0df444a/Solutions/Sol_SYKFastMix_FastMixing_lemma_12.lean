-- Prove2me | solution 1 for SYKFastMix.FastMixing.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T19:25:02.964562+00:00
-- url     : https://prove2.me/submissions/fcae1f5b-b9ba-4c16-b108-ad4cd35fded7

import Mathlib
import Theorems.Thm_SYKFastMix_FastMixing_lemma_9
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



set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open MvPolynomial
namespace SYKFastMix.FastMixing
variable {σ : Type} [DecidableEq σ]

def CoeffNonneg (p : MvPolynomial σ ℝ) : Prop := ∀ a, 0 ≤ coeff a p
def CoeffLE (p q : MvPolynomial σ ℝ) : Prop := ∀ a, coeff a p ≤ coeff a q

lemma coeffNonneg_zero : CoeffNonneg (0 : MvPolynomial σ ℝ) := by intro a; simp
lemma coeffNonneg_one : CoeffNonneg (1 : MvPolynomial σ ℝ) := by
  intro a
  rw [coeff_one]
  split_ifs <;> norm_num
lemma coeffNonneg_C (c : ℝ) (hc : 0≤c) : CoeffNonneg (C c : MvPolynomial σ ℝ) := by
  intro a
  rw [coeff_C]
  split_ifs <;> positivity
lemma coeffNonneg_X (i : σ) : CoeffNonneg (X i : MvPolynomial σ ℝ) := by
  intro a
  rw [coeff_X]
  split_ifs <;> norm_num
lemma CoeffNonneg.add {p q : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p+q) := by intro a; rw [coeff_add]; exact add_nonneg (hp a) (hq a)
lemma CoeffNonneg.mul {p q : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p*q) := by
  intro a
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun b hb ↦ mul_nonneg (hp b.1) (hq b.2))
lemma CoeffNonneg.pderiv {p : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (i : σ) :
    CoeffNonneg (pderiv i p) := by
  intro a
  rw [coeff_pderiv]
  exact mul_nonneg (hp _) (by positivity)
lemma CoeffNonneg.sum {α : Type} (s : Finset α) (p : α → MvPolynomial σ ℝ)
    (h : ∀ i∈s,CoeffNonneg (p i)) : CoeffNonneg (∑ i∈s,p i) := by
  intro a
  simp only [coeff_sum]
  exact Finset.sum_nonneg (fun i hi ↦ h i hi a)
lemma CoeffNonneg.prod {α : Type} (s : Finset α) (p : α → MvPolynomial σ ℝ)
    (h : ∀ i∈s,CoeffNonneg (p i)) : CoeffNonneg (∏ i∈s,p i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using (coeffNonneg_one (σ := σ))
  | cons i s hi ih =>
    rw [Finset.prod_cons]
    exact (h i (by simp)).mul (ih (fun j hj ↦ h j (by simp [hj])))
lemma CoeffNonneg.pow {p : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (n : ℕ) :
    CoeffNonneg (p^n) := by
  induction n with
  | zero => simpa using (coeffNonneg_one (σ := σ))
  | succ n ih => simpa only [pow_succ] using ih.mul hp

lemma coeffLE_refl (p : MvPolynomial σ ℝ) : CoeffLE p p := fun _ ↦ le_rfl
lemma CoeffLE.trans {p q r : MvPolynomial σ ℝ} (h : CoeffLE p q) (h' : CoeffLE q r) :
    CoeffLE p r := fun a ↦ (h a).trans (h' a)
lemma CoeffLE.add {p q r s : MvPolynomial σ ℝ} (h : CoeffLE p q) (h' : CoeffLE r s) :
    CoeffLE (p+r) (q+s) := by intro a; simpa only [coeff_add] using add_le_add (h a) (h' a)
lemma coeffLE_add_right (p : MvPolynomial σ ℝ) {q : MvPolynomial σ ℝ} (hq : CoeffNonneg q) :
    CoeffLE p (p+q) := by intro a; rw [coeff_add]; exact le_add_of_nonneg_right (hq a)
lemma CoeffLE.mul {p q r s : MvPolynomial σ ℝ} (h : CoeffLE p q) (h' : CoeffLE r s)
    (hr : CoeffNonneg r) (hq : CoeffNonneg q) : CoeffLE (p*r) (q*s) := by
  intro a
  simp only [coeff_mul]
  apply Finset.sum_le_sum
  intro b hb
  exact mul_le_mul (h b.1) (h' b.2) (hr b.2) (hq b.1)
lemma CoeffLE.pderiv {p q : MvPolynomial σ ℝ} (h : CoeffLE p q) (i : σ) :
    CoeffLE (pderiv i p) (pderiv i q) := by
  intro a
  simp only [coeff_pderiv]
  exact mul_le_mul_of_nonneg_right (h _) (by positivity)

lemma coeffLE_single_sum {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℝ)
    (i : α) (hi : i∈s) (hf : ∀ j∈s,CoeffNonneg (f j)) : CoeffLE (f i) (∑ j∈s,f j) := by
  intro a
  rw [coeff_sum]
  exact Finset.single_le_sum (fun j hj ↦ hf j hj a) hi

lemma CoeffLE.sum {α : Type} (s : Finset α) (p q : α → MvPolynomial σ ℝ)
    (h : ∀ i∈s,CoeffLE (p i) (q i)) : CoeffLE (∑ i∈s,p i) (∑ i∈s,q i) := by
  intro a
  simp only [coeff_sum]
  exact Finset.sum_le_sum (fun i hi ↦ h i hi a)

lemma CoeffNonneg.nsmul {p : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (n : ℕ) :
    CoeffNonneg (n • p) := by
  intro a
  rw [coeff_smul]
  exact nsmul_nonneg (hp a) n

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace SYKFastMix.FastMixing

lemma derivation_iterate_mul {R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (D : Derivation R A A) (f g : A) (n : ℕ) :
    D^[n] (f*g)=∑ i∈Finset.range (n+1), n.choose i • (D^[i] f*D^[n-i] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [map_sum,map_nsmul,Derivation.leibniz,smul_eq_mul,nsmul_add,Finset.sum_add_distrib]
    rw [show n+1+1=n+2 by omega,
      Finset.sum_choose_succ_nsmul (fun r s ↦ D^[r] f*D^[s] g) n]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [show n+1-i=(n-i)+1 by have := Finset.mem_range.mp hi; omega,
        Function.iterate_succ_apply']
    · apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [Function.iterate_succ_apply',mul_comm]

def dividedIterate {A : Type} [CommRing A] [Algebra ℝ A]
    (D : Derivation ℝ A A) (n : ℕ) (f : A) : A := (n.factorial : ℝ)⁻¹ • D^[n] f

lemma dividedIterate_mul {A : Type} [CommRing A] [Algebra ℝ A]
    (D : Derivation ℝ A A) (f g : A) (n : ℕ) :
    dividedIterate D n (f*g)=∑ i∈Finset.range (n+1), dividedIterate D i f*dividedIterate D (n-i) g := by
  unfold dividedIterate
  rw [derivation_iterate_mul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i≤n := by have := Finset.mem_range.mp hi; omega
  have hn : (n.factorial : ℝ)≠0 := by positivity
  have hi' : (i.factorial : ℝ)≠0 := by positivity
  have hni : ((n-i).factorial : ℝ)≠0 := by positivity
  have hf : (n.choose i : ℝ)*(i.factorial : ℝ)*((n-i).factorial : ℝ)=(n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hc : (n.factorial : ℝ)⁻¹*(n.choose i : ℝ)=
      ((n-i).factorial : ℝ)⁻¹*(i.factorial : ℝ)⁻¹ := by
    field_simp
    nlinarith [hf]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,smul_mul_assoc,mul_smul_comm,smul_smul,hc]
  congr 1
  ring

lemma derivation_iterate_const_mul {R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (D : Derivation R A A) (c f : A) (hc : D c=0) (m : ℕ) :
    D^[m] (c*f)=c*D^[m] f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih,Derivation.leibniz,hc,smul_zero,add_zero,
      Function.iterate_succ_apply',smul_eq_mul]

lemma derivation_iterate_sum {α R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (D : Derivation R A A) (m : ℕ) (s : Finset α) (f : α → A) :
    D^[m] (∑ i∈s,f i)=∑ i∈s,D^[m] (f i) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply',ih,map_sum]

lemma derivation_iterate_nsmul {R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (D : Derivation R A A) (m n : ℕ) (f : A) : D^[m] (n • f)=n • D^[m] f := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply',ih,map_nsmul]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MvPolynomial
namespace SYKFastMix.FastMixing
variable {N : ℕ}
abbrev ClassicalVariable (N : ℕ) := SYKEdge.KSet N 4 ⊕ Fin N
abbrev ClassicalPolynomial (N : ℕ) := MvPolynomial (ClassicalVariable N) ℝ

def formalEval (w : Disorder N) (x : Fin N → ℝ) : ClassicalPolynomial N →+* ℝ :=
  MvPolynomial.eval₂Hom (RingHom.id ℝ) (Sum.elim w x)
def formalDifferential (p : ClassicalPolynomial N) (w : Disorder N) (x : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ i, formalEval w x (pderiv (Sum.inr i) p) • ContinuousLinearMap.proj i

lemma formalDifferential_add (p q : ClassicalPolynomial N) (w : Disorder N) (x : Fin N → ℝ) :
    formalDifferential (p+q) w x=formalDifferential p w x+formalDifferential q w x := by
  simp only [formalDifferential,map_add,add_smul,Finset.sum_add_distrib]

lemma formalDifferential_mul_X_left (p : ClassicalPolynomial N) (A : SYKEdge.KSet N 4)
    (w : Disorder N) (x : Fin N → ℝ) :
    formalDifferential (p*X (Sum.inl A)) w x=w A • formalDifferential p w x := by
  simp only [formalDifferential,pderiv_mul,pderiv_X]
  have he (i : Fin N) : (Pi.single (Sum.inr i : ClassicalVariable N) (1 : ClassicalPolynomial N) :
      ClassicalVariable N → ClassicalPolynomial N) (Sum.inl A)=0 := by simp
  simp only [he,mul_zero,add_zero,map_mul]
  have hX : formalEval w x (X (Sum.inl A))=w A := by simp [formalEval]
  rw [hX]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul,mul_comm]

lemma formalDifferential_mul_X_right (p : ClassicalPolynomial N) (j : Fin N)
    (w : Disorder N) (x : Fin N → ℝ) :
    formalDifferential (p*X (Sum.inr j)) w x=
      x j • formalDifferential p w x+formalEval w x p • ContinuousLinearMap.proj j := by
  ext v
  simp only [formalDifferential,_root_.sum_apply,_root_.smul_apply,_root_.add_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,pderiv_mul,map_add,map_mul,pderiv_X]
  have he : formalEval w x (X (Sum.inr j))=x j := by simp [formalEval]
  have hs (i : Fin N) : formalEval w x ((Pi.single (Sum.inr i : ClassicalVariable N) (1 : ClassicalPolynomial N) :
      ClassicalVariable N → ClassicalPolynomial N) (Sum.inr j))=
      if i=j then 1 else 0 := by
    by_cases hij : i=j
    · subst j; simp
    · simp [hij,Ne.symm hij]
  simp only [he,hs,add_mul,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma formalEval_hasFDerivAt (p : ClassicalPolynomial N) (w : Disorder N) (x : Fin N → ℝ) :
    HasFDerivAt (fun y ↦ formalEval w y p) (formalDifferential p w x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [formalEval,formalDifferential] using! hasFDerivAt_const (c := a) x
  | add p q hp hq =>
    simpa only [map_add,formalDifferential_add] using! hp.add hq
  | mul_X p v hp =>
    rcases v with A|j
    · rw [formalDifferential_mul_X_left]
      have he : (fun y ↦ formalEval w y (p*X (Sum.inl A)))=
          fun y ↦ formalEval w y p*w A := by funext y; simp [formalEval]
      rw [he]
      convert! hp.mul_const (w A) using 1
    · rw [formalDifferential_mul_X_right]
      have he : (fun y ↦ formalEval w y (p*X (Sum.inr j)))=
          fun y ↦ formalEval w y p*y j := by funext y; simp [formalEval]
      rw [he]
      convert! hp.mul (hasFDerivAt_apply j x) using 1
      exact add_comm _ _

lemma coordinateDerivative_formalEval (p : ClassicalPolynomial N) (w : Disorder N)
    (x : Fin N → ℝ) (i : Fin N) :
    coordinateDerivative (fun y ↦ formalEval w y p) i x=formalEval w x (pderiv (Sum.inr i) p) := by
  rw [coordinateDerivative,(formalEval_hasFDerivAt p w x).fderiv]
  simp [formalDifferential,Pi.single_apply,eq_comm]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open MvPolynomial
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def formalG : ClassicalPolynomial N :=
  ∑ A : SYKEdge.KSet N 4, X (Sum.inl A)*∏ i∈A.1,X (Sum.inr i)

def formalGenerator : Derivation ℝ (ClassicalPolynomial N) (ClassicalPolynomial N) :=
  ∑ i : Fin N, (2*pderiv (Sum.inr i) formalG) • pderiv (Sum.inr i)

lemma derivation_sum_apply {α R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (s : Finset α) (D : α → Derivation R A A) (p : A) :
    (∑ i∈s,D i) p=∑ i∈s,D i p := by
  induction s using Finset.cons_induction with
  | empty => simp [Derivation.zero_apply]
  | cons i s hi ih => simp only [Finset.sum_cons,Derivation.add_apply,ih]

lemma formalGenerator_apply (p : ClassicalPolynomial N) :
    formalGenerator p=2*∑ i : Fin N, pderiv (Sum.inr i) formalG*pderiv (Sum.inr i) p := by
  simp only [formalGenerator,derivation_sum_apply,Derivation.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma formalG_nonneg : CoeffNonneg (formalG : ClassicalPolynomial N) := by
  apply CoeffNonneg.sum
  intro A hA
  exact (coeffNonneg_X _).mul (CoeffNonneg.prod _ _ (fun i hi ↦ coeffNonneg_X _))

lemma formalGenerator_nonneg {p : ClassicalPolynomial N} (hp : CoeffNonneg p) :
    CoeffNonneg (formalGenerator p) := by
  rw [formalGenerator_apply]
  have htwo : CoeffNonneg (2 : ClassicalPolynomial N) := by
    simpa only [one_add_one_eq_two] using
      (coeffNonneg_one (σ := ClassicalVariable N)).add coeffNonneg_one
  exact htwo.mul (CoeffNonneg.sum _ _ (fun i hi ↦
    (formalG_nonneg.pderiv _).mul (hp.pderiv _)))

lemma formalGenerator_iterate_nonneg {p : ClassicalPolynomial N} (hp : CoeffNonneg p) (m : ℕ) :
    CoeffNonneg (formalGenerator^[m] p) := by
  induction m with
  | zero => simpa using hp
  | succ m ih => simpa only [Function.iterate_succ_apply'] using formalGenerator_nonneg ih

lemma CoeffNonneg.real_smul {σ : Type} [DecidableEq σ] {p : MvPolynomial σ ℝ}
    (hp : CoeffNonneg p) (c : ℝ) (hc : 0≤c) : CoeffNonneg (c • p) := by
  intro a
  rw [coeff_smul]
  exact mul_nonneg hc (hp a)

lemma dividedIterate_formal_nonneg {p : ClassicalPolynomial N} (hp : CoeffNonneg p) (m : ℕ) :
    CoeffNonneg (dividedIterate formalGenerator m p) :=
  (formalGenerator_iterate_nonneg hp m).real_smul _ (by positivity)

lemma formalEval_formalG (w : Disorder N) (x : Fin N → ℝ) :
    formalEval w x formalG=classicalG w x := by
  simp [formalG,formalEval,classicalG,Finset.prod_mul_distrib]

lemma formalEval_generator (p : ClassicalPolynomial N) (w : Disorder N) (x : Fin N → ℝ) :
    formalEval w x (formalGenerator p)=classicalGenerator w (fun y ↦ formalEval w y p) x := by
  rw [formalGenerator_apply]
  simp only [map_mul,map_sum]
  have htwo : formalEval w x 2=2 := by norm_num [formalEval]
  rw [htwo]
  unfold classicalGenerator
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [coordinateDerivative_formalEval]
  have hg : classicalG w=fun y ↦ formalEval w y formalG := by
    funext y
    exact (formalEval_formalG w y).symm
  rw [hg,coordinateDerivative_formalEval]

lemma formalEval_generator_iterate (w : Disorder N) (x : Fin N → ℝ) (m : ℕ) (j : Fin N) :
    formalEval w x (formalGenerator^[m] (X (Sum.inr j)))=classicalIterate w m j x := by
  induction m generalizing x with
  | zero => simp [classicalIterate,formalEval]
  | succ m ih =>
    rw [Function.iterate_succ_apply',formalEval_generator]
    have he : (fun y ↦ formalEval w y (formalGenerator^[m] (X (Sum.inr j))))=
        classicalIterate w m j := funext ih
    rw [he]
    simp only [classicalIterate,Function.iterate_succ_apply']

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open MvPolynomial
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def formalWordProduct (S : Finset (Fin N)) : ClassicalPolynomial N := ∏ i∈S,X (Sum.inr i)

lemma formalWordProduct_pderiv (S : Finset (Fin N)) (i : Fin N) :
    pderiv (Sum.inr i) (formalWordProduct S)=
      if i∈S then formalWordProduct (S.erase i) else 0 := by
  induction S using Finset.cons_induction with
  | empty => simp [formalWordProduct,pderiv_one]
  | cons j S hj ih =>
    have hprod : formalWordProduct (Finset.cons j S hj)=X (Sum.inr j)*formalWordProduct S := by
      simp [formalWordProduct,Finset.prod_insert,hj]
    rw [hprod,pderiv_mul,ih,pderiv_X]
    by_cases hij : i=j
    · subst j
      simp [Pi.single_apply,hj,formalWordProduct]
    · by_cases hi : i∈S
      · have hji : j≠i := Ne.symm hij
        have hn : j∉S.erase i := by simp [hj]
        simp [Pi.single_apply,hij,hji,hi,formalWordProduct,Finset.erase_insert_of_ne hji,
          Finset.prod_insert,hn]
      · simp [Pi.single_apply,hij,Ne.symm hij,hi]

lemma formalG_pderiv (i : Fin N) :
    pderiv (Sum.inr i) (formalG : ClassicalPolynomial N)=
      ∑ A : SYKEdge.KSet N 4, if i∈A.1 then X (Sum.inl A)*formalWordProduct (A.1.erase i) else 0 := by
  unfold formalG
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [pderiv_mul]
  have hx : pderiv (Sum.inr i) (X (Sum.inl A) : ClassicalPolynomial N)=0 := by
    rw [pderiv_X]
    simp
  rw [hx,zero_mul,zero_add]
  change X (Sum.inl A)*pderiv (Sum.inr i) (formalWordProduct A.1)=_
  rw [formalWordProduct_pderiv]
  split_ifs <;> simp

lemma formalGenerator_coordinate (i : Fin N) :
    formalGenerator (X (Sum.inr i) : ClassicalPolynomial N)=2*pderiv (Sum.inr i) formalG := by
  rw [formalGenerator_apply]
  simp only [pderiv_X,Pi.single_apply,Sum.inr.injEq,mul_ite,mul_one,mul_zero]
  simp

lemma formalGenerator_coupling (A : SYKEdge.KSet N 4) :
    formalGenerator (X (Sum.inl A) : ClassicalPolynomial N)=0 := by
  rw [formalGenerator_apply]
  have hx (i : Fin N) : pderiv (Sum.inr i) (X (Sum.inl A) : ClassicalPolynomial N)=0 := by
    rw [pderiv_X]
    simp
  simp only [hx,mul_zero,Finset.sum_const_zero]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open MvPolynomial
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma formal_iterate_partial_product_lower (f : ClassicalPolynomial N) (hf : CoeffNonneg f)
    (j : Fin N) (m : ℕ) :
    CoeffLE (formalGenerator^[m] f)
      (pderiv (Sum.inr j) (formalGenerator^[m] (X (Sum.inr j)*f))) := by
  rw [derivation_iterate_mul]
  have hnonneg (r : ℕ) : CoeffNonneg
      (m.choose r • (formalGenerator^[r] (X (Sum.inr j))*formalGenerator^[m-r] f)) :=
    ((formalGenerator_iterate_nonneg (coeffNonneg_X _) r).mul
      (formalGenerator_iterate_nonneg hf (m-r))).nsmul _
  have hs := (coeffLE_single_sum (Finset.range (m+1))
    (fun r ↦ m.choose r • (formalGenerator^[r] (X (Sum.inr j))*formalGenerator^[m-r] f))
    0 (by simp) (fun r hr ↦ hnonneg r)).pderiv (Sum.inr j)
  simp only [Nat.choose_zero_right,Function.iterate_zero_apply,Nat.sub_zero,one_nsmul] at hs
  apply CoeffLE.trans ?_ hs
  rw [pderiv_mul,pderiv_X]
  simp only [Pi.single_eq_same,one_mul]
  exact coeffLE_add_right _ ((coeffNonneg_X _).mul
    ((formalGenerator_iterate_nonneg hf m).pderiv _))

lemma formalWordProduct_nonneg (S : Finset (Fin N)) : CoeffNonneg (formalWordProduct S) :=
  CoeffNonneg.prod _ _ (fun i hi ↦ coeffNonneg_X _)

lemma formal_iterate_erased_product_lower (S : Finset (Fin N)) (j : Fin N) (hj : j∈S) (m : ℕ) :
    CoeffLE (formalGenerator^[m] (formalWordProduct (S.erase j)))
      (pderiv (Sum.inr j) (formalGenerator^[m] (formalWordProduct S))) := by
  have he : formalWordProduct S=X (Sum.inr j)*formalWordProduct (S.erase j) := by
    unfold formalWordProduct
    exact (Finset.mul_prod_erase S _ hj).symm
  rw [he]
  exact formal_iterate_partial_product_lower _ (formalWordProduct_nonneg _) j m

def formalHessianNumerator (m : ℕ) (i j : Fin N) : ClassicalPolynomial N :=
  2*∑ A : SYKEdge.KSet N 4, if i∈A.1 ∧ j∈A.1.erase i then
    X (Sum.inl A)*formalGenerator^[m] (formalWordProduct ((A.1.erase i).erase j)) else 0

lemma formal_hessian_jacobian_bound (m : ℕ) (i j : Fin N) :
    CoeffLE (formalHessianNumerator m i j)
      (pderiv (Sum.inr j) (formalGenerator^[m+1] (X (Sum.inr i)))) := by
  rw [Function.iterate_succ_apply,formalGenerator_coordinate,formalG_pderiv]
  have htwo (p : ClassicalPolynomial N) : (2 : ClassicalPolynomial N)*p=2 • p := by
    simp [two_mul,two_nsmul]
  rw [htwo,derivation_iterate_nsmul,derivation_iterate_sum,map_nsmul,map_sum]
  unfold formalHessianNumerator
  rw [htwo]
  have hs : CoeffLE
      (∑ A : SYKEdge.KSet N 4, if i∈A.1 ∧ j∈A.1.erase i then
        X (Sum.inl A)*formalGenerator^[m] (formalWordProduct ((A.1.erase i).erase j)) else 0)
      (∑ A : SYKEdge.KSet N 4, pderiv (Sum.inr j) (formalGenerator^[m]
        (if i∈A.1 then X (Sum.inl A)*formalWordProduct (A.1.erase i) else 0))) := by
    apply CoeffLE.sum
    intro A hA
    by_cases hi : i∈A.1
    · simp only [hi,true_and,ite_true]
      rw [derivation_iterate_const_mul _ _ _ (formalGenerator_coupling A),pderiv_mul]
      have hx : pderiv (Sum.inr j) (X (Sum.inl A) : ClassicalPolynomial N)=0 := by
        rw [pderiv_X]; simp
      rw [hx,zero_mul,zero_add]
      by_cases hj : j∈A.1.erase i
      · rw [if_pos hj]
        exact (coeffLE_refl (X (Sum.inl A))).mul
          (formal_iterate_erased_product_lower _ j hj m)
          (formalGenerator_iterate_nonneg (formalWordProduct_nonneg _) m) (coeffNonneg_X _)
      · rw [if_neg hj]
        exact (coeffNonneg_X _).mul
          ((formalGenerator_iterate_nonneg (formalWordProduct_nonneg _) m).pderiv _)
    · simp only [hi,false_and,ite_false]
      have hz : formalGenerator^[m] (0 : ClassicalPolynomial N)=0 := by
        induction m with
        | zero => rfl
        | succ m ih => simp only [Function.iterate_succ_apply',ih,map_zero]
      rw [hz,map_zero]
      exact coeffLE_refl 0
  intro a
  simp only [coeff_smul,smul_eq_mul]
  exact nsmul_le_nsmul_right (hs a) 2

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open MvPolynomial MeasureTheory
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma integrable_gaussian_monomial (Q : Model N) (a : SYKEdge.KSet N 4 →₀ ℕ) :
    Integrable (fun w : Disorder N ↦ ∏ A,w A^(a A)) (disorderLaw Q) := by
  exact Integrable.fintype_prod (fun A ↦ integrable_gaussian_power
    (Real.toNNReal (6*Q.J^2/(N : ℝ)^3)) (a A))

lemma gaussian_monomial_integral_nonneg (Q : Model N) (a : SYKEdge.KSet N 4 →₀ ℕ) :
    0≤∫ w : Disorder N, (∏ A,w A^(a A)) ∂disorderLaw Q := by
  unfold disorderLaw
  rw [integral_fintype_prod_eq_prod (fun (A : SYKEdge.KSet N 4) (x : ℝ) ↦ x^(a A))]
  exact Finset.prod_nonneg (fun A hA ↦ gaussian_power_integral_nonneg _ _)

lemma eval_monomial_fintype {σ : Type} [Fintype σ] [DecidableEq σ]
    (a : σ →₀ ℕ) (c : ℝ) (w : σ → ℝ) :
    MvPolynomial.eval w (monomial a c)=c*∏ A,w A^(a A) := by
  rw [eval_monomial]
  congr 1
  exact Finset.prod_subset (Finset.subset_univ _)
    (by intro A hA hn; simp only [Finsupp.notMem_support_iff.mp hn,pow_zero])

lemma integrable_gaussian_polynomial (Q : Model N) (p : MvPolynomial (SYKEdge.KSet N 4) ℝ) :
    Integrable (fun w : Disorder N ↦ MvPolynomial.eval w p) (disorderLaw Q) := by
  have hp := p.as_sum
  rw [hp]
  simp only [eval_sum,eval_monomial_fintype]
  apply integrable_finset_sum
  intro a ha
  exact (integrable_gaussian_monomial Q a).const_mul _

lemma gaussian_polynomial_integral_nonneg (Q : Model N) (p : MvPolynomial (SYKEdge.KSet N 4) ℝ)
    (hp : CoeffNonneg p) :
    0≤∫ w : Disorder N, MvPolynomial.eval w p ∂disorderLaw Q := by
  have he (w : Disorder N) : MvPolynomial.eval w p=
      ∑ a∈p.support, coeff a p*(∏ A,w A^(a A)) := by
    conv_lhs => rw [p.as_sum]
    simp only [eval_sum,eval_monomial_fintype]
  simp_rw [he]
  rw [integral_finset_sum]
  · apply Finset.sum_nonneg
    intro a ha
    rw [integral_const_mul]
    exact mul_nonneg (hp a) (gaussian_monomial_integral_nonneg Q a)
  · intro a ha
    exact (integrable_gaussian_monomial Q a).const_mul _

lemma gaussian_polynomial_integral_mono (Q : Model N)
    (p q : MvPolynomial (SYKEdge.KSet N 4) ℝ) (h : CoeffLE p q) :
    (∫ w : Disorder N, MvPolynomial.eval w p ∂disorderLaw Q) ≤
      ∫ w : Disorder N, MvPolynomial.eval w q ∂disorderLaw Q := by
  have hh : CoeffNonneg (q-p) := by intro a; simpa only [coeff_sub,sub_nonneg] using h a
  have hi := gaussian_polynomial_integral_nonneg Q (q-p) hh
  simp only [map_sub] at hi
  rw [integral_sub (integrable_gaussian_polynomial Q q) (integrable_gaussian_polynomial Q p)] at hi
  linarith

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open Matrix MvPolynomial MeasureTheory
namespace SYKFastMix.FastMixing
variable {σ I : Type} [DecidableEq σ] [Fintype I] [DecidableEq I]

def MatrixCoeffNonneg (A : Matrix I I (MvPolynomial σ ℝ)) : Prop := ∀ i j,CoeffNonneg (A i j)
def MatrixCoeffLE (A B : Matrix I I (MvPolynomial σ ℝ)) : Prop := ∀ i j,CoeffLE (A i j) (B i j)

lemma matrixCoeffNonneg_one : MatrixCoeffNonneg (1 : Matrix I I (MvPolynomial σ ℝ)) := by
  intro i j
  by_cases hij : i=j <;> simp only [Matrix.one_apply,hij,ite_true,ite_false]
  · exact coeffNonneg_one
  · exact coeffNonneg_zero
lemma MatrixCoeffNonneg.mul {A B : Matrix I I (MvPolynomial σ ℝ)}
    (hA : MatrixCoeffNonneg A) (hB : MatrixCoeffNonneg B) : MatrixCoeffNonneg (A*B) := by
  intro i j
  exact CoeffNonneg.sum _ _ (fun k hk ↦ (hA i k).mul (hB k j))
lemma MatrixCoeffNonneg.transpose {A : Matrix I I (MvPolynomial σ ℝ)}
    (hA : MatrixCoeffNonneg A) : MatrixCoeffNonneg A.transpose := fun i j ↦ hA j i
lemma MatrixCoeffLE.mul {A B C D : Matrix I I (MvPolynomial σ ℝ)}
    (h : MatrixCoeffLE A B) (h' : MatrixCoeffLE C D)
    (hC : MatrixCoeffNonneg C) (hB : MatrixCoeffNonneg B) : MatrixCoeffLE (A*C) (B*D) := by
  intro i j
  exact CoeffLE.sum _ _ _ (fun k hk ↦ (h i k).mul (h' k j) (hC k j) (hB i k))
lemma MatrixCoeffLE.transpose {A B : Matrix I I (MvPolynomial σ ℝ)}
    (h : MatrixCoeffLE A B) : MatrixCoeffLE A.transpose B.transpose := fun i j ↦ h j i
lemma MatrixCoeffNonneg.pow {A : Matrix I I (MvPolynomial σ ℝ)} (hA : MatrixCoeffNonneg A) (p : ℕ) :
    MatrixCoeffNonneg (A^p) := by
  induction p with
  | zero => simpa using (matrixCoeffNonneg_one (σ := σ) (I := I))
  | succ p ih => simpa only [pow_succ] using ih.mul hA
lemma MatrixCoeffLE.pow {A B : Matrix I I (MvPolynomial σ ℝ)} (h : MatrixCoeffLE A B)
    (hA : MatrixCoeffNonneg A) (hB : MatrixCoeffNonneg B) (p : ℕ) : MatrixCoeffLE (A^p) (B^p) := by
  induction p with
  | zero => intro i j a; simp
  | succ p ih => simpa only [pow_succ] using ih.mul h hA (hB.pow p)
lemma MatrixCoeffLE.trace {A B : Matrix I I (MvPolynomial σ ℝ)} (h : MatrixCoeffLE A B) :
    CoeffLE (Matrix.trace A) (Matrix.trace B) := CoeffLE.sum _ _ _ (fun i hi ↦ h i i)

lemma matrix_polynomial_moment_mono {N : ℕ}
    (Q : Model N) (A B : Matrix I I (MvPolynomial (SYKEdge.KSet N 4) ℝ))
    (h : MatrixCoeffLE A B) (hA : MatrixCoeffNonneg A) (hB : MatrixCoeffNonneg B) (p : ℕ) :
    (∫ w : Disorder N, Matrix.trace (((A.map (MvPolynomial.eval w)).transpose*A.map (MvPolynomial.eval w))^p)
      ∂disorderLaw Q) ≤
    ∫ w : Disorder N, Matrix.trace (((B.map (MvPolynomial.eval w)).transpose*B.map (MvPolynomial.eval w))^p)
      ∂disorderLaw Q := by
  have hh := ((h.transpose.mul h hA hB.transpose).pow (hA.transpose.mul hA)
    (hB.transpose.mul hB) p).trace
  have hi := gaussian_polynomial_integral_mono Q _ _ hh
  have he (C : Matrix I I (MvPolynomial (SYKEdge.KSet N 4) ℝ)) (w : Disorder N) :
      MvPolynomial.eval w (Matrix.trace ((C.transpose*C)^p))=
        Matrix.trace (((C.map (MvPolynomial.eval w)).transpose*C.map (MvPolynomial.eval w))^p) := by
    have hT : (C.map (MvPolynomial.eval w)).transpose=C.transpose.map (MvPolynomial.eval w) := rfl
    rw [hT,← Matrix.map_mul,← Matrix.map_pow]
    simp [Matrix.trace,Matrix.diag]
  simp only [he] at hi
  exact hi

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open MvPolynomial
namespace SYKFastMix.FastMixing
variable {σ τ : Type} [DecidableEq σ] [DecidableEq τ]

lemma coeffNonneg_substitution (p : MvPolynomial σ ℝ) (f : σ → MvPolynomial τ ℝ)
    (hp : CoeffNonneg p) (hf : ∀ i,CoeffNonneg (f i)) :
    CoeffNonneg (MvPolynomial.eval₂Hom MvPolynomial.C f p) := by
  rw [p.as_sum,map_sum]
  apply CoeffNonneg.sum
  intro a ha
  change CoeffNonneg (MvPolynomial.eval₂ MvPolynomial.C f (monomial a (coeff a p)))
  rw [MvPolynomial.eval₂_monomial]
  exact (coeffNonneg_C _ (hp a)).mul
    (CoeffNonneg.prod _ _ (fun i hi ↦ (hf i).pow _))

lemma coeffLE_substitution (p q : MvPolynomial σ ℝ) (f : σ → MvPolynomial τ ℝ)
    (h : CoeffLE p q) (hf : ∀ i,CoeffNonneg (f i)) :
    CoeffLE (MvPolynomial.eval₂Hom MvPolynomial.C f p) (MvPolynomial.eval₂Hom MvPolynomial.C f q) := by
  have hh : CoeffNonneg (q-p) := by intro a; simpa only [coeff_sub,sub_nonneg] using h a
  have hi := coeffNonneg_substitution (q-p) f hh hf
  intro a
  simpa only [map_sub,coeff_sub,sub_nonneg] using hi a

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open MvPolynomial
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def initialOne : ClassicalPolynomial N →+* MvPolynomial (SYKEdge.KSet N 4) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim MvPolynomial.X (fun _ ↦ 1))

lemma initialOne_nonneg (p : ClassicalPolynomial N) (hp : CoeffNonneg p) :
    CoeffNonneg (initialOne p) := by
  apply coeffNonneg_substitution _ _ hp
  intro v
  rcases v with A|i
  · exact coeffNonneg_X A
  · exact coeffNonneg_one
lemma initialOne_mono (p q : ClassicalPolynomial N) (h : CoeffLE p q) :
    CoeffLE (initialOne p) (initialOne q) := by
  apply coeffLE_substitution _ _ _ h
  intro v
  rcases v with A|i
  · exact coeffNonneg_X A
  · exact coeffNonneg_one

lemma initialOne_smul (c : ℝ) (p : ClassicalPolynomial N) : initialOne (c • p)=c • initialOne p := by
  rw [← C_mul',map_mul]
  simp [initialOne,C_mul']

lemma initialOne_eval (p : ClassicalPolynomial N) (w : Disorder N) :
    MvPolynomial.eval w (initialOne p)=formalEval w (fun _ ↦ 1) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [initialOne,formalEval]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p v hp =>
    simp only [map_mul]
    rw [hp]
    rcases v with A|i <;> simp [initialOne,formalEval]

lemma CoeffLE.real_smul {σ : Type} [DecidableEq σ] {p q : MvPolynomial σ ℝ}
    (h : CoeffLE p q) (c : ℝ) (hc : 0≤c) : CoeffLE (c • p) (c • q) := by
  intro a
  simp only [coeff_smul,smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (h a) hc

def formalGammaCoefficient (m : ℕ) (i : Fin N) : MvPolynomial (SYKEdge.KSet N 4) ℝ :=
  initialOne (dividedIterate formalGenerator m (X (Sum.inr i)))
def formalJacobianCoefficient (m : ℕ) (i j : Fin N) : MvPolynomial (SYKEdge.KSet N 4) ℝ :=
  initialOne ((m.factorial : ℝ)⁻¹ • pderiv (Sum.inr j) (formalGenerator^[m] (X (Sum.inr i))))
def formalHessianCoefficient (m : ℕ) (i j : Fin N) : MvPolynomial (SYKEdge.KSet N 4) ℝ :=
  initialOne ((m.factorial : ℝ)⁻¹ • formalHessianNumerator m i j)

lemma formalGammaCoefficient_nonneg (m : ℕ) (i : Fin N) : CoeffNonneg (formalGammaCoefficient m i) :=
  initialOne_nonneg _ (dividedIterate_formal_nonneg (coeffNonneg_X _) m)
lemma formalJacobianCoefficient_nonneg (m : ℕ) (i j : Fin N) :
    CoeffNonneg (formalJacobianCoefficient m i j) :=
  initialOne_nonneg _ (((formalGenerator_iterate_nonneg (coeffNonneg_X _) m).pderiv _).real_smul _ (by positivity))

lemma formalHessianCoefficient_bound (m : ℕ) (i j : Fin N) :
    CoeffLE (formalHessianCoefficient m i j) ((m+1 : ℝ) • formalJacobianCoefficient (m+1) i j) := by
  have h := initialOne_mono _ _ ((formal_hessian_jacobian_bound m i j).real_smul
    (m.factorial : ℝ)⁻¹ (by positivity))
  change CoeffLE (formalHessianCoefficient m i j) _ at h
  convert h using 1
  simp only [formalJacobianCoefficient,initialOne_smul,smul_smul]
  congr 1
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

lemma formalGammaCoefficient_eval (m : ℕ) (i : Fin N) (w : Disorder N) :
    MvPolynomial.eval w (formalGammaCoefficient m i)=
      classicalIterate w m i (fun _ ↦ 1)/(m.factorial : ℝ) := by
  rw [formalGammaCoefficient,initialOne_eval]
  unfold dividedIterate
  rw [← C_mul',map_mul]
  simp only [formalEval,MvPolynomial.eval₂Hom_C,RingHom.id_apply]
  change (m.factorial : ℝ)⁻¹*formalEval w (fun _ ↦ 1)
    (formalGenerator^[m] (X (Sum.inr i)))=_
  rw [formalEval_generator_iterate]
  ring

lemma formalJacobianCoefficient_eval (m : ℕ) (i j : Fin N) (w : Disorder N) :
    MvPolynomial.eval w (formalJacobianCoefficient m i j)=
      coordinateDerivative (classicalIterate w m i) j (fun _ ↦ 1)/(m.factorial : ℝ) := by
  rw [formalJacobianCoefficient,initialOne_eval,← C_mul',map_mul]
  have hC (c : ℝ) : formalEval w (fun _ ↦ 1) (C c)=c := by simp [formalEval]
  rw [hC]
  have he : classicalIterate w m i=fun y ↦ formalEval w y (formalGenerator^[m] (X (Sum.inr i))) := by
    funext y
    exact (formalEval_generator_iterate w y m i).symm
  rw [he,coordinateDerivative_formalEval]
  ring

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma super_left_right_kronecker (A B : Mat ι) :
    super (fun X ↦ A*X*B)=Matrix.kronecker A B.transpose := by
  ext a b
  simp [super,Matrix.kroneckerMap_apply,Matrix.mul_apply,Matrix.single_apply,
    ite_and,Finset.sum_ite_eq',Finset.sum_ite_eq,mul_ite,ite_mul]

lemma unitary_transpose {B : Mat ι} (hB : B∈unitary (Mat ι)) : B.transpose∈unitary (Mat ι) := by
  rcases Unitary.mem_iff.mp hB with ⟨hl,hr⟩
  change Bᴴ*B=1 at hl
  change B*Bᴴ=1 at hr
  apply Unitary.mem_iff.mpr
  change (B.transpose)ᴴ*B.transpose=1 ∧ B.transpose*(B.transpose)ᴴ=1
  constructor
  · have hh := congrArg Matrix.transpose hr
    simpa only [Matrix.transpose_mul,Matrix.transpose_one,Matrix.conjTranspose_transpose,
      Matrix.transpose_conjTranspose] using hh
  · have hh := congrArg Matrix.transpose hl
    simpa only [Matrix.transpose_mul,Matrix.transpose_one,Matrix.conjTranspose_transpose,
      Matrix.transpose_conjTranspose] using hh

lemma unitary_kronecker {A B : Mat ι} (hA : A∈unitary (Mat ι)) (hB : B∈unitary (Mat ι)) :
    Matrix.kronecker A B∈unitary (Super ι) := by
  rcases Unitary.mem_iff.mp hA with ⟨hAl,hAr⟩
  rcases Unitary.mem_iff.mp hB with ⟨hBl,hBr⟩
  change Aᴴ*A=1 at hAl
  change A*Aᴴ=1 at hAr
  change Bᴴ*B=1 at hBl
  change B*Bᴴ=1 at hBr
  apply Unitary.mem_iff.mpr
  change (Matrix.kronecker A B)ᴴ*Matrix.kronecker A B=1 ∧
    Matrix.kronecker A B*(Matrix.kronecker A B)ᴴ=1
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,
    hAl,hAr,hBl,hBr,Matrix.one_kronecker_one]
  exact ⟨rfl,rfl⟩

lemma unitary_super_left_right {A B : Mat ι} (hA : A∈unitary (Mat ι)) (hB : B∈unitary (Mat ι)) :
    super (fun X ↦ A*X*B)∈unitary (Super ι) := by
  rw [super_left_right_kronecker]
  exact unitary_kronecker hA (unitary_transpose hB)

lemma cliffordWord_unitary {N : ℕ} (Q : Model N) (l : List (Fin N)) :
    cliffordWord Q l∈unitary (Mat (SiteHilbert N)) := by
  unfold cliffordWord
  apply Submonoid.list_prod_mem
  intro A hA
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hA
  apply Unitary.mem_iff.mpr
  change (Q.γ i)ᴴ*Q.γ i=1 ∧ Q.γ i*(Q.γ i)ᴴ=1
  rw [(Q.car.herm i).eq]
  exact ⟨Q.car.sq i,Q.car.sq i⟩

lemma norm_super_clifford_words {N : ℕ} (Q : Model N) (l k : List (Fin N)) :
    ‖super (fun X ↦ cliffordWord Q l*X*cliffordWord Q k)‖=1 := by
  letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
  exact CStarRing.norm_coe_unitary ⟨_,unitary_super_left_right (cliffordWord_unitary Q l)
    (cliffordWord_unitary Q k)⟩

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open Matrix
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma coupling_inversions (i j k l : Fin N) :
    (Finset.univ.filter (fun p : Fin 4 × Fin 4 ↦ p.1 < p.2 ∧
      (![i,j,k,l] : Fin 4 → Fin N) p.2<(![i,j,k,l] : Fin 4 → Fin N) p.1)).card=
      (if j < i then 1 else 0)+(if k < i then 1 else 0)+(if l < i then 1 else 0)+
        (if k < j then 1 else 0)+(if l < j then 1 else 0)+(if l < k then 1 else 0) := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  simp only [Fin.lt_def,Fin.val_zero,Fin.val_succ,Fin.val_ofNat]
  norm_num only
  simp only [true_and,false_and,ite_false,ite_true,zero_add,add_zero]
  omega

lemma coupling_explicit (w : Disorder N) (i j k l : Fin N) :
    coupling w i j k l=
      if h : ({i,j,k,l} : Finset (Fin N)).card=4 then
        (-1 : ℝ)^((if j < i then 1 else 0)+(if k < i then 1 else 0)+(if l < i then 1 else 0)+
          (if k < j then 1 else 0)+(if l < j then 1 else 0)+(if l < k then 1 else 0))*w ⟨{i,j,k,l},h⟩
      else 0 := by
  simp only [coupling,coupling_inversions]

lemma distinct_four_ne01 (i j k l : Fin N) (h : ({i,j,k,l} : Finset (Fin N)).card=4) : i≠j := by
  intro he
  subst j
  simp only [Finset.insert_idem] at h
  have hh : ({i,k,l} : Finset (Fin N)).card≤3 := Finset.card_le_three
  omega

lemma minus_one_order (i j : Fin N) (hij : i≠j) :
    (-1 : ℝ)^(if j < i then 1 else 0)=-(-1 : ℝ)^(if i < j then 1 else 0) := by
  rcases lt_or_gt_of_ne hij with h|h <;> simp [h,not_lt_of_ge h.le]

lemma coupling_swap01 (w : Disorder N) (i j k l : Fin N) :
    coupling w j i k l=-coupling w i j k l := by
  have hset : ({j,i,k,l} : Finset (Fin N))={i,j,k,l} := by ext x; simp [or_left_comm]
  rw [coupling_explicit,coupling_explicit]
  by_cases h : ({i,j,k,l} : Finset (Fin N)).card=4
  · simp only [hset,h,↓reduceDIte]
    have hn := minus_one_order i j (distinct_four_ne01 i j k l h)
    simp only [pow_add]
    rw [hn]
    ring
  · simp [hset,h]

lemma coupling_swap12 (w : Disorder N) (i j k l : Fin N) :
    coupling w i k j l=-coupling w i j k l := by
  have hset : ({i,k,j,l} : Finset (Fin N))={i,j,k,l} := by ext x; simp [or_left_comm,or_assoc]
  rw [coupling_explicit,coupling_explicit]
  by_cases h : ({i,j,k,l} : Finset (Fin N)).card=4
  · simp only [hset,h,↓reduceDIte]
    have hne : j≠k := by
      apply distinct_four_ne01 j k i l
      convert! h using 1
      congr 1
      ext x
      simp [or_comm,or_left_comm,or_assoc]
    have hn := minus_one_order j k hne
    simp only [pow_add]
    rw [hn]
    ring
  · simp [hset,h]

lemma coupling_swap23 (w : Disorder N) (i j k l : Fin N) :
    coupling w i j l k=-coupling w i j k l := by
  have hset : ({i,j,l,k} : Finset (Fin N))={i,j,k,l} := by ext x; simp [or_left_comm,or_assoc,or_comm]
  rw [coupling_explicit,coupling_explicit]
  by_cases h : ({i,j,k,l} : Finset (Fin N)).card=4
  · simp only [hset,h,↓reduceDIte]
    have hne : k≠l := by
      apply distinct_four_ne01 k l i j
      convert! h using 1
      congr 1
      ext x
      simp [or_comm,or_left_comm,or_assoc]
    have hn := minus_one_order k l hne
    simp only [pow_add]
    rw [hn]
    ring
  · simp [hset,h]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma quartic_pair_distinct (A : SYKEdge.KSet N 4) (i j k l : Fin N)
    (he : A.1={i,j,k,l}) : k≠i ∧ k≠j ∧ l≠i ∧ l≠j ∧ k≠l ∧ i≠j := by
  have hc : ({i,j,k,l} : Finset (Fin N)).card=4 := by rw [← he]; exact A.2
  have hc' (a b c d : Fin N) (hs : ({a,b,c,d} : Finset (Fin N))={i,j,k,l}) : a≠b :=
    distinct_four_ne01 a b c d (by rw [hs]; exact hc)
  refine ⟨hc' k i j l ?_,hc' k j i l ?_,hc' l i j k ?_,hc' l j i k ?_,hc' k l i j ?_,hc' i j k l rfl⟩ <;>
    ext x <;> simp [or_assoc,or_comm,or_left_comm]

lemma quartic_pair_condition (A : SYKEdge.KSet N 4) (i j k l : Fin N)
    (he : A.1={i,j,k,l}) : i∈A.1 ∧ j∈A.1.erase i := by
  have hd := quartic_pair_distinct A i j k l he
  rw [he]
  simp [hd.2.2.2.2.2,Ne.symm hd.2.2.2.2.2]

lemma quartic_pair_complement_iff (A : SYKEdge.KSet N 4) (i j a b : Fin N)
    (hi : i∈A.1) (hj : j∈A.1.erase i) (hab : a≠b)
    (hr : (A.1.erase i).erase j={a,b}) (k l : Fin N) :
    A.1={i,j,k,l} ↔ (k=a ∧ l=b) ∨ (k=b ∧ l=a) := by
  have hA : A.1={i,j,a,b} := by
    have h1 := Finset.insert_erase hi
    have h2 := Finset.insert_erase hj
    rw [← h1,← h2,hr]
  constructor
  · intro he
    have hd := quartic_pair_distinct A i j k l he
    have hk : k∈(A.1.erase i).erase j := by rw [he]; simp [hd.1,hd.2.1]
    have hl : l∈(A.1.erase i).erase j := by rw [he]; simp [hd.2.2.1,hd.2.2.2.1]
    rw [hr] at hk hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk hl
    rcases hk with rfl|rfl <;> rcases hl with rfl|rfl
    · exact False.elim (hd.2.2.2.2.1 rfl)
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
    · exact False.elim (hd.2.2.2.2.1 rfl)
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact hA
    · rw [hA]
      ext x
      simp [or_assoc,or_comm,or_left_comm]

lemma quartic_pair_sum {R : Type} [AddCommMonoid R] (A : SYKEdge.KSet N 4) (i j a b : Fin N)
    (hi : i∈A.1) (hj : j∈A.1.erase i) (hab : a≠b)
    (hr : (A.1.erase i).erase j={a,b}) (f : Fin N → Fin N → R) (hf : f a b=f b a) :
    (∑ k, ∑ l, if A.1={i,j,k,l} then f k l else 0)=2 • f a b := by
  have hterm (k l : Fin N) : (if A.1={i,j,k,l} then f k l else 0)=
      (if k=a ∧ l=b then f a b else 0)+(if k=b ∧ l=a then f a b else 0) := by
    simp only [quartic_pair_complement_iff A i j a b hi hj hab hr]
    by_cases h1 : k=a ∧ l=b
    · rcases h1 with ⟨rfl,rfl⟩; simp [hab,Ne.symm hab]
    · by_cases h2 : k=b ∧ l=a
      · rcases h2 with ⟨rfl,rfl⟩; simp [hab,Ne.symm hab,← hf]
      · simp [h1,h2]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib,ite_and,two_nsmul]

lemma quartic_pair_sum_zero {R : Type} [AddCommMonoid R] (A : SYKEdge.KSet N 4) (i j : Fin N)
    (h : ¬(i∈A.1 ∧ j∈A.1.erase i)) (f : Fin N → Fin N → R) :
    (∑ k, ∑ l, if A.1={i,j,k,l} then f k l else 0)=0 := by
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  rw [if_neg]
  exact fun he ↦ h (quartic_pair_condition A i j k l he)

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MvPolynomial
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def formalPairFlow (m : ℕ) (k l : Fin N) : MvPolynomial (SYKEdge.KSet N 4) ℝ :=
  initialOne (dividedIterate formalGenerator m (X (Sum.inr k)*X (Sum.inr l)))

lemma formalPairFlow_convolution (m : ℕ) (k l : Fin N) :
    formalPairFlow m k l=∑ r∈Finset.range (m+1), formalGammaCoefficient r k*formalGammaCoefficient (m-r) l := by
  rw [formalPairFlow,dividedIterate_mul,map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [map_mul]
  rfl

lemma formalPairFlow_symmetric (m : ℕ) (k l : Fin N) : formalPairFlow m k l=formalPairFlow m l k := by
  simp only [formalPairFlow,mul_comm]

lemma formalHessianCoefficient_expand (m : ℕ) (i j : Fin N) :
    formalHessianCoefficient m i j=
      2*∑ A : SYKEdge.KSet N 4, if i∈A.1 ∧ j∈A.1.erase i then X A*
        initialOne (dividedIterate formalGenerator m (formalWordProduct ((A.1.erase i).erase j))) else 0 := by
  unfold formalHessianCoefficient formalHessianNumerator
  rw [initialOne_smul,map_mul,map_sum]
  have h2 : initialOne (2 : ClassicalPolynomial N)=2 := by
    rw [show (2 : ClassicalPolynomial N)=1+1 by ring,map_add,map_one]
    ring
  rw [h2,← mul_smul_comm]
  congr 1
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  split_ifs with h
  · rw [map_mul]
    have hx : initialOne (X (Sum.inl A))=X A := by simp [initialOne]
    rw [hx]
    simp only [dividedIterate,initialOne_smul]
    rw [mul_smul_comm]
  · simp

lemma formalHessianCoefficient_pair_sum (m : ℕ) (i j : Fin N) :
    formalHessianCoefficient m i j=
      ∑ A : SYKEdge.KSet N 4, ∑ k : Fin N, ∑ l : Fin N,
        if A.1={i,j,k,l} then X A*formalPairFlow m k l else 0 := by
  rw [formalHessianCoefficient_expand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : i∈A.1 ∧ j∈A.1.erase i
  · simp only [h,ite_true]
    have hc : ((A.1.erase i).erase j).card=2 := by
      rw [Finset.card_erase_of_mem h.2,Finset.card_erase_of_mem h.1,A.2]
    obtain ⟨a,b,hab,hr⟩ := Finset.card_eq_two.mp hc
    rw [quartic_pair_sum A i j a b h.1 h.2 hab hr _
      (by rw [formalPairFlow_symmetric m a b])]
    have hp : formalWordProduct ((A.1.erase i).erase j)=X (Sum.inr a)*X (Sum.inr b) := by
      simp [formalWordProduct,hr,hab]
    rw [hp]
    change 2*(X A*formalPairFlow m a b)=2 • (X A*formalPairFlow m a b)
    simp [two_mul,two_nsmul]
  · rw [if_neg h,mul_zero,quartic_pair_sum_zero A i j h]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def couplingOrderSign (i j k l : Fin N) : ℝ := (-1)^(
  (if j < i then 1 else 0)+(if k < i then 1 else 0)+(if l < i then 1 else 0)+
  (if k < j then 1 else 0)+(if l < j then 1 else 0)+(if l < k then 1 else 0))
lemma couplingOrderSign_abs (i j k l : Fin N) : |couplingOrderSign i j k l|=1 := by
  simp [couplingOrderSign]

def mPathPhase (r s : ℕ) (b : Fin 3) : ℝ :=
  if b=0 then 1 else if b=1 then -(-1)^s else (-1)^r*(-1)^s
lemma mPathPhase_abs (r s : ℕ) (b : Fin 3) : |mPathPhase r s b|=1 := by
  unfold mPathPhase
  split_ifs <;> simp

def mPathWords (t u : InteractionPath N) (b : Fin 3) : List (Fin N) × List (Fin N) :=
  if b=0 then (t.word++u.word,[]) else if b=1 then (t.word,u.word) else ([],t.word++u.word)

def mPathWeight (r s : ℕ) (t u : InteractionPath N) : ℝ :=
  ((2 : ℝ)^r/(r.factorial : ℝ))*((2 : ℝ)^s/(s.factorial : ℝ))/3*|t.sign| * |u.sign|

lemma mPathWeight_nonneg (r s : ℕ) (t u : InteractionPath N) : 0 ≤ mPathWeight r s t u := by
  unfold mPathWeight
  positivity

lemma mPathOperator_norm (Q : Model N) (r s : ℕ) (i j k l : Fin N)
    (t u : InteractionPath N) (b : Fin 3) :
    ‖((((2 : ℝ)^r/(r.factorial : ℝ))*((2 : ℝ)^s/(s.factorial : ℝ))/3*
      t.sign*u.sign*couplingOrderSign i j k l*mPathPhase r s b : ℝ) : ℂ) •
      super (fun X ↦ cliffordWord Q (mPathWords t u b).1*X*
        cliffordWord Q (mPathWords t u b).2)‖=mPathWeight r s t u := by
  rw [norm_smul,norm_super_clifford_words,Complex.norm_real,Real.norm_eq_abs]
  simp only [abs_mul,couplingOrderSign_abs,mPathPhase_abs,mul_one]
  rw [abs_of_nonneg (by positivity : 0≤((2 : ℝ)^r/(r.factorial : ℝ))*((2 : ℝ)^s/(s.factorial : ℝ))/3)]
  rfl

def mPathTerm (Q : Model N) (r s : ℕ) (i j k l : Fin N) (A : SYKEdge.KSet N 4)
    (t u : InteractionPath N) (b : Fin 3) :
    GaussianBlockTerm N (Fin N) (SiteHilbert N×SiteHilbert N) :=
  ⟨A::(t.couplings++u.couplings),
    Matrix.kronecker (Matrix.single i j (1 : ℂ))
      (if A.1={i,j,k,l} then
        ((((2 : ℝ)^r/(r.factorial : ℝ))*((2 : ℝ)^s/(s.factorial : ℝ))/3*
          t.sign*u.sign*couplingOrderSign i j k l*mPathPhase r s b : ℝ) : ℂ) •
          super (fun X ↦ cliffordWord Q (mPathWords t u b).1*X*
            cliffordWord Q (mPathWords t u b).2) else 0),
    Matrix.single i j (if A.1={i,j,k,l} then mPathWeight r s t u else 0),
    by
      letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
      apply blockDominated_single_kronecker
      split_ifs
      · exact le_of_eq (mPathOperator_norm Q r s i j k l t u b)
      · simp⟩

def mPathPolynomial (Q : Model N) (m : ℕ) :
    GaussianBlockPolynomial.Poly N (Fin N) (SiteHilbert N×SiteHilbert N) :=
  (Finset.range (m+1)).toList.flatMap (fun r ↦
    (Finset.univ.toList : List (Fin N×Fin N×Fin N×Fin N)).flatMap (fun z ↦
      (Finset.univ.toList : List (SYKEdge.KSet N 4)).flatMap (fun A ↦
        (interactionPaths z.2.2.1 r).flatMap (fun t ↦
          (interactionPaths z.2.2.2 (m-r)).flatMap (fun u ↦
            (Finset.univ.toList : List (Fin 3)).map
              (mPathTerm Q r (m-r) z.1 z.2.1 z.2.2.1 z.2.2.2 A t u))))))

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
open Matrix MvPolynomial
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma finite_list_sum {α M : Type} [DecidableEq α] [AddCommMonoid M] (s : Finset α) (f : α → M) :
    (s.toList.map f).sum=∑ a∈s,f a := by
  rw [← List.sum_toFinset f (Finset.nodup_toList _)]
  simp

lemma list_sum_if_const {α M : Type} [AddMonoid M] (l : List α) (P : Prop) [Decidable P] (f : α → M) :
    (l.map (fun a ↦ if P then f a else 0)).sum=if P then (l.map f).sum else 0 := by
  by_cases h : P <;> simp [h]
lemma finset_sum_if_const {α M : Type} [AddCommMonoid M] (s : Finset α) (P : Prop) [Decidable P] (f : α → M) :
    (∑ a∈s, if P then f a else 0)=if P then (∑ a∈s,f a) else 0 := by
  by_cases h : P <;> simp [h]

lemma formalGammaCoefficient_eval_paths (m : ℕ) (k : Fin N) (w : Disorder N) :
    MvPolynomial.eval w (formalGammaCoefficient m k)=((2 : ℝ)^m/(m.factorial : ℝ))*
      ((interactionPaths k m).map (fun t ↦ couplingMonomial t.couplings w)).sum := by
  rw [formalGammaCoefficient_eval,classicalIterate_paths]
  simp only [InteractionPath.reval,realWord_ones,mul_one]
  ring

lemma mPathTerm_reval (Q : Model N) (w : Disorder N) (r s : ℕ) (i j k l a c : Fin N)
    (A : SYKEdge.KSet N 4) (t u : InteractionPath N) (b : Fin 3) :
    (mPathTerm Q r s i j k l A t u b).reval w a c=
      if a=i ∧ c=j then couplingMonomial (A::(t.couplings++u.couplings)) w*
        (if A.1={i,j,k,l} then mPathWeight r s t u else 0) else 0 := by
  simp only [mPathTerm,GaussianBlockTerm.reval,Matrix.smul_apply,smul_eq_mul,Matrix.single_apply]
  by_cases ha : a=i <;> by_cases hc : c=j <;> simp_all [eq_comm]

lemma mPathClassical_path_pair (w : Disorder N) (r s : ℕ) (k l : Fin N) (A : SYKEdge.KSet N 4) :
    (((interactionPaths k r).map (fun t ↦ ((interactionPaths l s).map
      (fun u ↦ couplingMonomial (A::(t.couplings++u.couplings)) w*
        (3*mPathWeight r s t u))).sum)).sum)=
      w A*MvPolynomial.eval w (formalGammaCoefficient r k)*MvPolynomial.eval w (formalGammaCoefficient s l) := by
  calc
    _=(((interactionPaths k r).map (fun t ↦ ((interactionPaths l s).map
      (fun u ↦ (w A*((2 : ℝ)^r/(r.factorial : ℝ))*couplingMonomial t.couplings w)*
        (((2 : ℝ)^s/(s.factorial : ℝ))*couplingMonomial u.couplings w))).sum)).sum) := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      apply congrArg List.sum
      apply List.map_congr_left
      intro u hu
      have ht' := (interactionPath_lengths k r t ht).2.2
      have hu' := (interactionPath_lengths l s u hu).2.2
      simp only [mPathWeight,ht',hu',couplingMonomial_cons,couplingMonomial_append,mul_one]
      ring
    _=_ := by
      simp only [List.sum_map_mul_left]
      rw [List.sum_map_mul_right]
      simp only [List.sum_map_mul_left]
      rw [formalGammaCoefficient_eval_paths,formalGammaCoefficient_eval_paths]
      ring

lemma mPathPolynomial_reval_expand (Q : Model N) (w : Disorder N) (m : ℕ) (a c : Fin N) :
    GaussianBlockPolynomial.reval (mPathPolynomial Q m) w a c=
      ∑ r∈Finset.range (m+1), ∑ k : Fin N, ∑ l : Fin N, ∑ A : SYKEdge.KSet N 4,
        if A.1={a,c,k,l} then w A*MvPolynomial.eval w (formalGammaCoefficient r k)*
          MvPolynomial.eval w (formalGammaCoefficient (m-r) l) else 0 := by
  unfold GaussianBlockPolynomial.reval mPathPolynomial
  rw [matrix_list_sum_apply]
  simp only [list_sum_flatMap,List.map_map,Function.comp_def,mPathTerm_reval,list_sum_if_const]
  simp only [all_list_sum,finite_list_sum,Fintype.sum_prod_type]
  simp only [finset_sum_if_const]
  simp only [ite_and]
  simp only [finset_sum_if_const]
  simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A.1={a,c,k,l}
  · simp only [h,ite_true]
    convert mPathClassical_path_pair w r (m-r) k l A using 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    apply congrArg List.sum
    apply List.map_congr_left
    intro u hu
    simp only [Fin.sum_univ_succ]
    ring
  · simp [h]

lemma formalHessianCoefficient_eval_expand (w : Disorder N) (m : ℕ) (i j : Fin N) :
    MvPolynomial.eval w (formalHessianCoefficient m i j)=
      ∑ r∈Finset.range (m+1), ∑ k : Fin N, ∑ l : Fin N, ∑ A : SYKEdge.KSet N 4,
        if A.1={i,j,k,l} then w A*MvPolynomial.eval w (formalGammaCoefficient r k)*
          MvPolynomial.eval w (formalGammaCoefficient (m-r) l) else 0 := by
  rw [formalHessianCoefficient_pair_sum]
  simp only [map_sum]
  have ht (A : SYKEdge.KSet N 4) (k l : Fin N) :
      MvPolynomial.eval w (if A.1={i,j,k,l} then X A*formalPairFlow m k l else 0)=
      ∑ r∈Finset.range (m+1), if A.1={i,j,k,l} then w A*
        MvPolynomial.eval w (formalGammaCoefficient r k)*
          MvPolynomial.eval w (formalGammaCoefficient (m-r) l) else 0 := by
    by_cases h : A.1={i,j,k,l}
    · rw [if_pos h,map_mul,formalPairFlow_convolution,map_sum]
      simp only [MvPolynomial.eval_X,map_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [h,ite_true,mul_assoc]
    · simp [h]
  simp_rw [ht]
  calc
    _=∑ A : SYKEdge.KSet N 4, ∑ k : Fin N, ∑ r∈Finset.range (m+1), ∑ l : Fin N,
        if A.1={i,j,k,l} then w A*MvPolynomial.eval w (formalGammaCoefficient r k)*
          MvPolynomial.eval w (formalGammaCoefficient (m-r) l) else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _=∑ A : SYKEdge.KSet N 4, ∑ r∈Finset.range (m+1), ∑ k : Fin N, ∑ l : Fin N,
        if A.1={i,j,k,l} then w A*MvPolynomial.eval w (formalGammaCoefficient r k)*
          MvPolynomial.eval w (formalGammaCoefficient (m-r) l) else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.sum_comm]
    _=∑ r∈Finset.range (m+1), ∑ A : SYKEdge.KSet N 4, ∑ k : Fin N, ∑ l : Fin N,
        if A.1={i,j,k,l} then w A*MvPolynomial.eval w (formalGammaCoefficient r k)*
          MvPolynomial.eval w (formalGammaCoefficient (m-r) l) else 0 := by rw [Finset.sum_comm]
    _=_ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]

lemma mPathPolynomial_reval (Q : Model N) (w : Disorder N) (m : ℕ) :
    GaussianBlockPolynomial.reval (mPathPolynomial Q m) w=
      (Matrix.of (formalHessianCoefficient m)).map (MvPolynomial.eval w) := by
  ext i j
  rw [mPathPolynomial_reval_expand,Matrix.map_apply,Matrix.of_apply,formalHessianCoefficient_eval_expand]

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma couplingOrderSign_fiber (w : Disorder N) (i j k l : Fin N) :
    coupling w i j k l=∑ A : SYKEdge.KSet N 4,
      if A.1={i,j,k,l} then couplingOrderSign i j k l*w A else 0 := by
  by_cases h : ({i,j,k,l} : Finset (Fin N)).card=4
  · let A : SYKEdge.KSet N 4 := ⟨{i,j,k,l},h⟩
    rw [Finset.sum_eq_single A]
    · rw [coupling_explicit]
      simp [h,A,couplingOrderSign]
    · intro B hB hBA
      rw [if_neg]
      exact fun he ↦ hBA (Subtype.ext he)
    · simp
  · have he (A : SYKEdge.KSet N 4) : A.1≠{i,j,k,l} := by
      intro hA
      apply h
      rw [← hA]
      exact A.2
    simp [coupling_explicit,h,he]

lemma mPath_three_actions (Q : Model N) (r s : ℕ) (t u : InteractionPath N) (X : Mat (SiteHilbert N)) :
    (∑ b : Fin 3, (mPathPhase r s b : ℂ) •
      (cliffordWord Q (mPathWords t u b).1*X*cliffordWord Q (mPathWords t u b).2))=
    cliffordWord Q t.word*cliffordWord Q u.word*X-
      (-1 : ℂ)^s • (cliffordWord Q t.word*X*cliffordWord Q u.word)+
      ((-1 : ℂ)^r*(-1 : ℂ)^s) • (X*cliffordWord Q t.word*cliffordWord Q u.word) := by
  simp only [Fin.sum_univ_succ]
  norm_num [mPathPhase,mPathWords,cliffordWord_append,cliffordWord,List.map_nil,List.prod_nil,
    Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_pow,mul_assoc]
  have h20 : (2 : Fin 3)≠0 := by decide
  have h21 : (2 : Fin 3)≠1 := by decide
  simp only [h20,h21,ite_false,List.map_append,List.prod_append,List.map_nil,List.prod_nil,one_mul,mul_one,mul_assoc]
  module

def mPairLinear {ι : Type} [Fintype ι] [DecidableEq ι] (r s : ℕ) :
    Mat ι →ₗ[ℂ] Mat ι →ₗ[ℂ] Super ι :=
  LinearMap.mk₂ ℂ (fun A C ↦ super (fun X ↦ A*C*X-
    (-1 : ℂ)^s • (A*X*C)+((-1 : ℂ)^r*(-1 : ℂ)^s) • (X*A*C)))
    (by
      intro A B C
      ext a b
      simp only [super,add_mul,mul_add,smul_add,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply]
      ring)
    (by
      intro c A C
      ext a b
      simp only [super,smul_mul_assoc,mul_smul_comm,smul_sub,smul_add,smul_smul,
        Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply]
      ring)
    (by
      intro A B C
      ext a b
      simp only [super,add_mul,mul_add,smul_add,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply]
      ring)
    (by
      intro c A C
      ext a b
      simp only [super,smul_mul_assoc,mul_smul_comm,smul_sub,smul_add,smul_smul,
        Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply]
      ring)

lemma mPairLinear_apply {ι : Type} [Fintype ι] [DecidableEq ι] (r s : ℕ) (A C : Mat ι) :
    mPairLinear r s A C=super (fun X ↦ A*C*X-
      (-1 : ℂ)^s • (A*X*C)+((-1 : ℂ)^r*(-1 : ℂ)^s) • (X*A*C)) := rfl

lemma linearPair_list_sums {α β M P V : Type} [AddCommMonoid M] [Module ℂ M]
    [AddCommMonoid P] [Module ℂ P] [AddCommMonoid V] [Module ℂ V]
    (B : M →ₗ[ℂ] P →ₗ[ℂ] V) (l : List α) (k : List β) (f : α → M) (g : β → P) :
    B (l.map f).sum (k.map g).sum=
      (l.map (fun a ↦ (k.map (fun b ↦ B (f a) (g b))).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,map_add,LinearMap.add_apply,ih]
    congr 1
    simpa only [List.map_map,Function.comp_def] using! map_list_sum (B (f a)) (k.map g)

lemma mBlock_gamma_pair (Q : Model N) (w : Disorder N) (r s : ℕ) (i j : Fin N) :
    mBlock w (gammaCoefficient Q w r) (fun k ↦ (-1 : ℂ)^r • gammaCoefficient Q w r k)
      (gammaCoefficient Q w s) (fun l ↦ (-1 : ℂ)^s • gammaCoefficient Q w s l) i j=
      (1/3 : ℂ) • ∑ k, ∑ l, (coupling w i j k l : ℂ) •
        mPairLinear r s (gammaCoefficient Q w r k) (gammaCoefficient Q w s l) := by
  ext a b
  simp only [mBlock,super,mPairLinear_apply,Matrix.smul_apply,Matrix.sum_apply,
    mul_smul_comm,smul_mul_assoc,smul_smul,smul_add,smul_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma mPair_gamma_paths (Q : Model N) (w : Disorder N) (r s : ℕ) (k l : Fin N) :
    mPairLinear r s (gammaCoefficient Q w r k) (gammaCoefficient Q w s l)=
      (((2 : ℂ)^r/(r.factorial : ℂ))*((2 : ℂ)^s/(s.factorial : ℂ))) •
      ((interactionPaths k r).map (fun t ↦ ((interactionPaths l s).map
        (fun u ↦ (((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ)*
          ((u.sign*couplingMonomial u.couplings w : ℝ) : ℂ)) •
          mPairLinear r s (cliffordWord Q t.word) (cliffordWord Q u.word))).sum)).sum := by
  rw [gammaCoefficient_paths,gammaCoefficient_paths]
  calc
    _=(((2 : ℂ)^r/(r.factorial : ℂ))*((2 : ℂ)^s/(s.factorial : ℂ))) •
        mPairLinear r s ((interactionPaths k r).map (fun t ↦ t.qeval Q w)).sum
          ((interactionPaths l s).map (fun u ↦ u.qeval Q w)).sum := by
      simp only [map_smul,LinearMap.smul_apply,smul_smul]
      congr 1
      ring
    _=_ := by
      congr 1
      rw [linearPair_list_sums]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      apply congrArg List.sum
      apply List.map_congr_left
      intro u hu
      simp only [InteractionPath.qeval,map_smul,LinearMap.smul_apply,smul_smul]
      congr 1
      ring

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma mPath_three_supers (Q : Model N) (r s : ℕ) (t u : InteractionPath N) :
    (∑ b : Fin 3, (mPathPhase r s b : ℂ) •
      super (fun X ↦ cliffordWord Q (mPathWords t u b).1*X*cliffordWord Q (mPathWords t u b).2))=
    mPairLinear r s (cliffordWord Q t.word) (cliffordWord Q u.word) := by
  ext a b
  have hh := congrArg (fun X ↦ X a.1 a.2)
    (mPath_three_actions Q r s t u (Matrix.single b.1 b.2 1))
  simpa only [mPairLinear_apply,super,Matrix.sum_apply,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply] using hh

lemma mPathTerm_qeval_block (Q : Model N) (w : Disorder N) (r s : ℕ) (i j k l a c : Fin N)
    (A : SYKEdge.KSet N 4) (t u : InteractionPath N) (b : Fin 3) :
    subblock ((mPathTerm Q r s i j k l A t u b).qeval w) a c=
      if a=i ∧ c=j then (couplingMonomial (A::(t.couplings++u.couplings)) w : ℂ) •
        (if A.1={i,j,k,l} then
          ((((2 : ℝ)^r/(r.factorial : ℝ))*((2 : ℝ)^s/(s.factorial : ℝ))/3*
            t.sign*u.sign*couplingOrderSign i j k l*mPathPhase r s b : ℝ) : ℂ) •
            super (fun X ↦ cliffordWord Q (mPathWords t u b).1*X*
              cliffordWord Q (mPathWords t u b).2) else 0) else 0 := by
  letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
  change subblock (couplingMonomial (A::(t.couplings++u.couplings)) w •
    Matrix.kronecker (Matrix.single i j (1 : ℂ)) _) a c=_
  rw [subblock_real_smul,subblock_single_kronecker]
  by_cases h : a=i ∧ c=j <;> simp [h]

lemma mPathTerm_qeval_branches (Q : Model N) (w : Disorder N) (r s : ℕ) (i j k l a c : Fin N)
    (A : SYKEdge.KSet N 4) (t u : InteractionPath N) :
    (∑ b : Fin 3, subblock ((mPathTerm Q r s i j k l A t u b).qeval w) a c)=
      if a=i ∧ c=j then
        (if A.1={i,j,k,l} then ((couplingOrderSign i j k l*w A : ℝ) : ℂ) •
          ((1/3 : ℂ) • mPairLinear r s
            ((((2 : ℂ)^r/(r.factorial : ℂ))) • t.qeval Q w)
            ((((2 : ℂ)^s/(s.factorial : ℂ))) • u.qeval Q w)) else 0) else 0 := by
  simp only [mPathTerm_qeval_block]
  by_cases hr : a=i ∧ c=j
  · simp only [hr,true_and,and_true,ite_true]
    by_cases hA : A.1={i,j,k,l}
    · simp only [hA,ite_true]
      have he (b : Fin 3) :
          (couplingMonomial (A::(t.couplings++u.couplings)) w : ℂ) •
            (((((2 : ℝ)^r/(r.factorial : ℝ))*((2 : ℝ)^s/(s.factorial : ℝ))/3*
              t.sign*u.sign*couplingOrderSign i j k l*mPathPhase r s b : ℝ) : ℂ) •
              super (fun X ↦ cliffordWord Q (mPathWords t u b).1*X*
                cliffordWord Q (mPathWords t u b).2))=
          (((couplingOrderSign i j k l*w A : ℝ) : ℂ)*(1/3)*
            (((2 : ℂ)^r/(r.factorial : ℂ))*((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ))*
            (((2 : ℂ)^s/(s.factorial : ℂ))*((u.sign*couplingMonomial u.couplings w : ℝ) : ℂ))) •
            ((mPathPhase r s b : ℂ) • super (fun X ↦ cliffordWord Q (mPathWords t u b).1*X*
                cliffordWord Q (mPathWords t u b).2)) := by
        simp only [smul_smul,couplingMonomial_cons,couplingMonomial_append,Complex.ofReal_mul,
          Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_ofNat]
        congr 1
        ring
      simp_rw [he]
      rw [← Finset.smul_sum,mPath_three_supers]
      simp only [InteractionPath.qeval,map_smul,LinearMap.smul_apply,smul_smul]
      congr 1
      ring
    · simp [hA]
  · simp [hr]

lemma mPath_pair_sum (Q : Model N) (w : Disorder N) (r s : ℕ) (k l : Fin N) :
    ((interactionPaths k r).map (fun t ↦ ((interactionPaths l s).map (fun u ↦
      mPairLinear r s (((2 : ℂ)^r/(r.factorial : ℂ)) • t.qeval Q w)
        (((2 : ℂ)^s/(s.factorial : ℂ)) • u.qeval Q w))).sum)).sum=
    mPairLinear r s (gammaCoefficient Q w r k) (gammaCoefficient Q w s l) := by
  rw [← linearPair_list_sums,list_sum_smul_left,list_sum_smul_left,
    ← gammaCoefficient_paths,← gammaCoefficient_paths]

lemma mPathPolynomial_qeval_block (Q : Model N) (w : Disorder N) (m : ℕ) (a c : Fin N) :
    subblock (GaussianBlockPolynomial.qeval (mPathPolynomial Q m) w) a c=
      ∑ r∈Finset.range (m+1), (1/3 : ℂ) • ∑ k : Fin N, ∑ l : Fin N,
        (coupling w a c k l : ℂ) •
          mPairLinear r (m-r) (gammaCoefficient Q w r k) (gammaCoefficient Q w (m-r) l) := by
  unfold GaussianBlockPolynomial.qeval mPathPolynomial
  rw [subblock_list_sum]
  simp only [list_sum_flatMap,List.map_map,Function.comp_def,all_list_sum,mPathTerm_qeval_branches]
  simp only [list_sum_if_const,list_sum_smul_left,mPath_pair_sum]
  simp only [finite_list_sum,Fintype.sum_prod_type,finset_sum_if_const]
  simp only [ite_and]
  simp only [finset_sum_if_const]
  simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [couplingOrderSign_fiber]
  simp only [Complex.ofReal_sum,Finset.sum_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A.1={a,c,k,l}
  · simp only [h,ite_true]
    rw [smul_comm]
  · simp [h]

lemma mPathPolynomial_qeval (Q : Model N) (w : Disorder N) (m : ℕ) :
    GaussianBlockPolynomial.qeval (mPathPolynomial Q m) w=mCoefficient Q w m := by
  ext a b
  have hh := mPathPolynomial_qeval_block Q w m a.1 b.1
  simp only [← mBlock_gamma_pair] at hh
  have he := congrArg (fun X ↦ X a.2 b.2) hh
  simpa only [subblock,Matrix.of_apply,Matrix.sum_apply,mCoefficient] using he

end SYKFastMix.FastMixing


set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
open Matrix MvPolynomial MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma formalHessianCoefficient_nonneg (m : ℕ) (i j : Fin N) :
    CoeffNonneg (formalHessianCoefficient m i j) := by
  rw [formalHessianCoefficient_pair_sum]
  apply CoeffNonneg.sum
  intro A hA
  apply CoeffNonneg.sum
  intro k hk
  apply CoeffNonneg.sum
  intro l hl
  split_ifs
  · exact (coeffNonneg_X _).mul (initialOne_nonneg _
      (dividedIterate_formal_nonneg ((coeffNonneg_X _).mul (coeffNonneg_X _)) m))
  · exact coeffNonneg_zero

lemma real_matrix_moment_smul {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (c : ℝ) (p : ℕ) :
    Matrix.trace (((c • A).transpose*(c • A))^p)=
      c^(2*p)*Matrix.trace ((A.transpose*A)^p) := by
  rw [Matrix.transpose_smul,smul_mul_assoc,mul_smul_comm,smul_smul,smul_pow,Matrix.trace_smul]
  simp only [smul_eq_mul]
  congr 1
  rw [mul_pow]
  ring

def formalJacobianMatrix (m : ℕ) : Matrix (Fin N) (Fin N) (MvPolynomial (SYKEdge.KSet N 4) ℝ) :=
  Matrix.of (formalJacobianCoefficient m)

lemma formalJacobianMatrix_eval_complex (m : ℕ) (w : Disorder N) :
    ((formalJacobianMatrix m).map (MvPolynomial.eval w)).map (algebraMap ℝ ℂ)=
      classicalCoefficient w m (fun _ ↦ 1) := by
  ext i j
  simp only [formalJacobianMatrix,Matrix.map_apply,Matrix.of_apply,formalJacobianCoefficient_eval,classicalCoefficient]
  change ((coordinateDerivative (classicalIterate w m i) j (fun _ ↦ 1)/(m.factorial : ℝ) : ℝ) : ℂ)=_
  simp only [Complex.ofReal_div,Complex.ofReal_natCast]

lemma lemma12_proof (Q : Model N) (m p : ℕ) (hp : 1≤p) :
  Integrable (fun w => traceMoment p (mCoefficient Q w m)) (disorderLaw Q) ∧
  Integrable (fun w => traceMoment p (classicalCoefficient w (m+1) (fun _ => 1))) (disorderLaw Q) ∧
  (1 / ((2 ^ (N / 2) : ℝ)^2)) * (∫ w, traceMoment p (mCoefficient Q w m) ∂disorderLaw Q) ≤
    ((m+1 : ℝ)^(2*p)) *
      (∫ w, traceMoment p (classicalCoefficient w (m+1) (fun _ => 1)) ∂disorderLaw Q) := by
  letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
  obtain ⟨hiq,hir,hc⟩ := GaussianBlockPolynomial.moment_comparison Q (mPathPolynomial Q m) p
  simp only [mPathPolynomial_qeval,mPathPolynomial_reval] at hiq hir hc
  let A := Matrix.of (formalHessianCoefficient (N := N) m)
  let F := formalJacobianMatrix (N := N) (m+1)
  let B : Matrix (Fin N) (Fin N) (MvPolynomial (SYKEdge.KSet N 4) ℝ) := (m+1 : ℝ) • F
  have hA : MatrixCoeffNonneg A := formalHessianCoefficient_nonneg m
  have hF : MatrixCoeffNonneg F := formalJacobianCoefficient_nonneg (m+1)
  have hB : MatrixCoeffNonneg B := fun i j ↦ (hF i j).real_smul _ (by positivity)
  have hAB : MatrixCoeffLE A B := formalHessianCoefficient_bound m
  have hmono := matrix_polynomial_moment_mono Q A B hAB hA hB p
  have hBeval (w : Disorder N) : B.map (MvPolynomial.eval w)=(m+1 : ℝ) • F.map (MvPolynomial.eval w) := by
    ext i j
    change MvPolynomial.eval w ((m+1 : ℝ) • F i j)=(m+1 : ℝ)*MvPolynomial.eval w (F i j)
    rw [← C_mul',map_mul]
    simp
  have hmoment (w : Disorder N) : Matrix.trace (((B.map (MvPolynomial.eval w)).transpose*
      B.map (MvPolynomial.eval w))^p)=
      (m+1 : ℝ)^(2*p)*traceMoment p (classicalCoefficient w (m+1) (fun _ ↦ 1)) := by
    rw [hBeval,real_matrix_moment_smul]
    congr 1
    rw [← traceMoment_real_matrix,formalJacobianMatrix_eval_complex]
  simp only [hmoment] at hmono
  rw [integral_const_mul] at hmono
  have hiF := (lemma_9 Q (m+1) p (by omega) hp).2.1
  refine ⟨hiq,hiF,?_⟩
  have hcard : (Fintype.card (SiteHilbert N×SiteHilbert N) : ℝ)=((2 : ℝ)^(N/2))^2 := by
    simp [SiteHilbert,pow_two]
  rw [hcard] at hc
  have hd : (0 : ℝ)<((2 : ℝ)^(N/2))^2 := by positivity
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hd).mpr
  exact hc.trans (by simpa only [mul_comm,mul_left_comm,mul_assoc] using
    mul_le_mul_of_nonneg_left hmono (le_of_lt hd))

end SYKFastMix.FastMixing

open SYKFastMix.FastMixing
theorem solution {N : ℕ} (Q : Model N) (m p : ℕ) (hp : 1 ≤ p) :
  Integrable (fun w => traceMoment p (mCoefficient Q w m)) (disorderLaw Q) ∧
  Integrable (fun w => traceMoment p (classicalCoefficient w (m+1) (fun _ => 1))) (disorderLaw Q) ∧
  (1 / ((2 ^ (N / 2) : ℝ)^2)) * (∫ w, traceMoment p (mCoefficient Q w m) ∂disorderLaw Q) ≤
    ((m : ℝ)+1)^(2*p) * (∫ w, traceMoment p (classicalCoefficient w (m+1) (fun _ => 1)) ∂disorderLaw Q) := lemma12_proof Q m p hp
