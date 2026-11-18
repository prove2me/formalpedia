-- Prove2me | solution 1 for SYKFastMix.FastMixing.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:57:52.33067+00:00
-- url     : https://prove2.me/submissions/acc858ec-b454-4287-8b87-7091c16a79ec

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

section
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
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : NormedAlgebra ℚ (Mat ι) := .restrictScalars ℚ ℂ (Mat ι)

lemma mexp_smul_add (H : Mat ι) (a b : ℂ) :
    mexp (a • H) * mexp (b • H) = mexp ((a+b) • H) := by
  have hc : Commute (a • H) (b • H) := by
    change (a • H) * (b • H) = (b • H) * (a • H)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm a b]
  exact (NormedSpace.exp_add_of_commute (𝔸 := Mat ι) hc).symm.trans (by rw [← add_smul]; rfl)

lemma mexp_smul_cancel (H : Mat ι) (a : ℂ) : mexp (a • H) * mexp ((-a) • H) = 1 := by
  rw [mexp_smul_add]
  simp [mexp]

lemma mexp_hermitian (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    (mexp ((a : ℂ) • H)).IsHermitian := by
  exact (hH.smul (by simp [IsSelfAdjoint])).exp


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

lemma gamma_mul_word {N : ℕ} (Q : Model N) (j : Fin N) (l : List (Fin N)) :
    Q.γ j * (l.map Q.γ).prod =
      (-1 : ℂ)^((l.filter (· != j)).length) • ((l.map Q.γ).prod * Q.γ j) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    let c : ℂ := if i=j then 1 else -1
    have hs : Q.γ j * Q.γ i = c • (Q.γ i * Q.γ j) := by
      by_cases hij : i=j
      · simp [c, hij]
      · simpa [c, hij] using Q.car.anticomm j i (Ne.symm hij)
    have hcount : (-1 : ℂ)^(((i::l).filter (· != j)).length) = c * (-1 : ℂ)^((l.filter (· != j)).length) := by
      by_cases hij : i=j <;> simp [c, hij, pow_succ, mul_comm]
    simp only [List.map_cons, List.prod_cons]
    calc
      Q.γ j * (Q.γ i * (l.map Q.γ).prod) = (Q.γ j * Q.γ i) * (l.map Q.γ).prod := by rw [mul_assoc]
      _ = c • (Q.γ i * (Q.γ j * (l.map Q.γ).prod)) := by rw [hs, smul_mul_assoc, mul_assoc]
      _ = c • (Q.γ i * ((-1 : ℂ)^((l.filter (· != j)).length) • ((l.map Q.γ).prod * Q.γ j))) := by rw [ih]
      _ = (-1 : ℂ)^(((i::l).filter (· != j)).length) • ((Q.γ i * (l.map Q.γ).prod) * Q.γ j) := by
        rw [mul_smul_comm, smul_smul, ← hcount, mul_assoc]

lemma rawString_character {N : ℕ} (Q : Model N) (S : Finset (Fin N)) (j : Fin N) :
    Q.γ j * rawString Q S * Q.γ j = (-1 : ℂ)^((S.erase j).card) • rawString Q S := by
  have hlen : ((S.sort (· ≤ ·)).filter (· != j)).length = (S.erase j).card := by
    have hn := (S.sort_nodup (· ≤ ·)).filter (· != j)
    have he : ((S.sort (· ≤ ·)).filter (· != j)).toFinset = S.erase j := by
      ext k
      simp [and_comm]
    rw [← he]
    exact (List.toFinset_card_of_nodup hn).symm
  unfold rawString
  rw [gamma_mul_word, smul_mul_assoc, mul_assoc, Q.car.sq, mul_one, hlen]


end SYKFastMix.FastMixing
end

section
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
end

section
namespace SYKFastMix.FastMixing

lemma sum_triple_restrict {α E : Type} [Fintype α] [DecidableEq α] [AddCommMonoid E]
    (S : Finset α) (f : α → α → α → E)
    (hf : ∀ i j k, i∉S ∨ j∉S ∨ k∉S → f i j k=0) :
    (∑ i, ∑ j, ∑ k, f i j k)=∑ i∈S, ∑ j∈S, ∑ k∈S, f i j k := by
  have houter : (∑ i, ∑ j, ∑ k, f i j k)=∑ i∈S, ∑ j, ∑ k, f i j k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i hi hnot
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    exact hf i j k (Or.inl hnot)
  rw [houter]
  apply Finset.sum_congr rfl
  intro i hi
  have hmiddle : (∑ j, ∑ k, f i j k)=∑ j∈S, ∑ k, f i j k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j hj hnot
    apply Finset.sum_eq_zero
    intro k hk
    exact hf i j k (Or.inr (Or.inl hnot))
  rw [hmiddle]
  apply Finset.sum_congr rfl
  intro j hj
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro k hk hnot
  exact hf i j k (Or.inr (Or.inr hnot))

variable {N : ℕ}

def quarticFiber (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i j k l : Fin N) : Mat (SiteHilbert N) :=
  if ({i,j,k,l} : Finset (Fin N))=A.1 then
    (coupling w i j k l : ℂ) • (Q.γ j*Q.γ k*Q.γ l) else 0

lemma coupling_fiber_sum (Q : Model N) (w : Disorder N) (i j k l : Fin N) :
    (coupling w i j k l : ℂ) • (Q.γ j*Q.γ k*Q.γ l)=
      ∑ A : SYKEdge.KSet N 4, quarticFiber Q w A i j k l := by
  by_cases h : ({i,j,k,l} : Finset (Fin N)).card=4
  · let A : SYKEdge.KSet N 4 := ⟨{i,j,k,l},h⟩
    rw [Finset.sum_eq_single A]
    · simp [quarticFiber,A]
    · intro B hB hBA
      unfold quarticFiber
      split_ifs with he
      · exact False.elim (hBA (Subtype.ext he.symm))
      · rfl
    · simp
  · have hc : coupling w i j k l=0 := by simp [coupling,h]
    simp [quarticFiber,hc]

lemma quarticFiber_restrict (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i : Fin N) :
    (∑ j, ∑ k, ∑ l, quarticFiber Q w A i j k l)=
      ∑ j∈A.1, ∑ k∈A.1, ∑ l∈A.1, quarticFiber Q w A i j k l := by
  apply sum_triple_restrict
  intro j k l hnot
  unfold quarticFiber
  split_ifs with he
  · exfalso
    have hj : j∈A.1 := by rw [← he]; simp
    have hk : k∈A.1 := by rw [← he]; simp
    have hl : l∈A.1 := by rw [← he]; simp
    rcases hnot with h|h|h <;> contradiction
  · rfl

lemma rawString_commutes_of_not_mem (Q : Model N) (A : SYKEdge.KSet N 4)
    (i : Fin N) (hi : i∉A.1) : Q.γ i*rawString Q A.1=rawString Q A.1*Q.γ i := by
  have hh := rawString_character Q A.1 i
  rw [Finset.erase_eq_of_notMem hi,A.2] at hh
  norm_num at hh
  have he := congrArg (fun M : Mat (SiteHilbert N) ↦ M*Q.γ i) hh
  simpa only [mul_assoc,Q.car.sq,mul_one] using he

lemma quarticFiber_zero_of_not_mem (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i : Fin N) (hi : i∉A.1) (j k l : Fin N) : quarticFiber Q w A i j k l=0 := by
  unfold quarticFiber
  split_ifs with he
  · exfalso
    apply hi
    rw [← he]
    simp
  · rfl

lemma rawString_anticommutes_of_mem (Q : Model N) (A : SYKEdge.KSet N 4)
    (i : Fin N) (hi : i∈A.1) : rawString Q A.1*Q.γ i=-(Q.γ i*rawString Q A.1) := by
  have hh := rawString_character Q A.1 i
  rw [Finset.card_erase_of_mem hi,A.2] at hh
  norm_num at hh
  have he := congrArg (fun M : Mat (SiteHilbert N) ↦ M*Q.γ i) hh
  simp only [mul_assoc,Q.car.sq,mul_one,neg_mul] at he
  have hn := congrArg Neg.neg he
  simpa only [neg_neg] using hn.symm


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma coupling_repeat01 (w : Disorder N) (i k l : Fin N) : coupling w i i k l=0 := by
  have h := coupling_swap01 w i i k l
  linarith

lemma coupling_repeat02 (w : Disorder N) (i j l : Fin N) : coupling w i j i l=0 := by
  rw [coupling_swap12,coupling_repeat01,neg_zero]

lemma coupling_repeat03 (w : Disorder N) (i j k : Fin N) : coupling w i j k i=0 := by
  rw [coupling_swap23,coupling_repeat02,neg_zero]

lemma coupling_repeat12 (w : Disorder N) (i j l : Fin N) : coupling w i j j l=0 := by
  have h := coupling_swap12 w i j j l
  linarith

lemma coupling_repeat13 (w : Disorder N) (i j k : Fin N) : coupling w i j k j=0 := by
  rw [coupling_swap23,coupling_repeat12,neg_zero]

lemma coupling_repeat23 (w : Disorder N) (i j k : Fin N) : coupling w i j k k=0 := by
  have h := coupling_swap23 w i j k k
  linarith

lemma quarticFiber_swap12 (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i j k l : Fin N) : quarticFiber Q w A i k j l=quarticFiber Q w A i j k l := by
  have hset : ({i,k,j,l} : Finset (Fin N))={i,j,k,l} := by ext x; simp [or_left_comm]
  unfold quarticFiber
  rw [hset]
  split_ifs
  · by_cases h : k=j
    · subst k
      rfl
    · rw [coupling_swap12,Q.car.anticomm k j h]
      simp only [Complex.ofReal_neg,neg_smul,neg_mul,smul_neg,neg_neg]
  · rfl

lemma quarticFiber_swap23 (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i j k l : Fin N) : quarticFiber Q w A i j l k=quarticFiber Q w A i j k l := by
  have hset : ({i,j,l,k} : Finset (Fin N))={i,j,k,l} := by ext x; simp [or_left_comm,or_comm,or_assoc]
  unfold quarticFiber
  rw [hset]
  split_ifs
  · by_cases h : l=k
    · subst l
      rfl
    · rw [coupling_swap23,mul_assoc (Q.γ j),Q.car.anticomm l k h]
      simp only [Complex.ofReal_neg,neg_smul,mul_neg,smul_neg,neg_neg,mul_assoc]
  · rfl

lemma quarticFiber_diag (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i j k l : Fin N) (h : i=j ∨ i=k ∨ i=l ∨ j=k ∨ j=l ∨ k=l) :
    quarticFiber Q w A i j k l=0 := by
  unfold quarticFiber
  split_ifs
  · rcases h with h|h|h|h|h|h
    · subst j; simp [coupling_repeat01]
    · subst k; simp [coupling_repeat02]
    · subst l; simp [coupling_repeat03]
    · subst k; simp [coupling_repeat12]
    · subst l; simp [coupling_repeat13]
    · subst l; simp [coupling_repeat23]
  · rfl

lemma sum_triple_three_symmetric {α E : Type} [DecidableEq α] [AddCommMonoid E]
    (f : α → α → α → E) (a b c : α) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hs1 : ∀ x y z, f y x z=f x y z) (hs2 : ∀ x y z, f x z y=f x y z)
    (hd : ∀ x y z, x=y ∨ x=z ∨ y=z → f x y z=0) :
    (∑ x∈({a,b,c} : Finset α), ∑ y∈({a,b,c} : Finset α), ∑ z∈({a,b,c} : Finset α), f x y z)=
      6 • f a b c := by
  have hbac : f b a c=f a b c := hs1 a b c
  have hacb : f a c b=f a b c := hs2 a b c
  have hbca : f b c a=f a b c := (hs2 b a c).trans hbac
  have hcab : f c a b=f a b c := (hs1 a c b).trans hacb
  have hcba : f c b a=f a b c := (hs1 b c a).trans hbca
  simp [Finset.sum_insert,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc,
    hbac,hacb,hbca,hcab,hcba,hd a a a (by simp),hd a a b (by simp),hd a a c (by simp),
    hd a b a (by simp),hd a b b (by simp),hd a c a (by simp),hd a c c (by simp),
    hd b a a (by simp),hd b a b (by simp),hd b b a (by simp),hd b b b (by simp),
    hd b b c (by simp),hd b c b (by simp),hd b c c (by simp),hd c a a (by simp),
    hd c a c (by simp),hd c b b (by simp),hd c b c (by simp),hd c c a (by simp),
    hd c c b (by simp),hd c c c (by simp)]
  abel


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma quarticFiber_restrict_erase (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i : Fin N) :
    (∑ j, ∑ k, ∑ l, quarticFiber Q w A i j k l)=
      ∑ j∈A.1.erase i, ∑ k∈A.1.erase i, ∑ l∈A.1.erase i, quarticFiber Q w A i j k l := by
  apply sum_triple_restrict
  intro j k l hnot
  rcases hnot with h|h|h
  · by_cases heq : j=i
    · subst j; exact quarticFiber_diag Q w A i i k l (by simp)
    have hnotA : j∉A.1 := by intro hj; exact h (Finset.mem_erase.mpr ⟨heq,hj⟩)
    unfold quarticFiber
    split_ifs with he
    · exfalso; apply hnotA; rw [← he]; simp
    · rfl
  · by_cases heq : k=i
    · subst k; exact quarticFiber_diag Q w A i j i l (by simp)
    have hnotA : k∉A.1 := by intro hk; exact h (Finset.mem_erase.mpr ⟨heq,hk⟩)
    unfold quarticFiber
    split_ifs with he
    · exfalso; apply hnotA; rw [← he]; simp
    · rfl
  · by_cases heq : l=i
    · subst l; exact quarticFiber_diag Q w A i j k i (by simp)
    have hnotA : l∉A.1 := by intro hl; exact h (Finset.mem_erase.mpr ⟨heq,hl⟩)
    unfold quarticFiber
    split_ifs with he
    · exfalso; apply hnotA; rw [← he]; simp
    · rfl

lemma quarticFiber_six (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i a b c : Fin N) (hA : A.1={i,a,b,c})
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    (∑ j, ∑ k, ∑ l, quarticFiber Q w A i j k l)=
      6 • ((coupling w i a b c : ℂ) • (Q.γ a*Q.γ b*Q.γ c)) := by
  have herase : A.1.erase i={a,b,c} := by
    rw [hA]
    ext x
    simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hne,h|h|h|h⟩
      · contradiction
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · intro h
      constructor
      · rcases h with rfl|rfl|rfl <;> exact Ne.symm (by assumption)
      · exact Or.inr h
  rw [quarticFiber_restrict_erase,herase]
  have he := sum_triple_three_symmetric (quarticFiber Q w A i) a b c hab hac hbc
    (quarticFiber_swap12 Q w A i) (quarticFiber_swap23 Q w A i)
    (fun x y z h ↦ quarticFiber_diag Q w A i x y z (by tauto))
  rw [he]
  simp only [quarticFiber,← hA,ite_true]

lemma coupling_increasing (w : Disorder N) (a b c d : Fin N)
    (hab : a<b) (hbc : b<c) (hcd : c<d) :
    coupling w a b c d=w ⟨{a,b,c,d},by simp [hab.ne,hbc.ne,hcd.ne,
      (hab.trans hbc).ne,(hbc.trans hcd).ne,((hab.trans hbc).trans hcd).ne]⟩ := by
  rw [coupling_explicit]
  have hac := hab.trans hbc
  have hbd := hbc.trans hcd
  have had := hac.trans hcd
  simp [hab.ne,hbc.ne,hcd.ne,hac.ne,hbd.ne,had.ne,
    not_lt_of_ge hab.le,not_lt_of_ge hbc.le,not_lt_of_ge hcd.le,
    not_lt_of_ge hac.le,not_lt_of_ge hbd.le,not_lt_of_ge had.le]

lemma quarticFiber_comm_from_contraction (Q : Model N) (w : Disorder N)
    (A : SYKEdge.KSet N 4) (i a b c : Fin N) (s : ℝ) (hA : A.1={i,a,b,c})
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hleft : Q.γ i*rawString Q A.1=(s : ℂ) • (Q.γ a*Q.γ b*Q.γ c))
    (hcoup : coupling w i a b c=w A*s) :
    (∑ j, ∑ k, ∑ l, quarticFiber Q w A i j k l)=
      3 • (Q.γ i*((w A : ℂ) • rawString Q A.1)-((w A : ℂ) • rawString Q A.1)*Q.γ i) := by
  have hi : i∈A.1 := by rw [hA]; simp
  have hanti := rawString_anticommutes_of_mem Q A i hi
  rw [quarticFiber_six Q w A i a b c hA hia hib hic hab hac hbc,hcoup]
  simp only [mul_smul_comm,smul_mul_assoc,hanti,smul_neg,sub_neg_eq_add,hleft,
    Complex.ofReal_mul,smul_smul]
  module

lemma quarticFiber_commutator (Q : Model N) (w : Disorder N) (A : SYKEdge.KSet N 4)
    (i : Fin N) :
    (∑ j, ∑ k, ∑ l, quarticFiber Q w A i j k l)=
      3 • (Q.γ i*((w A : ℂ) • rawString Q A.1)-((w A : ℂ) • rawString Q A.1)*Q.γ i) := by
  by_cases hi : i∈A.1
  · have hlen : (A.1.sort (· ≤ ·)).length=4 := by simpa using A.2
    obtain ⟨a,b,c,d,hsort⟩ := List.length_eq_four.mp hlen
    have hlt := A.1.sortedLT_sort
    rw [hsort] at hlt
    simp only [List.sortedLT_iff_pairwise] at hlt
    simp at hlt
    rcases hlt with ⟨⟨hab,hac,had⟩,⟨hbc,hbd⟩,hcd⟩
    have hA : A.1={a,b,c,d} := by
      have he := congrArg List.toFinset hsort
      simpa using he
    have hraw : rawString Q A.1=Q.γ a*(Q.γ b*(Q.γ c*Q.γ d)) := by simp [rawString,hsort]
    have hw : coupling w a b c d=w A := by
      rw [coupling_increasing w a b c d hab hbc hcd]
      congr 1
      exact Subtype.ext hA.symm
    have hsq (j : Fin N) (X : Mat (SiteHilbert N)) : Q.γ j*(Q.γ j*X)=X := by
      rw [← mul_assoc,Q.car.sq,one_mul]
    have hswap (j k : Fin N) (hjk : j≠k) (X : Mat (SiteHilbert N)) :
        Q.γ j*(Q.γ k*X)=-(Q.γ k*(Q.γ j*X)) := by
      rw [← mul_assoc,Q.car.anticomm j k hjk,neg_mul,mul_assoc]
    have haL : Q.γ a*rawString Q A.1=Q.γ b*Q.γ c*Q.γ d := by rw [hraw,hsq,mul_assoc]
    have hbL : Q.γ b*rawString Q A.1=-(Q.γ a*Q.γ c*Q.γ d) := by
      rw [hraw,hswap b a hab.ne.symm,hsq,mul_assoc]
    have hcL : Q.γ c*rawString Q A.1=Q.γ a*Q.γ b*Q.γ d := by
      rw [hraw,hswap c a hac.ne.symm,hswap c b hbc.ne.symm,hsq]
      simp only [mul_neg,neg_neg,mul_assoc]
    have hdL : Q.γ d*rawString Q A.1=-(Q.γ a*Q.γ b*Q.γ c) := by
      rw [hraw,hswap d a had.ne.symm,hswap d b hbd.ne.symm,← mul_assoc (Q.γ d),
        Q.car.anticomm d c hcd.ne.symm]
      simp only [neg_mul,mul_neg,mul_assoc,Q.car.sq,mul_one,neg_neg]
    rw [hA] at hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi|hi|hi|hi
    · subst i
      apply quarticFiber_comm_from_contraction Q w A a b c d 1 hA hab.ne hac.ne had.ne hbc.ne hbd.ne hcd.ne
      · simpa only [Complex.ofReal_one,one_smul] using haL
      · simpa only [mul_one] using hw
    · subst i
      have hAb : A.1={b,a,c,d} := hA.trans (by ext x; simp [or_left_comm])
      apply quarticFiber_comm_from_contraction Q w A b a c d (-1) hAb hab.ne.symm hbc.ne hbd.ne hac.ne had.ne hcd.ne
      · simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul] using hbL
      · rw [coupling_swap01,hw,mul_neg_one]
    · subst i
      have hAc : A.1={c,a,b,d} := hA.trans (by ext x; simp [or_left_comm,or_assoc])
      apply quarticFiber_comm_from_contraction Q w A c a b d 1 hAc hac.ne.symm hbc.ne.symm hcd.ne hab.ne had.ne hbd.ne
      · simpa only [Complex.ofReal_one,one_smul] using hcL
      · rw [coupling_swap01,coupling_swap12,neg_neg,hw,mul_one]
    · subst i
      have hAd : A.1={d,a,b,c} := hA.trans (by ext x; simp [or_left_comm,or_comm,or_assoc])
      apply quarticFiber_comm_from_contraction Q w A d a b c (-1) hAd had.ne.symm hbd.ne.symm hcd.ne.symm hab.ne hac.ne hbc.ne
      · simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul] using hdL
      · rw [coupling_swap01,coupling_swap12,coupling_swap23,neg_neg,hw,mul_neg_one]
  · simp only [quarticFiber_zero_of_not_mem Q w A i hi,Finset.sum_const_zero,
      mul_smul_comm,smul_mul_assoc,rawString_commutes_of_not_mem Q A i hi,sub_self,nsmul_zero]

lemma majorana_hamiltonian_commutator (Q : Model N) (w : Disorder N) (i : Fin N) :
    Q.γ i*hamiltonian Q w-hamiltonian Q w*Q.γ i=
      (1/3 : ℂ) • ∑ j, ∑ k, ∑ l, (coupling w i j k l : ℂ) • (Q.γ j*Q.γ k*Q.γ l) := by
  have he : (∑ j, ∑ k, ∑ l, (coupling w i j k l : ℂ) • (Q.γ j*Q.γ k*Q.γ l))=
      ∑ A : SYKEdge.KSet N 4, ∑ j, ∑ k, ∑ l, quarticFiber Q w A i j k l := by
    simp_rw [coupling_fiber_sum Q w i]
    calc
      _=∑ j : Fin N, ∑ k : Fin N, ∑ A : SYKEdge.KSet N 4, ∑ l : Fin N, quarticFiber Q w A i j k l := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
      _=∑ j : Fin N, ∑ A : SYKEdge.KSet N 4, ∑ k : Fin N, ∑ l : Fin N, quarticFiber Q w A i j k l := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
      _=_ := by rw [Finset.sum_comm]
  rw [he]
  simp only [quarticFiber_commutator,← Finset.smul_sum]
  simp only [hamiltonian,Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  module


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def conjugationAlgHom (B C : Mat ι) (hBC : B*C=1) (hCB : C*B=1) : Mat ι →ₐ[ℂ] Mat ι where
  toFun X := B*X*C
  map_one' := by rw [mul_one,hBC]
  map_mul' X Y := by
    calc
      B*(X*Y)*C=B*X*(C*B)*Y*C := by rw [hCB,mul_one]; noncomm_ring
      _=(B*X*C)*(B*Y*C) := by noncomm_ring
  map_zero' := by simp
  map_add' X Y := by simp only [mul_add,add_mul]
  commutes' z := by simp only [Algebra.algebraMap_eq_smul_one,mul_smul_comm,smul_mul_assoc,
    mul_one,hBC]

def imaginaryConjugation (H : Mat ι) (s : ℝ) : Mat ι →ₐ[ℂ] Mat ι :=
  conjugationAlgHom (mexp ((-s : ℂ) • H)) (mexp ((s : ℂ) • H))
    (by simpa only [neg_neg] using mexp_smul_cancel H (-s)) (mexp_smul_cancel H s)

lemma imaginaryConjugation_apply (H X : Mat ι) (s : ℝ) :
    imaginaryConjugation H s X=mexp ((-s : ℂ) • H)*X*mexp ((s : ℂ) • H) := rfl

lemma imaginaryConjugation_hamiltonian (H : Mat ι) (s : ℝ) : imaginaryConjugation H s H=H := by
  letI : NormedAlgebra ℚ (Mat ι) := .restrictScalars ℚ ℂ (Mat ι)
  have hc : Commute ((-s : ℂ) • H) H := (Commute.refl H).smul_left (-s : ℂ)
  have hcomm : mexp ((-s : ℂ) • H)*H=H*mexp ((-s : ℂ) • H) := hc.exp_left.eq
  rw [imaginaryConjugation_apply,hcomm,mul_assoc]
  have hcancel : mexp ((-s : ℂ) • H)*mexp ((s : ℂ) • H)=1 := by
    simpa only [neg_neg] using mexp_smul_cancel H (-s)
  rw [hcancel,mul_one]

lemma imaginary_hamiltonian_commutator {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) (i : Fin N) :
    imaginary Q w s i*hamiltonian Q w-hamiltonian Q w*imaginary Q w s i=
      (1/3 : ℂ) • ∑ j, ∑ k, ∑ l, (coupling w i j k l : ℂ) •
        (imaginary Q w s j*imaginary Q w s k*imaginary Q w s l) := by
  have he := congrArg (imaginaryConjugation (hamiltonian Q w) s)
    (majorana_hamiltonian_commutator Q w i)
  simp only [map_sub,map_mul,map_smul,map_sum,imaginaryConjugation_hamiltonian] at he
  exact he


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def couplingSum (w : Disorder N) (i : Fin N) (f : Fin N → Fin N → Fin N → Mat ι) : Mat ι :=
  ∑ j, ∑ k, ∑ l, (coupling w i j k l : ℂ) • f j k l

lemma couplingSum_swap12 (w : Disorder N) (i : Fin N) (f : Fin N → Fin N → Fin N → Mat ι) :
    couplingSum w i (fun j k l ↦ f k j l)=-couplingSum w i f := by
  unfold couplingSum
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [coupling_swap12 w i j k l,Complex.ofReal_neg,neg_smul]

lemma couplingSum_swap23 (w : Disorder N) (i : Fin N) (f : Fin N → Fin N → Fin N → Mat ι) :
    couplingSum w i (fun j k l ↦ f j l k)=-couplingSum w i f := by
  unfold couplingSum
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [coupling_swap23 w i j k l,Complex.ofReal_neg,neg_smul]

lemma couplingSum_cyclic (w : Disorder N) (i : Fin N) (f : Fin N → Fin N → Fin N → Mat ι) :
    couplingSum w i (fun j k l ↦ f k l j)=couplingSum w i f := by
  have he := couplingSum_swap12 w i (fun j k l ↦ f j l k)
  have h2 := couplingSum_swap23 w i f
  calc
    _= -couplingSum w i (fun j k l ↦ f j l k) := he
    _= _ := by rw [h2,neg_neg]

lemma couplingSum_add (w : Disorder N) (i : Fin N) (f g : Fin N → Fin N → Fin N → Mat ι) :
    couplingSum w i (fun j k l ↦ f j k l+g j k l)=couplingSum w i f+couplingSum w i g := by
  simp only [couplingSum,smul_add,Finset.sum_add_distrib]

lemma couplingSum_sub (w : Disorder N) (i : Fin N) (f g : Fin N → Fin N → Fin N → Mat ι) :
    couplingSum w i (fun j k l ↦ f j k l-g j k l)=couplingSum w i f-couplingSum w i g := by
  simp only [couplingSum,smul_sub,Finset.sum_sub_distrib]

lemma couplingSum_smul (w : Disorder N) (i : Fin N) (z : ℂ)
    (f : Fin N → Fin N → Fin N → Mat ι) :
    couplingSum w i (fun j k l ↦ z • f j k l)=z • couplingSum w i f := by
  simp only [couplingSum,smul_comm _ z,Finset.smul_sum]

lemma cubic_telescoping (A B : Fin N → Mat ι) (X : Mat ι) (j k l : Fin N) :
    A j*A k*((1/2 : ℂ) • (A l*X-X*B l))+
      A j*((1/2 : ℂ) • (A k*X-X*B k))*B l+
      ((1/2 : ℂ) • (A j*X-X*B j))*B k*B l=
      (1/2 : ℂ) • (A j*A k*A l*X-X*B j*B k*B l) := by
  simp only [mul_smul_comm,smul_mul_assoc,← smul_add]
  congr 1
  noncomm_ring

lemma coupling_cubic_reduction (w : Disorder N) (i : Fin N) (A B : Fin N → Mat ι) (X : Mat ι) :
    let C := fun j ↦ (1/2 : ℂ) • (A j*X-X*B j)
    couplingSum w i (fun j k l ↦ A k*A l*C j-A k*C j*B l+C j*B k*B l)=
      (1/2 : ℂ) • couplingSum w i (fun j k l ↦ A j*A k*A l*X-X*B j*B k*B l) := by
  dsimp only
  let C := fun j ↦ (1/2 : ℂ) • (A j*X-X*B j)
  have h1 := couplingSum_cyclic w i (fun j k l ↦ A j*A k*C l)
  have h2 := couplingSum_swap12 w i (fun j k l ↦ A j*C k*B l)
  change couplingSum w i (fun j k l ↦ A k*A l*C j-A k*C j*B l+C j*B k*B l)=_
  rw [couplingSum_add,couplingSum_sub,h1,h2,sub_neg_eq_add,← couplingSum_add,← couplingSum_add]
  simp only [C,cubic_telescoping]
  rw [couplingSum_smul]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

lemma rawString_hermitian_of_card_four {N : ℕ} (Q : Model N)
    (S : Finset (Fin N)) (hS : S.card = 4) : (rawString Q S).IsHermitian := by
  unfold rawString Matrix.IsHermitian
  rw [Matrix.conjTranspose_list_prod]
  have hlen : (S.sort (· ≤ ·)).length = 4 := by simpa using hS
  have hnodup : (S.sort (· ≤ ·)).Nodup := S.sort_nodup (· ≤ ·)
  obtain ⟨a, b, c, d, hlist⟩ := List.length_eq_four.mp hlen
  rw [hlist] at hnodup
  simp at hnodup
  rcases hnodup with ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  rw [hlist]
  simp
  rw [(Q.car.herm a).eq, (Q.car.herm b).eq, (Q.car.herm c).eq, (Q.car.herm d).eq]
  calc
    Q.γ d * (Q.γ c * (Q.γ b * Q.γ a)) =
        (Q.γ d * Q.γ c) * (Q.γ b * Q.γ a) := by noncomm_ring
    _ = -(Q.γ c * Q.γ d) * (Q.γ b * Q.γ a) := by
          rw [Q.car.anticomm d c (Ne.symm hcd)]
    _ = Q.γ c * (-(Q.γ d * Q.γ b) * Q.γ a) := by noncomm_ring
    _ = Q.γ c * (Q.γ b * Q.γ d * Q.γ a) := by
          rw [Q.car.anticomm d b (Ne.symm hbd)]
          noncomm_ring
    _ = (Q.γ c * Q.γ b) * (Q.γ d * Q.γ a) := by noncomm_ring
    _ = -(Q.γ b * Q.γ c) * (Q.γ d * Q.γ a) := by
          rw [Q.car.anticomm c b (Ne.symm hbc)]
    _ = Q.γ b * Q.γ c * (Q.γ a * Q.γ d) := by
          rw [Q.car.anticomm d a (Ne.symm had)]
          noncomm_ring
    _ = Q.γ b * (Q.γ c * Q.γ a) * Q.γ d := by noncomm_ring
    _ = -(Q.γ b * (Q.γ a * Q.γ c) * Q.γ d) := by
          rw [Q.car.anticomm c a (Ne.symm hac)]
          noncomm_ring
    _ = -((Q.γ b * Q.γ a) * (Q.γ c * Q.γ d)) := by noncomm_ring
    _ = (Q.γ a * Q.γ b) * (Q.γ c * Q.γ d) := by
          rw [Q.car.anticomm b a (Ne.symm hab)]
          noncomm_ring
    _ = Q.γ a * (Q.γ b * (Q.γ c * Q.γ d)) := by noncomm_ring

lemma hamiltonian_hermitian_words {N : ℕ} (Q : Model N) (w : Disorder N) :
    (hamiltonian Q w).IsHermitian := by
  unfold hamiltonian Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Matrix.conjTranspose_smul, (rawString_hermitian_of_card_four Q A.1 A.2).eq]
  simp


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
lemma imaginary_conjTranspose {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) (i : Fin N) :
    (imaginary Q w s i)ᴴ=imaginary Q w (-s) i := by
  unfold imaginary
  simp only [Complex.ofReal_neg, neg_neg]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have hp := mexp_hermitian _ (hamiltonian_hermitian_words Q w) s
  have hn := mexp_hermitian _ (hamiltonian_hermitian_words Q w) (-s)
  simp only [Complex.ofReal_neg] at hn
  rw [hp.eq, hn.eq, (Q.car.herm i).eq]
  simp only [mul_assoc]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

lemma mBlock_apply (w : Disorder N) (A B C D : Fin N → Mat ι) (i j : Fin N) (X : Mat ι) :
    applySuper (mBlock w A B C D i j) X=(1/3 : ℂ) • ∑ k, ∑ l,
      (coupling w i j k l : ℂ) • (A k*C l*X-A k*X*D l+X*B k*D l) := by
  let F : Mat ι →L[ℂ] Mat ι := (1/3 : ℂ) • ∑ k, ∑ l,
    (coupling w i j k l : ℂ) • (leftAct (A k*C l)-(rightAct (D l)).comp (leftAct (A k))+rightAct (B k*D l))
  have hsuper : super F.toLinearMap=mBlock w A B C D i j := by
    congr 1
    funext Y
    change F Y=_
    simp only [F,_root_.smul_apply,_root_.sum_apply,_root_.add_apply,_root_.sub_apply,
      ContinuousLinearMap.comp_apply,leftAct_apply,rightAct_apply]
    simp only [mul_assoc]
  rw [← hsuper,applySuper_super]
  change F X=_
  simp only [F,_root_.smul_apply,_root_.sum_apply,_root_.add_apply,_root_.sub_apply,
    ContinuousLinearMap.comp_apply,leftAct_apply,rightAct_apply,mul_assoc]

lemma cMap_apply_commutator (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N)
    (X : Mat (SiteHilbert N)) :
    applySuper (cMap Q w β i) X=(1/2 : ℂ) •
      (imaginary Q w (β/4) i*X-X*imaginary Q w (-(β/4)) i) := by
  let A := imaginary Q w (β/4) i
  have he := applySuper_super (((1/2 : ℂ) • (leftAct A-rightAct Aᴴ)).toLinearMap) X
  change applySuper (cMap Q w β i) X=(1/2 : ℂ) • (A*X-X*Aᴴ) at he
  rw [he,imaginary_conjTranspose]

end SYKFastMix.FastMixing
open SYKFastMix.FastMixing
theorem solution {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (_hβ : 0 ≤ β)
    (X : Mat (SiteHilbert N)) (i : Fin N) :
    applySuper (cMap Q w β i) (hamiltonian Q w*X-X*hamiltonian Q w)-
      (hamiltonian Q w*applySuper (cMap Q w β i) X-applySuper (cMap Q w β i) X*hamiltonian Q w)=
      ∑ j, applySuper (mBlock w (imaginary Q w (β/4)) (imaginary Q w (-(β/4)))
        (imaginary Q w (β/4)) (imaginary Q w (-(β/4))) i j) (applySuper (cMap Q w β j) X) := by
  let H := hamiltonian Q w
  let A := imaginary Q w (β/4)
  let B := imaginary Q w (-(β/4))
  let C := fun j ↦ (1/2 : ℂ) • (A j*X-X*B j)
  have hL : applySuper (cMap Q w β i) (H*X-X*H)-
      (H*applySuper (cMap Q w β i) X-applySuper (cMap Q w β i) X*H)=
      (1/2 : ℂ) • ((A i*H-H*A i)*X-X*(B i*H-H*B i)) := by
    rw [cMap_apply_commutator,cMap_apply_commutator]
    change (1/2 : ℂ) • (A i*(H*X-X*H)-(H*X-X*H)*B i)-
      (H*((1/2 : ℂ) • (A i*X-X*B i))-((1/2 : ℂ) • (A i*X-X*B i))*H)=_
    simp only [mul_smul_comm,smul_mul_assoc,← smul_sub]
    congr 1
    noncomm_ring
  have hAc := imaginary_hamiltonian_commutator Q w (β/4) i
  have hBc := imaginary_hamiltonian_commutator Q w (-(β/4)) i
  change A i*H-H*A i=(1/3 : ℂ) • couplingSum w i (fun j k l ↦ A j*A k*A l) at hAc
  change B i*H-H*B i=(1/3 : ℂ) • couplingSum w i (fun j k l ↦ B j*B k*B l) at hBc
  rw [hL,hAc,hBc]
  have hR : (∑ j, applySuper (mBlock w A B A B i j) (C j))=
      (1/3 : ℂ) • couplingSum w i (fun j k l ↦ A k*A l*C j-A k*C j*B l+C j*B k*B l) := by
    simp only [mBlock_apply,couplingSum,← Finset.smul_sum]
  change (1/2 : ℂ) • (((1/3 : ℂ) • couplingSum w i (fun j k l ↦ A j*A k*A l))*X-
      X*((1/3 : ℂ) • couplingSum w i (fun j k l ↦ B j*B k*B l)))=_
  simp only [cMap_apply_commutator] at ⊢
  change _=(∑ j, applySuper (mBlock w A B A B i j) (C j))
  rw [hR,coupling_cubic_reduction]
  simp only [couplingSum,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    smul_sub,smul_smul,Finset.sum_sub_distrib,mul_assoc]
  module


namespace SYKFastMix.FastMixing

end SYKFastMix.FastMixing
end
