-- Prove2me | solution 1 for RankAssort.SimpleLearn.first_click_identity
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T06:33:24.29984+00:00
-- url     : https://prove2.me/submissions/82a9d00e-2315-4312-9815-8a4162814fe3

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
open MeasureTheory Set
namespace Queelius.RankingCoupling
open RankAssort.SimpleLearn
lemma bern_nonnegative {n : ℕ} (θ : CustomerType n) (i : Fin n) (b : Bool) : 0 ≤ bern (θ.p i) b := by
  cases b <;> simp [bern] <;> linarith [θ.p_nonneg i,θ.p_le_one i]
lemma like_nonnegative {n : ℕ} (θ : CustomerType n) (L : Fin n → Bool) : 0 ≤ likeWeight θ L := by
  exact Finset.prod_nonneg (fun i _ => bern_nonnegative θ i (L i))
lemma like_mass {n : ℕ} (θ : CustomerType n) : ∑ L,likeWeight θ L=1 := by
  unfold likeWeight
  rw [← Fintype.prod_sum]
  simp [bern]
lemma coupled_bounds {n : ℕ} (θ : CustomerType n) (E : (Fin n → Bool) → Prop) :
    0 ≤ coupledProb θ E ∧ coupledProb θ E ≤ 1 := by
  classical
  constructor
  · apply Finset.sum_nonneg
    intro L _
    split_ifs <;> first | exact like_nonnegative θ L | rfl
  · rw [← like_mass θ]
    apply Finset.sum_le_sum
    intro L _
    split_ifs <;> first | rfl | exact like_nonnegative θ L
lemma coupled_mono {n : ℕ} (θ : CustomerType n) (E F : (Fin n → Bool) → Prop)
    (hEF : ∀ L,E L → F L) : coupledProb θ E ≤ coupledProb θ F := by
  classical
  unfold coupledProb
  apply Finset.sum_le_sum
  intro L _
  by_cases he : E L
  · simp only [if_pos he,if_pos (hEF L he)]
    exact le_rfl
  · rw [if_neg he]
    split_ifs <;> first | exact like_nonnegative θ L | rfl
lemma measurable_like {n : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (L : Fin n → Bool) :
    Measurable (fun θ => likeWeight (τ θ) L) := by
  unfold likeWeight
  apply Finset.measurable_prod
  intro i _
  cases hb : L i
  · change Measurable (fun θ => (1:ℝ)-(τ θ).p i)
    exact (measurable_const : Measurable (fun _ : Θ => (1:ℝ))).sub (hτ.1 i)
  · simpa [bern,hb] using hτ.1 i
lemma measurable_coupled {n : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (E : Θ → (Fin n → Bool) → Prop)
    (hE : ∀ L,MeasurableSet {θ | E θ L}) : Measurable (fun θ => coupledProb (τ θ) (E θ)) := by
  classical
  unfold coupledProb
  apply Finset.measurable_sum
  intro L _
  exact Measurable.ite (hE L) (measurable_like τ hτ L) measurable_const
lemma measurable_noClick {n : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (l : List (Fin n)) (r : ℕ) (L : Fin n → Bool) :
    MeasurableSet {θ | noClickTop (τ θ) l r L} := by
  classical
  have he : {θ | noClickTop (τ θ) l r L}=
      ⋂ j : ℕ,⋂ hj : j < l.length,{θ | j < r → j < (τ θ).k → L (l.get ⟨j,hj⟩)=false} := by
    ext θ;simp [noClickTop]
  rw [he]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  by_cases hjr : j < r
  · by_cases hl : L (l.get ⟨j,hj⟩)=false
    · simp only [List.get_eq_getElem] at hl
      simp [hjr,hl]
    · simp only [List.get_eq_getElem] at hl
      have hm := measurableSet_le hτ.2.2 (measurable_const : Measurable (fun _ : Θ => j))
      simpa [hjr,hl] using hm
  · simp [hjr]
lemma measurable_clicksAt {n : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (l : List (Fin n)) (r : ℕ) (L : Fin n → Bool) :
    MeasurableSet {θ | clicksAt (τ θ) l r L} := by
  classical
  have he : {θ | clicksAt (τ θ) l r L}=
      ⋃ hr : r < l.length,{θ | r < (τ θ).k ∧ L (l.get ⟨r,hr⟩)=true} := by ext θ;simp [clicksAt]
  rw [he]
  apply MeasurableSet.iUnion
  intro hr
  by_cases hl : L (l.get ⟨r,hr⟩)=true
  · simp only [List.get_eq_getElem] at hl
    simpa [hl] using (measurableSet_lt (measurable_const : Measurable (fun _ : Θ => r)) hτ.2.2)
  · simp only [List.get_eq_getElem] at hl
    simp [hl]
lemma integrable_coupled {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (E : Θ → (Fin n → Bool) → Prop)
    (hE : ∀ L,MeasurableSet {θ | E θ L}) : Integrable (fun θ => coupledProb (τ θ) (E θ)) D :=
  Integrable.of_mem_Icc 0 1 (measurable_coupled τ hτ E hE).aemeasurable (ae_of_all _ (fun θ => coupled_bounds (τ θ) (E θ)))
lemma prefix_noClick {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (r : ℕ) (hr : r ≤ l.length)
    (i : Fin n) (L : Fin n → Bool) (hno : noClickTop θ l r L) :
    noClickTop θ (l.take r++[i]) r L := by
  intro j hj hjr hjk
  have htake : (l.take r).length=r := List.length_take_of_le hr
  have hjtake : j < (l.take r).length := by rw [htake];exact hjr
  have hjl : j < l.length := lt_of_lt_of_le hjr hr
  have he : (l.take r++[i]).get ⟨j,hj⟩=l.get ⟨j,hjl⟩ := by
    simp only [List.get_eq_getElem,List.getElem_append_left hjtake,List.getElem_take]
  rw [he]
  exact hno j hjl hjr hjk
lemma prefix_click {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (r : ℕ) (hr : r ≤ l.length)
    (i : Fin n) (L : Fin n → Bool) (hrk : r < θ.k) (hL : L i=true) :
    clicksAt θ (l.take r++[i]) r L := by
  have htake : (l.take r).length=r := List.length_take_of_le hr
  have hlen : r < (l.take r++[i]).length := by simp [htake]
  refine ⟨hlen,hrk,?_⟩
  have he : (l.take r++[i]).get ⟨r,hlen⟩=i := by
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_right (show (l.take r).length ≤ r by omega)]
    simp [htake]
  rw [he]
  exact hL
lemma joint_event_inclusion {n : ℕ} (θ : CustomerType n) (l l' : List (Fin n)) (r : ℕ)
    (hr : r ≤ l.length) (i : Fin n) (hi : l'[r]?=some i) (L : Fin n → Bool) :
    (noClickTop θ l r L ∧ noClickTop θ l' r L ∧ clicksAt θ l' r L) →
      noClickTop θ (l.take r++[i]) r L ∧ clicksAt θ (l.take r++[i]) r L := by
  rintro ⟨hno,_,hclick⟩
  rcases hclick with ⟨hrs,hrk,hLike⟩
  have he : l'.get ⟨r,hrs⟩=i := by
    rw [List.getElem?_eq_getElem hrs] at hi
    simpa only [List.get_eq_getElem] using Option.some.inj hi
  refine ⟨prefix_noClick θ l r hr i L hno,prefix_click θ l r hr i L hrk ?_⟩
  rw [← he]
  exact hLike
lemma joint_bound {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (l l' : List (Fin n)) (r : ℕ)
    (hr : r ≤ l.length) (i : Fin n) (hi : l'[r]?=some i) :
    jointTerm D τ l l' r ≤ firstClickTerm D τ (l.take r++[i]) r := by
  unfold jointTerm firstClickTerm
  apply integral_mono
  · apply integrable_coupled D τ hτ
    intro L
    exact (measurable_noClick τ hτ l r L).inter
      ((measurable_noClick τ hτ l' r L).inter (measurable_clicksAt τ hτ l' r L))
  · apply integrable_coupled D τ hτ
    intro L
    exact (measurable_noClick τ hτ (l.take r++[i]) r L).inter
      (measurable_clicksAt τ hτ (l.take r++[i]) r L)
  · intro θ
    exact coupled_mono (τ θ) _ _ (fun L => joint_event_inclusion (τ θ) l l' r hr i hi L)
lemma repeated_product_control {n : ℕ} (θ : CustomerType n) (i : Fin n) :
    coupledProb θ (fun L => noClickTop θ [i,i] 1 L ∧ clicksAt θ [i,i] 1 L)=0 := by
  classical
  unfold coupledProb
  apply Finset.sum_eq_zero
  intro L _
  have hn : ¬ (noClickTop θ [i,i] 1 L ∧ clicksAt θ [i,i] 1 L) := by
    rintro ⟨hno,hclick⟩
    rcases hclick with ⟨hr,hk,ht⟩
    have hp : 0 < θ.k := by linarith [θ.one_le_k]
    have hf := hno 0 (by simp) (by decide) hp
    have hfalse : L i=false := by simpa using hf
    have htrue : L i=true := by simpa using ht
    exact Bool.false_ne_true (hfalse.symm.trans htrue)
  simp [hn]
lemma exhausted_window_control {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (r : ℕ)
    (hr : θ.k ≤ r) : coupledProb θ (fun L => noClickTop θ l r L ∧ clicksAt θ l r L)=0 := by
  classical
  unfold coupledProb
  apply Finset.sum_eq_zero
  intro L _
  simp [clicksAt,not_lt.mpr hr]
end Queelius.RankingCoupling

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem _root_.coupling_comparison_solution {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (piT piStar : List (Fin n)) (hT : piT.Nodup) (hTlen : piT.length = n)
    (hs : piStar.Nodup) (hslen : piStar.length = n)
    (r : ℕ) (hr : r < n) (iStar : Fin n) (hiStar : piStar[r]? = some iStar) :
    jointTerm D τ piT piStar r ≤ firstClickTerm D τ (piT.take r ++ [iStar]) r := by
  exact Queelius.RankingCoupling.joint_bound D τ hτ piT piStar r (by rw [hTlen];exact hr.le) iStar hiStar
end RankAssort.SimpleLearn

namespace Queelius.RankingFirstClick
open RankAssort.SimpleLearn
lemma causal_mass : ∀ m : ℕ, ∀ q : (Fin m → Bool) → Fin m → ℝ,
    (∀ c d j,(∀ k,k < j → c k=d k) → q c j=q d j) →
    (∑ c : Fin m → Bool,∏ j,bern (q c j) (c j))=1 := by
  intro m
  induction m with
  | zero => intro q hc;simp
  | succ m ih =>
    intro q hc
    have h0 (b : Bool) (c : Fin m → Bool) : q (Fin.cons b c) 0=q (fun _ => false) 0 := by
      apply hc (Fin.cons b c) (fun _ => false) (0 : Fin (m+1))
      intro k hk
      have hz : (0 : Fin (m+1)).val=0 := rfl
      have hh : k.val < (0 : Fin (m+1)).val := hk
      rw [hz] at hh
      omega
    have hr (b : Bool) : (∑ c : Fin m → Bool,∏ j,bern (q (Fin.cons b c) j.succ) (c j))=1 := by
      apply ih
      intro c d j hcd
      apply hc
      intro k hk
      cases k using Fin.cases with
      | zero => simp
      | succ k => simpa using hcd k (by simpa using hk)
    rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp,Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    have heq (b : Bool) (c : Fin m → Bool) :
        (Fin.consEquiv (fun _ : Fin (m+1) => Bool)) (b,c)=Fin.cons b c := rfl
    simp_rw [heq,h0,← Finset.mul_sum,hr]
    simp [bern]
lemma clicked_before_causal {n : ℕ} (θ : CustomerType n) (l : List (Fin n))
    (c d : Fin (window θ l) → Bool) (j : Fin (window θ l))
    (hcd : ∀ k,k < j → c k=d k) : clickedBefore θ l c j=clickedBefore θ l d j := by
  unfold clickedBefore
  congr 1
  apply Finset.filter_congr
  intro k _
  by_cases hk : k < j
  · simp [hk,hcd k hk]
  · simp [hk]
lemma click_mass {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) : ∑ c,clickWeight θ l c=1 := by
  unfold clickWeight
  apply causal_mass
  intro c d j hcd
  rw [clicked_before_causal θ l c d j hcd]
lemma false_click_weight {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) :
    clickWeight θ l (fun _ => false)=∏ j : Fin (window θ l),(1-θ.p (windowGet θ l j)) := by
  simp [clickWeight,clickedBefore,bern,θ.f_empty]
lemma hook_product {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) :
    hookProb θ l=1-∏ j : Fin (window θ l),(1-θ.p (windowGet θ l j)) := by
  classical
  have he : (Finset.univ.filter (fun c : Fin (window θ l) → Bool => ∃ j,c j=true))=
      Finset.univ.erase (fun _ => false) := by
    ext c
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,ne_eq,and_true]
    constructor
    · rintro ⟨j,hj⟩ h
      have hh := congrFun h j
      rw [hj] at hh
      exact Bool.false_ne_true hh.symm
    · intro hc
      by_contra hn
      apply hc
      funext j
      cases h : c j
      · rfl
      · exact False.elim (hn ⟨j,h⟩)
  unfold hookProb
  rw [he,Finset.sum_erase_eq_sub (Finset.mem_univ _),click_mass,false_click_weight]
end Queelius.RankingFirstClick

namespace Queelius.RankingFirstClick
open RankAssort.SimpleLearn
lemma coupled_complement {n : ℕ} (θ : CustomerType n) (E : (Fin n → Bool) → Prop) :
    coupledProb θ (fun L => ¬ E L)=1-coupledProb θ E := by
  classical
  unfold coupledProb
  rw [← Queelius.RankingCoupling.like_mass θ,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro L _
  by_cases he : E L <;> simp [he]
lemma coupled_cylinder {n : ℕ} (θ : CustomerType n) (A : Finset (Fin n)) :
    coupledProb θ (fun L => ∀ i ∈ A,L i=false)=∏ i ∈ A,(1-θ.p i) := by
  classical
  let K (i : Fin n) (b : Bool) : ℝ := if i ∈ A ∧ b=true then 0 else bern (θ.p i) b
  have he (L : Fin n → Bool) :
      (if (∀ i ∈ A,L i=false) then likeWeight θ L else 0)=
        ∏ i,K i (L i) := by
    by_cases hL : ∀ i ∈ A,L i=false
    · rw [if_pos hL]
      unfold likeWeight
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ A
      · simp [K,hi,hL i hi]
      · simp [K,hi]
    · rw [if_neg hL]
      push_neg at hL
      obtain ⟨i,hi,hb⟩ := hL
      have htrue : L i=true := by cases h : L i <;> simp_all
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [K,hi,htrue]
  unfold coupledProb
  dsimp only
  have hsum : (∑ L : Fin n → Bool,if (∀ i ∈ A,L i=false) then likeWeight θ L else 0)=
      ∑ L : Fin n → Bool,∏ i,K i (L i) := by
    apply Finset.sum_congr rfl
    intro L _
    exact he L
  trans (∑ L : Fin n → Bool,if (∀ i ∈ A,L i=false) then likeWeight θ L else 0)
  · apply Finset.sum_congr rfl
    intro L _
    simp only [ite_eq_ite]
  rw [hsum,← Fintype.prod_sum]
  have hb (i : Fin n) : (∑ b : Bool,K i b)=
      if i ∈ A then 1-θ.p i else 1 := by
    by_cases hi : i ∈ A <;> simp [K,hi,bern]
  simp_rw [hb]
  rw [Finset.prod_ite_mem]
  simp
lemma window_injective {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (hl : l.Nodup) :
    Function.Injective (windowGet θ l) := by
  intro a b hab
  have he := hl.get_inj_iff.mp hab
  apply Fin.ext
  exact congrArg (fun j : Fin l.length => j.val) he
lemma coupled_window {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (hl : l.Nodup) :
    coupledProb θ (fun L => ∃ j,∃ hj : j < l.length,j < θ.k ∧ L (l.get ⟨j,hj⟩)=true)=
      1-∏ j : Fin (window θ l),(1-θ.p (windowGet θ l j)) := by
  classical
  let A := Finset.univ.image (windowGet θ l)
  have he (L : Fin n → Bool) :
      (∃ j,∃ hj : j < l.length,j < θ.k ∧ L (l.get ⟨j,hj⟩)=true) ↔ ¬ ∀ i ∈ A,L i=false := by
    constructor
    · rintro ⟨j,hj,hk,htrue⟩ hno
      let q : Fin (window θ l) := ⟨j,lt_min hk hj⟩
      have hmem : windowGet θ l q ∈ A := Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
      have hh := hno _ hmem
      change L (l.get ⟨j,hj⟩)=false at hh
      rw [htrue] at hh
      exact Bool.false_ne_true hh.symm
    · intro hno
      push_neg at hno
      obtain ⟨i,hi,hL⟩ := hno
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hi
      have htrue : L (windowGet θ l q)=true := by cases h : L (windowGet θ l q) <;> simp_all
      exact ⟨q.val,lt_of_lt_of_le q.isLt (min_le_right _ _),lt_of_lt_of_le q.isLt (min_le_left _ _),htrue⟩
  have hE : (fun L : Fin n → Bool => ∃ j,∃ hj : j < l.length,j < θ.k ∧ L (l.get ⟨j,hj⟩)=true)=
      (fun L => ¬ ∀ i ∈ A,L i=false) := by funext L;exact propext (he L)
  rw [hE,coupled_complement,coupled_cylinder]
  congr 1
  dsimp [A]
  rw [Finset.prod_image (fun a _ b _ hab => window_injective θ l hl hab)]
end Queelius.RankingFirstClick
namespace RankAssort.SimpleLearn
 theorem _root_.solution {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (hl : l.Nodup) :
    hookProb θ l =
        coupledProb θ (fun L => ∃ j, ∃ hj : j < l.length, j < θ.k ∧ L (l.get ⟨j, hj⟩) = true) ∧
      hookProb θ l = 1 - ∏ j : Fin (window θ l), (1 - θ.p (windowGet θ l j)) := by
  exact ⟨(Queelius.RankingFirstClick.hook_product θ l).trans (Queelius.RankingFirstClick.coupled_window θ l hl).symm,
    Queelius.RankingFirstClick.hook_product θ l⟩
end RankAssort.SimpleLearn

namespace Queelius.RankingFirstClick
open RankAssort.SimpleLearn
lemma empty_window_control {n : ℕ} (θ : CustomerType n) : hookProb θ []=0 := by
  rw [hook_product]
  have hz : window θ []=0 := by simp [window]
  letI : IsEmpty (Fin (window θ [])) := ⟨fun j => by have hh := j.isLt;omega⟩
  simp
noncomputable def twoCoinType : CustomerType 2 where
  p := fun _ => 1/2
  f := fun _ _ => 0
  k := 2
  p_nonneg := by intro i;norm_num
  p_le_one := by intro i;norm_num
  f_ge := by intro i A;norm_num
  f_le := by intro i A;norm_num
  f_empty := by intro i;rfl
  one_le_k := by decide
  k_le := by decide
lemma repeated_position_control :
    hookProb twoCoinType [0,0]=(3/4:ℝ) ∧
      coupledProb twoCoinType (fun L => L 0=true)=(1/2:ℝ) := by
  constructor
  · rw [hook_product]
    norm_num [window,windowGet,twoCoinType,Fin.prod_univ_succ]
  · have he : (fun L : Fin 2 → Bool => L 0=true)=(fun L => ¬ ∀ i ∈ ({0}:Finset (Fin 2)),L i=false) := by
      funext L
      cases h : L 0 <;> simp [h]
    rw [he,coupled_complement,coupled_cylinder]
    norm_num [twoCoinType]
end Queelius.RankingFirstClick
