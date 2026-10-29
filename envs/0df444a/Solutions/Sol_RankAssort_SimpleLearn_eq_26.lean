-- Prove2me | solution 1 for RankAssort.SimpleLearn.eq_26
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T05:45:17.575192+00:00
-- url     : https://prove2.me/submissions/e2ba9637-ad78-4ed7-98e7-6ca9047556d0

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
theorem _root_.solution {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (piT piStar : List (Fin n)) (hT : piT.Nodup) (hTlen : piT.length = n)
    (hs : piStar.Nodup) (hslen : piStar.length = n)
    (r : ℕ) (hr : r < n) (iStar : Fin n) (hiStar : piStar[r]? = some iStar) :
    jointTerm D τ piT piStar r ≤ firstClickTerm D τ (piT.take r ++ [iStar]) r := by
  exact Queelius.RankingCoupling.joint_bound D τ hτ piT piStar r (by rw [hTlen];exact hr.le) iStar hiStar
end RankAssort.SimpleLearn
