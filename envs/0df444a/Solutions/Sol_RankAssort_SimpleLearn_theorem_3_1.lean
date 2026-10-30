-- Prove2me | solution 1 for RankAssort.SimpleLearn.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T08:05:57.573325+00:00
-- url     : https://prove2.me/submissions/17164cb1-460e-4db7-a716-1e1052c29104

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Algorithm
section
open MeasureTheory Set
open scoped ENNReal
namespace Queelius.RankingPAC
lemma measurable_fiber_event {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (X : Ω → α) (hX : ∀ a,MeasurableSet (X ⁻¹' {a})) (Q : α → Prop) :
    MeasurableSet {ω | Q (X ω)} := by
  classical
  have he : {ω | Q (X ω)}=⋃ a : α,⋃ (_ : Q a),X ⁻¹' {a} := by ext ω;simp
  rw [he]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun _ => hX a))
lemma conditional_partition_bound {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → α)
    (hX : ∀ a,MeasurableSet (X ⁻¹' {a})) (B : Set Ω) (d : ℝ≥0∞)
    (hB : ∀ a,P ((X ⁻¹' {a}) ∩ B) ≤ d*P (X ⁻¹' {a})) : P B ≤ d := by
  have hu : (⋃ a : α,X ⁻¹' {a})=univ := by ext ω;simp
  have hd : Pairwise (fun a b => Disjoint (X ⁻¹' {a}) (X ⁻¹' {b})) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have hs : (∑' a : α,P (X ⁻¹' {a}))=1 := by
    rw [← measure_iUnion hd hX,hu,measure_univ]
  have hb : B=⋃ a : α,(X ⁻¹' {a}) ∩ B := by ext ω;simp
  calc
    P B = P (⋃ a : α,(X ⁻¹' {a}) ∩ B) := congrArg P hb
    _ ≤ ∑' a : α,P ((X ⁻¹' {a}) ∩ B) := measure_iUnion_le _
    _ ≤ ∑' a : α,d*P (X ⁻¹' {a}) := ENNReal.tsum_le_tsum hB
    _ = d := by rw [ENNReal.tsum_mul_left,hs,mul_one]
open RankAssort.SimpleLearn
lemma rank_failure_bound {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (epsP deltaP : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : SimpleLearningRun D τ epsP deltaP P) (r : ℕ) (hr : r < n) :
    P {ω | ∃ i,(run.out ω)[r]?=some i ∧ ¬ IsApproxBest D τ ((run.out ω).take r) i epsP}
      ≤ ENNReal.ofReal deltaP := by
  apply conditional_partition_bound P (fun ω => (run.out ω).take r)
  · intro σ
    exact measurable_fiber_event run.out run.out_meas (fun l => l.take r=σ)
  · intro σ
    have he :
        ((fun ω => (run.out ω).take r) ⁻¹' {σ}) ∩
          {ω | ∃ i,(run.out ω)[r]?=some i ∧ ¬ IsApproxBest D τ ((run.out ω).take r) i epsP}=
        {ω | (run.out ω).take r=σ} ∩
          {ω | ∃ i,(run.out ω)[r]?=some i ∧ ¬ IsApproxBest D τ σ i epsP} := by
      ext ω
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_setOf_eq]
      constructor
      · rintro ⟨h,hb⟩;exact ⟨h,by simpa only [h] using hb⟩
      · rintro ⟨h,hb⟩;exact ⟨h,by simpa only [h] using hb⟩
    rw [he]
    exact run.pac r hr σ
lemma bad_rank_iff {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (epsP deltaP : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (run : SimpleLearningRun D τ epsP deltaP P) (ω : Ω) (r : ℕ) (hr : r < n) :
    (¬ ∃ i,(run.out ω)[r]?=some i ∧ IsApproxBest D τ ((run.out ω).take r) i epsP) ↔
      ∃ i,(run.out ω)[r]?=some i ∧ ¬ IsApproxBest D τ ((run.out ω).take r) i epsP := by
  have hlen : r < (run.out ω).length := by rw [(run.out_perm ω).2];exact hr
  constructor
  · intro hb
    refine ⟨(run.out ω)[r],List.getElem?_eq_getElem hlen,?_⟩
    intro hg
    exact hb ⟨_,List.getElem?_eq_getElem hlen,hg⟩
  · rintro ⟨i,hi,hb⟩ ⟨j,hj,hg⟩
    have he : j=i := Option.some.inj (hj.symm.trans hi)
    subst j;exact hb hg
lemma simultaneous_good_bound {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (epsP delta : ℝ) (hdelta : 0 < delta)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : SimpleLearningRun D τ epsP (delta / n) P) :
    ENNReal.ofReal (1-delta) ≤ P {ω | ∀ r < n,∃ i,(run.out ω)[r]?=some i ∧
      IsApproxBest D τ ((run.out ω).take r) i epsP} := by
  classical
  let G : Set Ω := {ω | ∀ r < n,∃ i,(run.out ω)[r]?=some i ∧
      IsApproxBest D τ ((run.out ω).take r) i epsP}
  have hm : MeasurableSet G := measurable_fiber_event run.out run.out_meas
    (fun l => ∀ r < n,∃ i,l[r]?=some i ∧ IsApproxBest D τ (l.take r) i epsP)
  let B : ℕ → Set Ω := fun r => {ω | ¬ ∃ i,(run.out ω)[r]?=some i ∧
      IsApproxBest D τ ((run.out ω).take r) i epsP}
  have hb (r : ℕ) (hr : r < n) : P (B r) ≤ ENNReal.ofReal (delta/n) := by
    have he : B r={ω | ∃ i,(run.out ω)[r]?=some i ∧ ¬ IsApproxBest D τ ((run.out ω).take r) i epsP} := by
      ext ω;exact bad_rank_iff D τ epsP (delta/n) P run ω r hr
    rw [he];exact rank_failure_bound D τ epsP (delta/n) P run r hr
  have hc : Gᶜ=⋃ r ∈ Finset.range n,B r := by
    ext ω
    simp only [G,B,mem_compl_iff,mem_setOf_eq,mem_iUnion,Finset.mem_range,not_forall,_root_.not_imp]
  have hsum : (∑ r ∈ Finset.range n,ENNReal.ofReal (delta/n)) ≤ ENNReal.ofReal delta := by
    by_cases hn : n=0
    · simp [hn]
    · rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      apply ENNReal.ofReal_le_ofReal
      have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      field_simp
      exact le_rfl
  have hbad : P Gᶜ ≤ ENNReal.ofReal delta := by
    rw [hc]
    exact (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum (fun r hr => hb r (Finset.mem_range.mp hr))).trans hsum)
  change ENNReal.ofReal (1-delta) ≤ P G
  rw [ENNReal.ofReal_sub _ hdelta.le,ENNReal.ofReal_one]
  have hcomp := prob_compl_eq_one_sub (μ := P) hm.compl
  rw [compl_compl] at hcomp
  rw [hcomp]
  exact tsub_le_tsub_left hbad 1
lemma correlated_failure_control :
    (∑ b : Bool,if b=true then (1/2 : ℚ) else 0)=1/2 ∧
    (∑ b : Bool,if b=true ∧ b=true then (1/2 : ℚ) else 0)=1/2 ∧
    (1/2 : ℚ) ≠ (1/2 : ℚ)*(1/2 : ℚ) := by norm_num
lemma empty_rank_control {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℕ → Ω → Prop) : P {ω | ∀ r < (0 : ℕ),Q r ω}=1 := by simp
end Queelius.RankingPAC

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem _root_.learning_confidence_solution {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) (τ : Θ → CustomerType n)
    (epsP delta : ℝ) (hdelta : 0 < delta)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : SimpleLearningRun D τ epsP (delta / n) P) :
    ENNReal.ofReal (1 - delta) ≤
      P {ω | ∀ r < n, ∃ i, (run.out ω)[r]? = some i ∧
              IsApproxBest D τ ((run.out ω).take r) i epsP} := by
  exact Queelius.RankingPAC.simultaneous_good_bound D τ epsP delta hdelta P run
end RankAssort.SimpleLearn

end

section
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
 theorem _root_.first_click_solution {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (hl : l.Nodup) :
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

namespace Queelius.RankingDecomposition
open RankAssort.SimpleLearn Queelius.RankingCoupling Queelius.RankingFirstClick
lemma noClick_succ {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (r : ℕ) (L : Fin n → Bool) :
    noClickTop θ l (r+1) L ↔ noClickTop θ l r L ∧ ¬ clicksAt θ l r L := by
  constructor
  · intro hs
    constructor
    · intro j hj hjr hjk
      exact hs j hj (by omega) hjk
    · rintro ⟨hr,hk,htrue⟩
      have hh := hs r hr (by omega) hk
      rw [htrue] at hh
      exact Bool.false_ne_true hh.symm
  · rintro ⟨hn,hc⟩ j hj hjr hjk
    by_cases hlt : j < r
    · exact hn j hj hlt hjk
    · have he : j=r := by omega
      subst j
      cases h : L (l.get ⟨r,hj⟩)
      · rfl
      · exact False.elim (hc ⟨hj,hjk,h⟩)
lemma noClick_difference {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (r : ℕ) :
    coupledProb θ (noClickTop θ l r)-coupledProb θ (noClickTop θ l (r+1))=
      coupledProb θ (fun L => noClickTop θ l r L ∧ clicksAt θ l r L) := by
  classical
  unfold coupledProb
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro L _
  have hs := noClick_succ θ l r L
  by_cases hn : noClickTop θ l r L <;> by_cases hc : clicksAt θ l r L <;> simp [hs,hn,hc]
lemma noClick_zero {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) :
    coupledProb θ (noClickTop θ l 0)=1 := by
  unfold coupledProb
  simpa [noClickTop] using like_mass θ
lemma anyClick_iff {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (L : Fin n → Bool) :
    (∃ j,∃ hj : j < l.length,j < θ.k ∧ L (l.get ⟨j,hj⟩)=true) ↔ ¬ noClickTop θ l l.length L := by
  constructor
  · rintro ⟨j,hj,hk,ht⟩ hn
    have hh := hn j hj hj hk
    rw [ht] at hh
    exact Bool.false_ne_true hh.symm
  · intro hn
    unfold noClickTop at hn
    push_neg at hn
    obtain ⟨j,hj,_,hk,hb⟩ := hn
    have ht : L (l.get ⟨j,hj⟩)=true := by cases h : L (l.get ⟨j,hj⟩) <;> simp_all
    exact ⟨j,hj,hk,ht⟩
lemma hook_noClick {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (hl : l.Nodup) :
    hookProb θ l=1-coupledProb θ (noClickTop θ l l.length) := by
  have hh := (first_click_solution θ l hl).1
  have he : (fun L : Fin n → Bool => ∃ j,∃ hj : j < l.length,j < θ.k ∧ L (l.get ⟨j,hj⟩)=true)=
      (fun L => ¬ noClickTop θ l l.length L) := by funext L;exact propext (anyClick_iff θ l L)
  rw [hh,he,coupled_complement]
lemma telescope (F : ℕ → ℝ) (m : ℕ) :
    (∑ r ∈ Finset.range m,(F r-F (r+1)))=F 0-F m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih];ring
lemma hook_first_sum {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (hl : l.Nodup) :
    hookProb θ l=∑ r ∈ Finset.range l.length,coupledProb θ (fun L => noClickTop θ l r L ∧ clicksAt θ l r L) := by
  have ht := telescope (fun r => coupledProb θ (noClickTop θ l r)) l.length
  simp_rw [noClick_difference θ l] at ht
  rw [noClick_zero] at ht
  rw [hook_noClick θ l hl]
  exact ht.symm
lemma integrable_hook {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (l : List (Fin n)) (hl : l.Nodup) :
    Integrable (fun θ => hookProb (τ θ) l) D := by
  have he : (fun θ => hookProb (τ θ) l)=
      (fun θ => 1-coupledProb (τ θ) (noClickTop (τ θ) l l.length)) := by
    funext θ;exact hook_noClick (τ θ) l hl
  rw [he]
  exact (integrable_const (1:ℝ)).sub (integrable_coupled D τ hτ _ (fun L => measurable_noClick τ hτ l l.length L))
lemma expected_hook_sum {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (l : List (Fin n)) (hl : l.Nodup) :
    expHook D τ l=∑ r ∈ Finset.range l.length,firstClickTerm D τ l r := by
  have he : (fun θ => hookProb (τ θ) l)=
      (fun θ => ∑ r ∈ Finset.range l.length,coupledProb (τ θ) (fun L => noClickTop (τ θ) l r L ∧ clicksAt (τ θ) l r L)) := by
    funext θ;exact hook_first_sum (τ θ) l hl
  unfold expHook firstClickTerm
  rw [he,integral_finsetSum]
  intro r hr
  apply integrable_coupled D τ hτ
  intro L
  exact (measurable_noClick τ hτ l r L).inter (measurable_clicksAt τ hτ l r L)
lemma prefix_noClick_iff {n : ℕ} (θ : CustomerType n) (σ : List (Fin n)) (i : Fin n) (L : Fin n → Bool) :
    noClickTop θ (σ++[i]) σ.length L ↔ noClickTop θ σ σ.length L := by
  constructor
  · intro hn j hj hjr hjk
    have hja : j < (σ++[i]).length := by simp;omega
    have he : (σ++[i]).get ⟨j,hja⟩=σ.get ⟨j,hj⟩ := by
      simp only [List.get_eq_getElem,List.getElem_append_left hj]
    rw [← he]
    exact hn j hja hjr hjk
  · intro hn j hj hjr hjk
    have he : (σ++[i]).get ⟨j,hj⟩=σ.get ⟨j,hjr⟩ := by
      simp only [List.get_eq_getElem,List.getElem_append_left hjr]
    rw [he]
    exact hn j hjr hjr hjk
lemma appended_gain {n : ℕ} (θ : CustomerType n) (σ : List (Fin n)) (i : Fin n) (happ : (σ++[i]).Nodup) :
    hookProb θ (σ++[i])-hookProb θ σ=
      coupledProb θ (fun L => noClickTop θ (σ++[i]) σ.length L ∧ clicksAt θ (σ++[i]) σ.length L) := by
  have hp : σ.Nodup := (List.nodup_append.mp happ).1
  have he : noClickTop θ (σ++[i]) σ.length=noClickTop θ σ σ.length := by
    funext L;exact propext (prefix_noClick_iff θ σ i L)
  have hs := noClick_difference θ (σ++[i]) σ.length
  rw [he] at hs
  have hlen : (σ++[i]).length=σ.length+1 := by simp
  rw [hook_noClick θ (σ++[i]) happ,hook_noClick θ σ hp,hlen]
  simp only [he]
  linarith
lemma expected_appended_gain {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (σ : List (Fin n)) (i : Fin n) (happ : (σ++[i]).Nodup) :
    firstClickTerm D τ (σ++[i]) σ.length=margBenefit D τ σ i := by
  have hp : σ.Nodup := (List.nodup_append.mp happ).1
  unfold firstClickTerm margBenefit expHook
  rw [← integral_sub (integrable_hook D τ hτ (σ++[i]) happ) (integrable_hook D τ hτ σ hp)]
  apply integral_congr_ae
  exact ae_of_all _ (fun θ => (appended_gain (τ θ) σ i happ).symm)
end Queelius.RankingDecomposition
namespace RankAssort.SimpleLearn
open MeasureTheory
 theorem _root_.hook_decomposition_solution {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) :
    (∀ l : List (Fin n), l.Nodup →
        expHook D τ l = ∑ r ∈ Finset.range l.length, firstClickTerm D τ l r) ∧
      (∀ (σ : List (Fin n)) (i : Fin n), (σ ++ [i]).Nodup →
        firstClickTerm D τ (σ ++ [i]) σ.length = margBenefit D τ σ i) := by
  exact ⟨Queelius.RankingDecomposition.expected_hook_sum D τ hτ,
    Queelius.RankingDecomposition.expected_appended_gain D τ hτ⟩
end RankAssort.SimpleLearn

namespace Queelius.RankingComparison
open RankAssort.SimpleLearn Queelius.RankingCoupling Queelius.RankingDecomposition
lemma event_noClick_step {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (E : (Fin n → Bool) → Prop) (r : ℕ) :
    coupledProb θ (fun L => E L ∧ noClickTop θ l r L)-
      coupledProb θ (fun L => E L ∧ noClickTop θ l (r+1) L)=
      coupledProb θ (fun L => E L ∧ noClickTop θ l r L ∧ clicksAt θ l r L) := by
  classical
  unfold coupledProb
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro L _
  have hs := noClick_succ θ l r L
  by_cases he : E L <;> by_cases hn : noClickTop θ l r L <;> by_cases hc : clicksAt θ l r L <;> simp [hs,he,hn,hc]
lemma event_noClick_zero {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (E : (Fin n → Bool) → Prop) :
    coupledProb θ (fun L => E L ∧ noClickTop θ l 0 L)=coupledProb θ E := by
  have he : (fun L : Fin n → Bool => E L ∧ noClickTop θ l 0 L)=E := by
    funext L
    apply propext
    constructor
    · exact And.left
    · intro hE
      exact ⟨hE,fun j _ hj _ => False.elim (Nat.not_lt_zero j hj)⟩
  exact congrArg (coupledProb θ) he
lemma event_first_sum {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (E : (Fin n → Bool) → Prop) :
    coupledProb θ E-coupledProb θ (fun L => E L ∧ noClickTop θ l l.length L)=
      ∑ r ∈ Finset.range l.length,coupledProb θ (fun L => E L ∧ noClickTop θ l r L ∧ clicksAt θ l r L) := by
  have hh := telescope (fun r => coupledProb θ (fun L => E L ∧ noClickTop θ l r L)) l.length
  simp_rw [event_noClick_step θ l E] at hh
  rw [event_noClick_zero] at hh
  exact hh.symm
lemma hook_comparison {n : ℕ} (θ : CustomerType n) (l l' : List (Fin n)) (hl : l.Nodup) (hl' : l'.Nodup) :
    hookProb θ l' ≤ hookProb θ l+
      ∑ r ∈ Finset.range l'.length,coupledProb θ (fun L => noClickTop θ l r L ∧ noClickTop θ l' r L ∧ clicksAt θ l' r L) := by
  have he := event_first_sum θ l' (noClickTop θ l l.length)
  have hm := coupled_mono θ (fun L => noClickTop θ l l.length L ∧ noClickTop θ l' l'.length L)
    (noClickTop θ l' l'.length) (fun L h => h.2)
  have hs := Finset.sum_le_sum (s := Finset.range l'.length) (fun r _ =>
    coupled_mono θ (fun L => noClickTop θ l l.length L ∧ noClickTop θ l' r L ∧ clicksAt θ l' r L)
      (fun L => noClickTop θ l r L ∧ noClickTop θ l' r L ∧ clicksAt θ l' r L) (by
        intro L h
        exact ⟨fun j hj _ hk => h.1 j hj hj hk,h.2⟩))
  rw [hook_noClick θ l' hl',hook_noClick θ l hl]
  linarith
lemma expected_hook_comparison {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (l l' : List (Fin n)) (hl : l.Nodup) (hl' : l'.Nodup) :
    expHook D τ l' ≤ expHook D τ l+∑ r ∈ Finset.range l'.length,jointTerm D τ l l' r := by
  let B := fun θ => ∑ r ∈ Finset.range l'.length,coupledProb (τ θ)
    (fun L => noClickTop (τ θ) l r L ∧ noClickTop (τ θ) l' r L ∧ clicksAt (τ θ) l' r L)
  have hi (r : ℕ) : Integrable (fun θ => coupledProb (τ θ)
      (fun L => noClickTop (τ θ) l r L ∧ noClickTop (τ θ) l' r L ∧ clicksAt (τ θ) l' r L)) D := by
    apply integrable_coupled D τ hτ
    intro L
    exact (measurable_noClick τ hτ l r L).inter
      ((measurable_noClick τ hτ l' r L).inter (measurable_clicksAt τ hτ l' r L))
  have hB : Integrable B D := integrable_finsetSum _ (fun r _ => hi r)
  have hh := integral_mono (integrable_hook D τ hτ l' hl') ((integrable_hook D τ hτ l hl).add hB)
    (fun θ => hook_comparison (τ θ) l l' hl hl')
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_hook D τ hτ l hl) hB] at hh
  have he : (∫ θ,B θ ∂D)=∑ r ∈ Finset.range l'.length,jointTerm D τ l l' r := by
    dsimp only [B]
    rw [integral_finsetSum _ (fun r _ => hi r)]
    rfl
  rw [he] at hh
  exact hh
end Queelius.RankingComparison
namespace RankAssort.SimpleLearn
open MeasureTheory
 theorem _root_.hook_comparison_solution {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (l piStar : List (Fin n)) (hl : l.Nodup) (hlen : l.length = n)
    (hs : piStar.Nodup) (hslen : piStar.length = n) :
    expHook D τ piStar ≤ expHook D τ l + ∑ r ∈ Finset.range n, jointTerm D τ l piStar r := by
  simpa only [hslen] using Queelius.RankingComparison.expected_hook_comparison D τ hτ l piStar hl hs
end RankAssort.SimpleLearn

namespace Queelius.RankingComparison
open RankAssort.SimpleLearn
lemma products_positive {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) : 0 < n := by
  obtain ⟨θ⟩ := MeasureTheory.nonempty_of_isProbabilityMeasure D
  have hk := (τ θ).one_le_k
  have hn := (τ θ).k_le
  omega
end Queelius.RankingComparison

namespace Queelius.RankingApproximation
open RankAssort.SimpleLearn Queelius.RankingCoupling Queelius.RankingDecomposition Queelius.RankingComparison
lemma prefix_noClick_iff_full {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (r : ℕ)
    (hr : r ≤ l.length) (i : Fin n) (L : Fin n → Bool) :
    noClickTop θ (l.take r++[i]) r L ↔ noClickTop θ l r L := by
  constructor
  · intro hn j hj hjr hjk
    have htake : j < (l.take r).length := by rw [List.length_take_of_le hr];exact hjr
    have hja : j < (l.take r++[i]).length := by simp;omega
    have he : (l.take r++[i]).get ⟨j,hja⟩=l.get ⟨j,hj⟩ := by
      simp only [List.get_eq_getElem,List.getElem_append_left htake,List.getElem_take]
    rw [← he]
    exact hn j hja hjr hjk
  · exact prefix_noClick θ l r hr i L
lemma prefix_click_iff_full {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (r : ℕ)
    (hr : r < l.length) (i : Fin n) (hi : l[r]?=some i) (L : Fin n → Bool) :
    clicksAt θ (l.take r++[i]) r L ↔ clicksAt θ l r L := by
  have htake : (l.take r).length=r := List.length_take_of_le hr.le
  have hli : l.get ⟨r,hr⟩=i := by
    rw [List.getElem?_eq_getElem hr] at hi
    simpa only [List.get_eq_getElem] using Option.some.inj hi
  have hlen : r < (l.take r++[i]).length := by simp [htake]
  have hai : (l.take r++[i]).get ⟨r,hlen⟩=i := by
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_right (show (l.take r).length ≤ r by omega)]
    simp [htake]
  constructor
  · rintro ⟨ha,hk,hL⟩
    refine ⟨hr,hk,?_⟩
    simpa only [hli,hai] using hL
  · rintro ⟨ha,hk,hL⟩
    exact prefix_click θ l r hr.le i L hk (by simpa only [hli] using hL)
lemma first_prefix {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (l : List (Fin n)) (r : ℕ) (hr : r < l.length)
    (i : Fin n) (hi : l[r]?=some i) :
    firstClickTerm D τ (l.take r++[i]) r=firstClickTerm D τ l r := by
  unfold firstClickTerm
  apply integral_congr_ae
  apply ae_of_all
  intro θ
  apply congrArg (coupledProb (τ θ))
  funext L
  exact propext (and_congr (prefix_noClick_iff_full (τ θ) l r hr.le i L)
    (prefix_click_iff_full (τ θ) l r hr i hi L))
lemma repeated_prefix_zero {n : ℕ} (θ : CustomerType n) (σ : List (Fin n))
    (i : Fin n) (hi : i ∈ σ) :
    coupledProb θ (fun L => noClickTop θ (σ++[i]) σ.length L ∧ clicksAt θ (σ++[i]) σ.length L)=0 := by
  classical
  unfold coupledProb
  apply Finset.sum_eq_zero
  intro L _
  have hn : ¬ (noClickTop θ (σ++[i]) σ.length L ∧ clicksAt θ (σ++[i]) σ.length L) := by
    rintro ⟨hno,hclick⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hi
    obtain ⟨hr,hk,hL⟩ := hclick
    have hf := ((prefix_noClick_iff θ σ i L).mp hno) j.val j.isLt j.isLt (lt_trans j.isLt hk)
    rw [hj] at hf
    have hai : (σ++[i]).get ⟨σ.length,hr⟩=i := by
      simp only [List.get_eq_getElem,List.getElem_append_right (le_refl _)];simp
    rw [hai] at hL
    exact Bool.false_ne_true (hf.symm.trans hL)
  simp [hn]
lemma first_nonneg {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (l : List (Fin n)) (r : ℕ) : 0 ≤ firstClickTerm D τ l r :=
  integral_nonneg (fun θ => (coupled_bounds (τ θ) _).1)
lemma joint_approx {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (l l' : List (Fin n)) (hl : l.Nodup)
    (r : ℕ) (hr : r < l.length) (i j : Fin n) (hi : l[r]?=some i) (hj : l'[r]?=some j)
    (tol : ℝ) (hgood : IsApproxBest D τ (l.take r) i tol) :
    jointTerm D τ l l' r ≤ firstClickTerm D τ l r+tol := by
  have htol : 0 ≤ tol := by have hh := hgood.2 i hgood.1;linarith
  have hcmp := joint_bound D τ hτ l l' r hr.le j hj
  have hlen : (l.take r).length=r := List.length_take_of_le hr.le
  by_cases hjmem : j ∈ l.take r
  · have hz : firstClickTerm D τ (l.take r++[j]) r=0 := by
      unfold firstClickTerm
      have he : (fun θ => coupledProb (τ θ) (fun L =>
          noClickTop (τ θ) (l.take r++[j]) r L ∧ clicksAt (τ θ) (l.take r++[j]) r L))=0 := by
        funext θ
        simpa only [hlen,Pi.zero_apply] using repeated_prefix_zero (τ θ) (l.take r) j hjmem
      rw [he];simp
    rw [hz] at hcmp
    linarith [first_nonneg D τ l r]
  · have hpre : (l.take r).Nodup := hl.take
    have hndj : (l.take r++[j]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hpre,by simp,?_⟩
      intro a ha b hb he
      have hb' : b=j := List.mem_singleton.mp hb
      exact hjmem ((he.trans hb') ▸ ha)
    have hndi : (l.take r++[i]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hpre,by simp,?_⟩
      intro a ha b hb he
      have hb' : b=i := List.mem_singleton.mp hb
      exact hgood.1 ((he.trans hb') ▸ ha)
    have heJ := expected_appended_gain D τ hτ (l.take r) j hndj
    have heI := expected_appended_gain D τ hτ (l.take r) i hndi
    rw [hlen] at heJ heI
    rw [heJ] at hcmp
    have hbest := hgood.2 j hjmem
    rw [← heI,first_prefix D τ l r hr i hi] at hbest
    linarith
lemma approx_bound {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (eps : ℝ)
    (piT : List (Fin n)) (hT : piT.Nodup) (hTlen : piT.length=n)
    (hgood : ∀ r < n,∃ i,piT[r]?=some i ∧ IsApproxBest D τ (piT.take r) i (2*eps/n))
    (piStar : List (Fin n)) (hs : piStar.Nodup) (hslen : piStar.length=n) :
    expHook D τ piStar ≤ 2*expHook D τ piT+2*eps := by
  have hcmp := hook_comparison_solution D τ hτ piT piStar hT hTlen hs hslen
  have hsumb : (∑ r ∈ Finset.range n,jointTerm D τ piT piStar r) ≤
      ∑ r ∈ Finset.range n,(firstClickTerm D τ piT r+2*eps/n) := by
    apply Finset.sum_le_sum
    intro r hr
    have hrn := Finset.mem_range.mp hr
    obtain ⟨i,hi,hgoodi⟩ := hgood r hrn
    let j := piStar.get ⟨r,by omega⟩
    have hj : piStar[r]?=some j := by simp [j,List.getElem?_eq_getElem (show r < piStar.length by omega)]
    exact joint_approx D τ hτ piT piStar hT r (by omega) i j hi hj (2*eps/n) hgoodi
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (products_positive D τ))
  have he : (∑ r ∈ Finset.range n,(firstClickTerm D τ piT r+2*eps/n))=
      expHook D τ piT+2*eps := by
    have hsum := expected_hook_sum D τ hτ piT hT
    rw [hTlen] at hsum
    rw [Finset.sum_add_distrib,← hsum]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  rw [he] at hsumb
  linarith
end Queelius.RankingApproximation

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem _root_.approximation_solution {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (eps : ℝ)
    (piT : List (Fin n)) (hT : piT.Nodup) (hTlen : piT.length = n)
    (hgood : ∀ r < n, ∃ i, piT[r]? = some i ∧ IsApproxBest D τ (piT.take r) i (2 * eps / n))
    (piStar : List (Fin n)) (hs : piStar.Nodup) (hslen : piStar.length = n) :
    expHook D τ piStar ≤ 2 * expHook D τ piT + 2 * eps := by
  exact Queelius.RankingApproximation.approx_bound D τ hτ eps piT hT hTlen hgood piStar hs hslen
end RankAssort.SimpleLearn

end

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem _root_.solution {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : SimpleLearningRun D τ (2 * eps / n) (delta / n) P) :
    ENNReal.ofReal (1 - delta) ≤
      P {ω | ∀ piStar : List (Fin n), piStar.Nodup → piStar.length = n →
              (1 / 2 : ℝ) * expHook D τ piStar - eps ≤ expHook D τ (run.out ω)} := by
  have hg := learning_confidence_solution D τ (2*eps/n) delta hdelta P run
  apply hg.trans
  apply measure_mono
  intro ω hω piStar hs hslen
  have ha := approximation_solution D τ hτ eps (run.out ω) (run.out_perm ω).1
    (run.out_perm ω).2 hω piStar hs hslen
  linarith
end RankAssort.SimpleLearn
