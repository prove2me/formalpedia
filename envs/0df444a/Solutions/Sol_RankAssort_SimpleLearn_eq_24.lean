-- Prove2me | solution 1 for RankAssort.SimpleLearn.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T04:49:32.220989+00:00
-- url     : https://prove2.me/submissions/c0f71673-b0cf-4016-865a-34b83b77e3ee

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Algorithm
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
theorem _root_.solution {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) (τ : Θ → CustomerType n)
    (epsP delta : ℝ) (hdelta : 0 < delta)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : SimpleLearningRun D τ epsP (delta / n) P) :
    ENNReal.ofReal (1 - delta) ≤
      P {ω | ∀ r < n, ∃ i, (run.out ω)[r]? = some i ∧
              IsApproxBest D τ ((run.out ω).take r) i epsP} := by
  exact Queelius.RankingPAC.simultaneous_good_bound D τ epsP delta hdelta P run
end RankAssort.SimpleLearn
