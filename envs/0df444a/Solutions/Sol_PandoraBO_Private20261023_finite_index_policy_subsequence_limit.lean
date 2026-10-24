-- Prove2me | solution 1 for PandoraBO.Private20261023.finite_index_policy_subsequence_limit
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:25.403985+00:00
-- url     : https://prove2.me/submissions/6ecd1906-2383-4f54-a114-df86ecb54a77

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_policy_expectations_converge_of_eventual_decisions
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace PandoraBO.Private20261023.FiniteIndexPolicyLimit

abbrev Table (n : ℕ) := Box n × ((Box n → Bool) → Decision n)

def Compatible {n : ℕ} (t : Table n) (z : Box n → EReal) : Prop :=
  (∀ i, z i ≤ z t.1) ∧
  (∀ m, (t.2 m = none → ∀ i, m i ≠ true) ∧
    (∀ i, t.2 m = some i → m i = true ∧ ∀ j, m j = true → z j ≤ z i))

def IndexRules {n : ℕ} (z : Box n → EReal) (π : Policy n) : Prop :=
  (∀ u i, z i ≤ z (π.first u)) ∧
  (∀ h u, validHistory h →
    match π.next (h, u) with
    | none => ∀ i, ¬ wasOpened h i → z i ≤ (historyReward h : EReal)
    | some i => (historyReward h : EReal) ≤ z i ∧
        ∀ j, ¬ wasOpened h j → z j ≤ z i)

def candidates {n : ℕ} (m : Box n → Bool) : Finset (Box n) :=
  Finset.univ.filter (fun i => m i = true)

def best {n : ℕ} (z : Box n → EReal) (m : Box n → Bool) : Decision n :=
  if hs : (candidates m).Nonempty then
    some (Classical.choose (Finset.exists_max_image (candidates m) z hs))
  else none

theorem best_some {n : ℕ} (z : Box n → EReal) (m : Box n → Bool) (i : Box n)
    (hi : best z m = some i) :
    m i = true ∧ ∀ j, m j = true → z j ≤ z i := by
  by_cases hs : (candidates m).Nonempty
  · have hchoice : Classical.choose (Finset.exists_max_image (candidates m) z hs) = i := by
      simpa only [best, dif_pos hs, Option.some.injEq] using hi
    have hspec := Classical.choose_spec (Finset.exists_max_image (candidates m) z hs)
    rw [hchoice] at hspec
    exact ⟨(Finset.mem_filter.mp hspec.1).2, fun j hj =>
      hspec.2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  · have hbad : (none : Decision n) = some i := by
      simpa only [best, dif_neg hs] using hi
    cases hbad

theorem best_none {n : ℕ} (z : Box n → EReal) (m : Box n → Bool)
    (hstop : best z m = none) : ∀ i, m i ≠ true := by
  intro i hi
  have hs : (candidates m).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hbad : (some (Classical.choose
      (Finset.exists_max_image (candidates m) z hs)) : Decision n) = none := by
    simpa only [best, dif_pos hs] using hstop
  cases hbad

def canonicalTable {n : ℕ} (z : Box n → EReal) : Table n :=
  ⟨Classical.choose (Finset.exists_max_image (Finset.univ : Finset (Box n)) z
    ⟨0, Finset.mem_univ _⟩), best z⟩

theorem canonicalTable_compatible {n : ℕ} (z : Box n → EReal) :
    Compatible (canonicalTable z) z := by
  refine ⟨?_, fun m => ⟨best_none z m, best_some z m⟩⟩
  intro i
  exact (Classical.choose_spec (Finset.exists_max_image
    (Finset.univ : Finset (Box n)) z ⟨0, Finset.mem_univ _⟩)).2 i (Finset.mem_univ _)

theorem occupied_measurable {n : ℕ} (k : Fin (n + 1)) :
    MeasurableSet {h : History n | occupied h k} :=
  (measurableSet_singleton true).preimage (measurable_pi_apply k).fst

theorem wasOpened_measurable {n : ℕ} (i : Box n) :
    MeasurableSet {h : History n | wasOpened h i} := by
  have heq : {h : History n | wasOpened h i} =
      ⋃ k : Fin (n + 1), {h : History n | occupied h k ∧ observedBox h k = i} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, wasOpened]
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  exact (occupied_measurable k).inter
    ((measurableSet_singleton i).preimage (measurable_pi_apply k).snd.fst)

theorem fold_reward_measurable {n : ℕ} (ks : List (Fin (n + 1)))
    (f : History n → ℝ) (hf : Measurable f) :
    Measurable (fun h => ks.foldl
      (fun incumbent k => if occupied h k then max incumbent (observedReward h k)
        else incumbent) (f h)) := by
  induction ks generalizing f with
  | nil => exact hf
  | cons k ks ih =>
      exact ih (fun h => if occupied h k then max (f h) (observedReward h k) else f h)
        (Measurable.ite (occupied_measurable k)
          (hf.max (measurable_pi_apply k).snd.snd) hf)

theorem historyReward_measurable {n : ℕ} : Measurable (@historyReward n) :=
  fold_reward_measurable (List.finRange (n + 1))
    (fun h : History n => observedReward h 0) (measurable_pi_apply 0).snd.snd

/-- A weak mask opens on equality; a strict mask stops on equality. -/
def eligible {n : ℕ} (z : Box n → EReal) (weak : Bool) (h : History n) (i : Box n) : Prop :=
  ¬ wasOpened h i ∧ if weak then (historyReward h : EReal) ≤ z i
    else (historyReward h : EReal) < z i

def mask {n : ℕ} (z : Box n → EReal) (weak : Bool) (h : History n) : Box n → Bool :=
  fun i => if eligible z weak h i then true else false

theorem mask_true {n : ℕ} (z : Box n → EReal) (weak : Bool) (h : History n) (i : Box n) :
    mask z weak h i = true ↔ eligible z weak h i := by simp [mask]

theorem mask_measurable {n : ℕ} (z : Box n → EReal) (weak : Bool) :
    Measurable (mask z weak) := by
  apply measurable_pi_lambda
  intro i
  have hreward : Measurable (fun h : History n => (historyReward h : EReal)) :=
    historyReward_measurable.coe_real_ereal
  have heligible : MeasurableSet {h : History n | eligible z weak h i} := by
    cases weak
    · exact (wasOpened_measurable i).compl.inter (measurableSet_lt hreward measurable_const)
    · exact (wasOpened_measurable i).compl.inter (measurableSet_le hreward measurable_const)
  exact Measurable.ite heligible measurable_const measurable_const

def tablePolicy {n : ℕ} (t : Table n) (z : Box n → EReal) (weak : Bool)
    (hm : ∀ m i, t.2 m = some i → m i = true) : Policy n := {
  first := fun _ => t.1
  first_measurable := measurable_const
  next := fun p => t.2 (mask z weak p.1)
  next_measurable := (measurable_of_finite t.2).comp ((mask_measurable z weak).comp measurable_fst)
  next_unopened := by
    intro h u i hi
    exact ((mask_true z weak h i).mp (hm (mask z weak h) i hi)).1
}

theorem eligible_le {n : ℕ} (z : Box n → EReal) (weak : Bool) (h : History n) (i : Box n)
    (hi : eligible z weak h i) : (historyReward h : EReal) ≤ z i := by
  cases weak
  · exact hi.2.le
  · exact hi.2

theorem ineligible_le {n : ℕ} (z : Box n → EReal) (weak : Bool) (h : History n) (i : Box n)
    (hu : ¬ wasOpened h i) (hi : ¬ eligible z weak h i) : z i ≤ (historyReward h : EReal) := by
  cases weak
  · exact le_of_not_gt (fun hlt => hi ⟨hu, hlt⟩)
  · exact (lt_of_not_ge (fun hle => hi ⟨hu, hle⟩)).le

theorem tablePolicy_rules {n : ℕ} (t : Table n) (z : Box n → EReal) (weak : Bool)
    (ht : Compatible t z) :
    IndexRules z (tablePolicy t z weak (fun m i hi => ((ht.2 m).2 i hi).1)) := by
  refine ⟨fun u i => ht.1 i, ?_⟩
  intro h u _
  change match t.2 (mask z weak h) with
    | none => ∀ i, ¬ wasOpened h i → z i ≤ (historyReward h : EReal)
    | some i => (historyReward h : EReal) ≤ z i ∧ ∀ j, ¬ wasOpened h j → z j ≤ z i
  cases hnext : t.2 (mask z weak h) with
  | none =>
      intro i hu
      exact ineligible_le z weak h i hu (fun hi =>
        (ht.2 (mask z weak h)).1 hnext i ((mask_true z weak h i).mpr hi))
  | some i =>
      obtain ⟨hi, hmax⟩ := (ht.2 (mask z weak h)).2 i hnext
      have hle := eligible_le z weak h i ((mask_true z weak h i).mp hi)
      refine ⟨hle, fun j hu => ?_⟩
      by_cases hj : eligible z weak h j
      · exact hmax j ((mask_true z weak h j).mpr hj)
      · exact (ineligible_le z weak h j hu hj).trans hle

def canonicalPolicy {n : ℕ} (z : Box n → EReal) : Policy n :=
  tablePolicy (canonicalTable z) z false
    (fun m i hi => ((canonicalTable_compatible z).2 m).2 i hi |>.1)

theorem canonicalPolicy_rules {n : ℕ} (z : Box n → EReal) :
    IndexRules z (canonicalPolicy z) := tablePolicy_rules _ _ _ (canonicalTable_compatible z)

theorem compatible_limit {n : ℕ} (t : Table n)
    (zs : ℕ → Box n → EReal) (z : Box n → EReal)
    (hcompat : ∀ k, Compatible t (zs k))
    (hlim : ∀ i, Tendsto (fun k => zs k i) atTop (nhds (z i))) : Compatible t z := by
  refine ⟨fun i => le_of_tendsto_of_tendsto' (hlim i) (hlim t.1)
    (fun k => (hcompat k).1 i), ?_⟩
  intro m
  refine ⟨(hcompat 0).2 m |>.1, fun i hi => ⟨((hcompat 0).2 m |>.2 i hi).1, ?_⟩⟩
  intro j hj
  exact le_of_tendsto_of_tendsto' (hlim j) (hlim i)
    (fun k => ((hcompat k).2 m |>.2 i hi).2 j hj)

/-- Approaching thresholds from below gives strict stopping at the limit;
    approaching strictly from above gives continuation at equality. -/
theorem mask_eventually_eq {n : ℕ} (zs : ℕ → Box n → EReal) (z : Box n → EReal)
    (weak : Bool) (hlim : ∀ i, Tendsto (fun k => zs k i) atTop (nhds (z i)))
    (hside : ∀ i k, if weak then z i < zs k i else zs k i ≤ z i)
    (h : History n) : ∀ᶠ k in atTop, mask (zs k) false h = mask z weak h := by
  have heach : ∀ i, ∀ᶠ k in atTop, mask (zs k) false h i = mask z weak h i := by
    intro i
    by_cases hu : wasOpened h i
    · exact Eventually.of_forall (fun k => by simp [mask, eligible, hu])
    cases weak
    · by_cases hr : (historyReward h : EReal) < z i
      · filter_upwards [(tendsto_order.mp (hlim i)).1 _ hr] with k hk
        simp [mask, eligible, hu, hr, hk]
      · exact Eventually.of_forall (fun k => by
          have hk : ¬ (historyReward h : EReal) < zs k i :=
            fun hlt => hr (hlt.trans_le (hside i k))
          simp [mask, eligible, hu, hr, hk])
    · by_cases hr : (historyReward h : EReal) ≤ z i
      · exact Eventually.of_forall (fun k => by
          have hk : (historyReward h : EReal) < zs k i := hr.trans_lt (hside i k)
          simp [mask, eligible, hu, hr, hk])
      · filter_upwards [(tendsto_order.mp (hlim i)).2 _ (lt_of_not_ge hr)] with k hk
        have hnot : ¬ (historyReward h : EReal) < zs k i := not_lt_of_ge hk.le
        simp [mask, eligible, hu, hr, hnot]
  exact (Filter.eventually_all.mpr heach).mono (fun k hk => funext hk)

theorem finite_constant_subsequence {α : Type*} [Finite α] (tables : ℕ → α) :
    ∃ table : α, ∃ extraction : ℕ → ℕ,
      StrictMono extraction ∧ ∀ k, tables (extraction k) = table := by
  have hfreq : ∃ᶠ k in atTop, ∃ table : α, tables k = table :=
    (Filter.Eventually.of_forall (fun k => ⟨tables k, rfl⟩)).frequently
  obtain ⟨table, htable⟩ := Filter.frequently_exists.mp hfreq
  obtain ⟨extraction, hmono, hconstant⟩ := extraction_of_frequently_atTop htable
  exact ⟨table, extraction, hmono, hconstant⟩

theorem canonical_policy_subsequence {n : ℕ} (M : Instance n)
    (zs : ℕ → Box n → EReal) (z : Box n → EReal)
    (weak : Bool) (hlim : ∀ i, Tendsto (fun k => zs k i) atTop (nhds (z i)))
    (hside : ∀ i k, if weak then z i < zs k i else zs k i ≤ z i) :
    ∃ extraction : ℕ → ℕ, ∃ π : Policy n,
      StrictMono extraction ∧ IndexRules z π ∧
      Tendsto (fun k => expectedCost M (canonicalPolicy (zs (extraction k)))) atTop
        (nhds (expectedCost M π)) ∧
      Tendsto (fun k => expectedReward M (canonicalPolicy (zs (extraction k)))) atTop
        (nhds (expectedReward M π)) := by
  obtain ⟨t, extraction, hextract, htable⟩ := finite_constant_subsequence
    (fun k => canonicalTable (zs k))
  have hcompat : ∀ k, Compatible t (zs (extraction k)) := by
    intro k
    rw [← htable k]
    exact canonicalTable_compatible _
  have hsub : ∀ i, Tendsto (fun k => zs (extraction k) i) atTop (nhds (z i)) :=
    fun i => (hlim i).comp hextract.tendsto_atTop
  have ht := compatible_limit t (fun k => zs (extraction k)) z hcompat hsub
  let π := tablePolicy t z weak (fun m i hi => ((ht.2 m).2 i hi).1)
  refine ⟨extraction, π, hextract, tablePolicy_rules t z weak ht, ?_⟩
  have hfirst : ∀ u : ℝ, ∀ᶠ k in atTop,
      (canonicalPolicy (zs (extraction k))).first u = π.first u := by
    intro u
    exact Eventually.of_forall (fun k => congrArg Prod.fst (htable k))
  have hnext : ∀ h : History n, ∀ u : ℝ, ∀ᶠ k in atTop,
      (canonicalPolicy (zs (extraction k))).next (h,u) = π.next (h,u) := by
    intro h u
    filter_upwards [mask_eventually_eq (fun k => zs (extraction k)) z weak hsub
      (fun i k => hside i (extraction k)) h] with k hk
    change (canonicalTable (zs (extraction k))).2 (mask (zs (extraction k)) false h) =
      t.2 (mask z weak h)
    rw [htable k, hk]
  exact (policy_expectations_converge_of_eventual_decisions M
    (fun k => canonicalPolicy (zs (extraction k))) π hfirst hnext).2

end PandoraBO.Private20261023.FiniteIndexPolicyLimit

theorem solution {n : ℕ} (M : PandoraBO.Instance n)
    (zs : ℕ → PandoraBO.Box n → EReal) (z : PandoraBO.Box n → EReal)
    (weak : Bool) (hlim : ∀ i, Tendsto (fun k => zs k i) atTop (nhds (z i)))
    (hside : ∀ i k, if weak then z i < zs k i else zs k i ≤ z i) :
    ∃ policies : ℕ → PandoraBO.Policy n,
      (∀ j k, zs j = zs k → policies j = policies k) ∧
      (∀ k, (∀ u i, zs k i ≤ zs k ((policies k).first u)) ∧
        (∀ h u, PandoraBO.validHistory h →
          match (policies k).next (h,u) with
          | none => ∀ i, ¬ PandoraBO.wasOpened h i →
              zs k i ≤ (PandoraBO.historyReward h : EReal)
          | some i => (PandoraBO.historyReward h : EReal) ≤ zs k i ∧
              ∀ j, ¬ PandoraBO.wasOpened h j → zs k j ≤ zs k i)) ∧
      ∃ extraction : ℕ → ℕ, ∃ π : PandoraBO.Policy n,
        StrictMono extraction ∧
        ((∀ u i, z i ≤ z (π.first u)) ∧
          (∀ h u, PandoraBO.validHistory h →
            match π.next (h,u) with
            | none => ∀ i, ¬ PandoraBO.wasOpened h i →
                z i ≤ (PandoraBO.historyReward h : EReal)
            | some i => (PandoraBO.historyReward h : EReal) ≤ z i ∧
                ∀ j, ¬ PandoraBO.wasOpened h j → z j ≤ z i)) ∧
        Tendsto (fun k => PandoraBO.expectedCost M (policies (extraction k))) atTop
          (nhds (PandoraBO.expectedCost M π)) ∧
        Tendsto (fun k => PandoraBO.expectedReward M (policies (extraction k))) atTop
          (nhds (PandoraBO.expectedReward M π)) := by
  refine ⟨fun k => PandoraBO.Private20261023.FiniteIndexPolicyLimit.canonicalPolicy (zs k),
    fun j k heq => congrArg PandoraBO.Private20261023.FiniteIndexPolicyLimit.canonicalPolicy heq,
    fun k => PandoraBO.Private20261023.FiniteIndexPolicyLimit.canonicalPolicy_rules (zs k), ?_⟩
  exact PandoraBO.Private20261023.FiniteIndexPolicyLimit.canonical_policy_subsequence
    M zs z weak hlim hside
