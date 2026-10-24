-- Prove2me | solution 1 for PandoraBO.Private20261023.gittins_policy_exists
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:51:41.47804+00:00
-- url     : https://prove2.me/submissions/38ee7bd4-b279-4037-8db5-3acf14677da3

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_reservation_index_exists_unique
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false

noncomputable section

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PandoraBO.Private20261023.GittinsExistence

theorem occupied_measurable {n : ℕ} (k : Fin (n + 1)) :
    MeasurableSet {h : History n | occupied h k} := by
  exact (measurableSet_singleton true).preimage (measurable_pi_apply k).fst

theorem observedReward_measurable {n : ℕ} (k : Fin (n + 1)) :
    Measurable (fun h : History n => observedReward h k) :=
  (measurable_pi_apply k).snd.snd

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
  classical
  induction ks generalizing f with
  | nil => exact hf
  | cons k ks ih =>
      exact ih (fun h => if occupied h k then max (f h) (observedReward h k) else f h)
        (Measurable.ite (occupied_measurable k)
          (hf.max (observedReward_measurable k)) hf)

theorem historyReward_measurable {n : ℕ} : Measurable (@historyReward n) := by
  classical
  exact fold_reward_measurable (List.finRange (n + 1))
    (fun h : History n => observedReward h 0) (observedReward_measurable 0)

/-- Eligibility is strict, so this deterministic policy stops on index ties. -/
def eligibleMask {n : ℕ} (z : Box n → ℝ) (h : History n) : Box n → Bool := by
  classical
  exact fun i => if ¬ wasOpened h i ∧ historyReward h < z i then true else false

theorem eligibleMask_eq_true {n : ℕ} (z : Box n → ℝ) (h : History n) (i : Box n) :
    eligibleMask z h i = true ↔ ¬ wasOpened h i ∧ historyReward h < z i := by
  classical
  simp [eligibleMask]

theorem eligibleMask_measurable {n : ℕ} (z : Box n → ℝ) :
    Measurable (eligibleMask z) := by
  classical
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    ((wasOpened_measurable i).compl.inter
      (measurableSet_lt historyReward_measurable measurable_const))
    measurable_const measurable_const

def candidates {n : ℕ} (m : Box n → Bool) : Finset (Box n) :=
  Finset.univ.filter (fun i => m i = true)

def selectBest {n : ℕ} (z : Box n → ℝ) (m : Box n → Bool) : Decision n :=
  if hs : (candidates m).Nonempty then
    some (Classical.choose (Finset.exists_max_image (candidates m) z hs))
  else none

theorem selectBest_some {n : ℕ} (z : Box n → ℝ) (m : Box n → Bool) (i : Box n)
    (hi : selectBest z m = some i) :
    m i = true ∧ ∀ j, m j = true → z j ≤ z i := by
  classical
  by_cases hs : (candidates m).Nonempty
  · have hchoice : Classical.choose (Finset.exists_max_image (candidates m) z hs) = i := by
      simpa only [selectBest, dif_pos hs, Option.some.injEq] using hi
    have hspec := Classical.choose_spec (Finset.exists_max_image (candidates m) z hs)
    rw [hchoice] at hspec
    refine ⟨(Finset.mem_filter.mp hspec.1).2, fun j hj => ?_⟩
    exact hspec.2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  · have hbad : (none : Decision n) = some i := by
      simpa only [selectBest, dif_neg hs] using hi
    cases hbad

theorem selectBest_none {n : ℕ} (z : Box n → ℝ) (m : Box n → Bool)
    (hstop : selectBest z m = none) : ∀ i, m i ≠ true := by
  classical
  intro i hi
  have hs : (candidates m).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hbad : (some (Classical.choose
      (Finset.exists_max_image (candidates m) z hs)) : Decision n) = none := by
    simpa only [selectBest, dif_pos hs] using hstop
  cases hbad

theorem selectBest_measurable {n : ℕ} (z : Box n → ℝ) :
    Measurable (selectBest z) :=
  measurable_of_finite _

theorem exists_policy_for_indices {n : ℕ} (M : Instance n) (multiplier : ℝ)
    (z : Box n → ℝ) (hz : reservationIndices M multiplier z) :
    ∃ π : Policy n, isGittinsPolicy M multiplier π := by
  classical
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Box n)) z
    ⟨0, Finset.mem_univ _⟩
  let π : Policy n := {
    first := fun _ => i₀
    first_measurable := measurable_const
    next := fun p => selectBest z (eligibleMask z p.1)
    next_measurable := (selectBest_measurable z).comp
      ((eligibleMask_measurable z).comp measurable_fst)
    next_unopened := by
      intro h u i hi
      have heligible := (selectBest_some z (eligibleMask z h) i hi).1
      exact ((eligibleMask_eq_true z h i).mp heligible).1
  }
  refine ⟨π, z, hz, ?_, ?_⟩
  · intro u i
    exact hmax i (Finset.mem_univ _)
  · intro h u _
    change match selectBest z (eligibleMask z h) with
      | none => ∀ i, ¬ wasOpened h i → z i ≤ historyReward h
      | some i => historyReward h ≤ z i ∧
        ∀ j, ¬ wasOpened h j → z j ≤ z i
    cases hnext : selectBest z (eligibleMask z h) with
    | none =>
        intro i hunopened
        apply le_of_not_gt
        intro hgreater
        exact selectBest_none z (eligibleMask z h) hnext i
          ((eligibleMask_eq_true z h i).mpr ⟨hunopened, hgreater⟩)
    | some i =>
        obtain ⟨hi, hmaxi⟩ := selectBest_some z (eligibleMask z h) i hnext
        have hincumbent := ((eligibleMask_eq_true z h i).mp hi).2
        refine ⟨hincumbent.le, fun j hj => ?_⟩
        by_cases heligible : historyReward h < z j
        · exact hmaxi j ((eligibleMask_eq_true z h j).mpr ⟨hj, heligible⟩)
        · exact (le_of_not_gt heligible).trans hincumbent.le

end PandoraBO.Private20261023.GittinsExistence

theorem solution {n : ℕ} (M : PandoraBO.Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) :
    ∃ π : PandoraBO.Policy n, PandoraBO.isGittinsPolicy M multiplier π := by
  classical
  have hroots : ∀ i : PandoraBO.Box n, ∃ z : ℝ,
      PandoraBO.reservationRoot M i (multiplier * M.cost i) z := fun i =>
    (PandoraBO.Private20261023.reservation_index_exists_unique M multiplier hpos i).exists
  let z : PandoraBO.Box n → ℝ := fun i => Classical.choose (hroots i)
  have hz : PandoraBO.reservationIndices M multiplier z :=
    fun i => Classical.choose_spec (hroots i)
  exact PandoraBO.Private20261023.GittinsExistence.exists_policy_for_indices M multiplier z hz
