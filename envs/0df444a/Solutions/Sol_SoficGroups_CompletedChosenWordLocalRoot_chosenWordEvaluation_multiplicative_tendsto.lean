-- Prove2me | solution 1 for SoficGroups.CompletedChosenWordLocalRoot.chosenWordEvaluation_multiplicative_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/05cc7fb5-802b-4bb0-a043-43f692cd5c7c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_comm
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_normalizedHamming_mul_le
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenWordEvaluation_tendsto_action
import Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_normalizedHamming_mul_le
import Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_chosenWordEvaluation_tendsto_action

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators
namespace SoficGroups.CompletedChosenWordLocalRoot
theorem _root_.solution
    {G ι : Type*} [Group G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (p : ∀ n, G → Equiv.Perm (V n))
    (hone : ∀ n, p n 1 = 1)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (p n (a * g)) (p n a * p n g))
        atTop (nhds 0))
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g : G, ((w g).map s).prod = g)
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hletter : ∀ i : ι,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (σ n i) (p n (s i)))
        atTop (nhds 0))
    (a g : G) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        (chosenWordEvaluation (σ n) w (a * g))
        (chosenWordEvaluation (σ n) w a *
          chosenWordEvaluation (σ n) w g))
      atTop (nhds 0) := by
  let φ : ∀ n, G → Equiv.Perm (V n) :=
    fun n k => chosenWordEvaluation (σ n) w k
  have hφ (k : G) : Tendsto
      (fun n => SoficGroups.normalizedHamming (φ n k) (p n k))
      atTop (nhds 0) :=
    chosenWordEvaluation_tendsto_action
      V p hone hmul s w hw σ hletter k
  have hpa : Tendsto
      (fun n => SoficGroups.normalizedHamming (p n a) (φ n a))
      atTop (nhds 0) := by
    have heq :
        (fun n => SoficGroups.normalizedHamming (p n a) (φ n a)) =
        (fun n => SoficGroups.normalizedHamming (φ n a) (p n a)) := by
      funext n
      exact SoficGroups.normalizedHamming_comm _ _
    rw [heq]
    exact hφ a
  have hpg : Tendsto
      (fun n => SoficGroups.normalizedHamming (p n g) (φ n g))
      atTop (nhds 0) := by
    have heq :
        (fun n => SoficGroups.normalizedHamming (p n g) (φ n g)) =
        (fun n => SoficGroups.normalizedHamming (φ n g) (p n g)) := by
      funext n
      exact SoficGroups.normalizedHamming_comm _ _
    rw [heq]
    exact hφ g
  have hupper : Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (φ n (a * g)) (p n (a * g)) +
        (SoficGroups.normalizedHamming
          (p n (a * g)) (p n a * p n g) +
        (SoficGroups.normalizedHamming (p n a) (φ n a) +
          SoficGroups.normalizedHamming (p n g) (φ n g))))
      atTop (nhds 0) := by
    simpa using (hφ (a * g)).add
      ((hmul a g).add (hpa.add hpg))
  change Tendsto
    (fun n => SoficGroups.normalizedHamming
      (φ n (a * g)) (φ n a * φ n g)) atTop (nhds 0)
  refine squeeze_zero
    (fun n => SoficGroups.normalizedHamming_nonneg _ _) ?_ hupper
  intro n
  calc
    SoficGroups.normalizedHamming
        (φ n (a * g)) (φ n a * φ n g) ≤
      SoficGroups.normalizedHamming
        (φ n (a * g)) (p n (a * g)) +
      SoficGroups.normalizedHamming
        (p n (a * g)) (φ n a * φ n g) :=
      SoficGroups.normalizedHamming_triangle _ _ _
    _ ≤ SoficGroups.normalizedHamming
        (φ n (a * g)) (p n (a * g)) +
      (SoficGroups.normalizedHamming
        (p n (a * g)) (p n a * p n g) +
        SoficGroups.normalizedHamming
          (p n a * p n g) (φ n a * φ n g)) := by
      gcongr
      exact SoficGroups.normalizedHamming_triangle _ _ _
    _ ≤ SoficGroups.normalizedHamming
        (φ n (a * g)) (p n (a * g)) +
      (SoficGroups.normalizedHamming
        (p n (a * g)) (p n a * p n g) +
        (SoficGroups.normalizedHamming (p n a) (φ n a) +
          SoficGroups.normalizedHamming (p n g) (φ n g))) := by
      gcongr
      exact normalizedHamming_mul_le
        (p n a) (φ n a) (p n g) (φ n g)
end SoficGroups.CompletedChosenWordLocalRoot
