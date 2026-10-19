-- Prove2me | solution 1 for SoficGroups.CompletedSourceFinalGeneratorTransfer.twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/fd68fbfa-916c-46c1-a3ef-c4d4e5560661

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompletedSourceChosenWordRestrictionTransfer_completedGenerator_normalizedHamming_tendsto_zero
import Theorems.Thm_SoficGroups_CompletedSourceFinalGeneratorTransfer_deleted_density_relative_survivors

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer
namespace SoficGroups.CompletedSourceFinalGeneratorTransfer
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*}
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (s : ι → J)
    (P : (n : ℕ) → Finset (V n))
    (D : (n : ℕ) → Finset {x : V n // x ∈ P n})
    (τ : (n : ℕ) → (i : ι) →
      Equiv.Perm
        {x : {x : V n // x ∈ P n} //
          x ∈ (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n})})
    (hsource : ∀ n i, σ n i = p n (s i))
    (hagrees : ∀ n i,
      ∀ x : {x : {x : V n // x ∈ P n} //
        x ∈ (Finset.univ \ D n :
          Finset {x : V n // x ∈ P n})},
        completedRestriction (σ n i) (P n) x.val ∈
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n}) →
        (τ n i x).val =
          completedRestriction (σ n i) (P n) x.val)
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : V n // x ∈ P n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (P n).card)
      atTop (nhds 0)) :
    ∀ i : ι,
      Tendsto
        (fun n =>
          SoficGroups.normalizedHamming
            (τ n i)
            (completedRestriction
              (completedRestriction (p n (s i)) (P n))
              (Finset.univ \ D n)))
        atTop (nhds 0) := by
  intro i
  have hdeletedbase : Tendsto
      (fun n =>
        ((D n).card : ℝ) /
          Fintype.card {x : V n // x ∈ P n})
      atTop (nhds 0) := by
    simpa only [Fintype.card_coe] using hdeleted
  have hsurvivors :=
    deleted_density_relative_survivors
      (fun n => {x : V n // x ∈ P n}) D hZ hdeletedbase
  have hdeletedfinal : Tendsto
      (fun n =>
        (((Finset.univ \
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n})).card : ℝ) /
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n}).card))
      atTop (nhds 0) := by
    convert hsurvivors using 1
    funext n
    have hset :
        (Finset.univ \
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n})) = D n := by
      ext x
      simp
    rw [hset]
  have hletter :=
    completedGenerator_normalizedHamming_tendsto_zero
      (fun n => {x : V n // x ∈ P n})
      (fun n => completedRestriction (σ n i) (P n))
      (fun n => (Finset.univ \ D n :
        Finset {x : V n // x ∈ P n}))
      (fun n => τ n i)
      (fun n => hagrees n i)
      hdeletedfinal
  convert hletter using 1
  funext n
  rw [hsource n i]
end SoficGroups.CompletedSourceFinalGeneratorTransfer
