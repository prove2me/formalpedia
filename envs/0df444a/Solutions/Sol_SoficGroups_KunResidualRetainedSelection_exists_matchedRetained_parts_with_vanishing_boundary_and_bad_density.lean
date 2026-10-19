-- Prove2me | solution 1 for SoficGroups.KunResidualRetainedSelection.exists_matchedRetained_parts_with_vanishing_boundary_and_bad_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/fb42faba-2ac1-4e3f-98be-4825dbf6840d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetained_bad_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunResidualRetainedSelection_exists_matchedRetained_part_boundary_and_bad_density_le
import Theorems.Thm_SoficGroups_KunResidualRetainedSelection_matchedRetained_boundary_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.KunResidualRetainedSelection
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (hdiscard : Tendsto
      (fun n => (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (B : ∀ n, Finset (V n))
    (hbad : Tendsto
      (fun n => (((U n ∩ B n).card : ℝ) / (U n).card))
      atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0)) :
    ∃ C : ∀ n, Finset (V n),
      (∀ n, C n ∈ R n) ∧
        Tendsto
          (fun n => (SoficGroups.boundary (σ n) (C n) : ℝ) / (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n => (((C n ∩ B n).card : ℝ) / (C n).card))
          atTop (𝓝 0) := by
  have hretboundary := matchedRetained_boundary_density_tendsto_zero
    σ U hU P R hR hRne hdiscard hboundary
  have hretbad := SoficGroups.matchedRetained_bad_density_tendsto_zero
    U hU P R hR hRne hdiscard B hbad
  have hcombined : Tendsto
      (fun n =>
        ((∑ D ∈ R n, (SoficGroups.boundary (σ n) D : ℝ)) +
          ((SoficGroups.matchedRetainedSupport (R n) ∩ B n).card : ℝ)) /
            (SoficGroups.matchedRetainedSupport (R n)).card)
      atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hretboundary.add hretbad
  have hchoose (n : ℕ) :=
    exists_matchedRetained_part_boundary_and_bad_density_le
      (σ n) (P n) (R n) (hR n) (hRne n) (B n)
  let C : ∀ n, Finset (V n) := fun n => (hchoose n).choose
  have hC (n : ℕ) : C n ∈ R n := (hchoose n).choose_spec.1
  have hCb (n : ℕ) :
      (SoficGroups.boundary (σ n) (C n) : ℝ) / (C n).card ≤
        ((∑ D ∈ R n, (SoficGroups.boundary (σ n) D : ℝ)) +
          ((SoficGroups.matchedRetainedSupport (R n) ∩ B n).card : ℝ)) /
            (SoficGroups.matchedRetainedSupport (R n)).card :=
    (hchoose n).choose_spec.2.1
  have hCe (n : ℕ) :
      ((C n ∩ B n).card : ℝ) / (C n).card ≤
        ((∑ D ∈ R n, (SoficGroups.boundary (σ n) D : ℝ)) +
          ((SoficGroups.matchedRetainedSupport (R n) ∩ B n).card : ℝ)) /
            (SoficGroups.matchedRetainedSupport (R n)).card :=
    (hchoose n).choose_spec.2.2
  exact ⟨C, hC,
    squeeze_zero (fun n => by positivity) hCb hcombined,
    squeeze_zero (fun n => by positivity) hCe hcombined⟩
end SoficGroups.KunResidualRetainedSelection
