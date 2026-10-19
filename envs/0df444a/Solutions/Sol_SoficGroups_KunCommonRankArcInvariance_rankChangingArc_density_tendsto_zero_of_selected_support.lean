-- Prove2me | solution 1 for SoficGroups.KunCommonRankArcInvariance.rankChangingArc_density_tendsto_zero_of_selected_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/2395974a-6369-4daa-9a2c-9bc416906f69

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_RankArcCharging_rankChangingArc_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCommonRankArcInvariance
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCommonRankArcInvariance
theorem _root_.solution
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {κ : Type*}
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (j : (n : ℕ) → Finset (V n) → ℤ)
    (w : (n : ℕ) → κ → Equiv.Perm (V n))
    (homitted : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (V n)) \
          SoficGroups.RankArcCharging.selectedRankSupport
            (P n) (b n) (j n)).card : ℝ) /
              Fintype.card (V n)))
      atTop (nhds 0))
    (hcross : ∀ i : κ, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing
          (P n) (w n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∀ i : κ, Tendsto
      (fun n =>
        ((SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset (V n))
          (b n) (w n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
  intro i
  exact SoficGroups.RankArcCharging.rankChangingArc_density_tendsto_zero
    V (fun n => (Finset.univ : Finset (V n)))
    P b j (fun n => w n i)
    (fun n => (Fintype.card (V n) : ℝ))
    (fun n => by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance)
    (hcross i) homitted
end SoficGroups.KunCommonRankArcInvariance
