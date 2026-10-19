-- Prove2me | solution 1 for SoficGroups.KunGuardedCanonicalMatchedDensity.canonical_matched_density_of_guarded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/8663a179-af37-47ac-9ad2-9c21f3168e9a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunGuardedCanonicalMatchedDensity_matchedRadiusBad_mono_bad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunGuardedCanonicalMatchedDensity
open Filter Topology
namespace SoficGroups.KunGuardedCanonicalMatchedDensity
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (U : (n : ℕ) → Finset (V n))
    (P : (n : ℕ) → Finpartition (U n))
    {ι : Type*} (I : ℕ → Finset ι)
    (w : (n : ℕ) → ι → Equiv.Perm (V n))
    (B E C : (n : ℕ) → Finset (V n))
    (hguarded : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (P n) (I n) (w n) (B n ∪ E n)).card : ℝ) /
            (C n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (P n) (I n) (w n) (B n)).card : ℝ) /
            (C n).card))
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => by positivity) ?_ hguarded
  intro n
  have hsubset :
      C n ∩ SoficGroups.matchedRadiusBad
          (P n) (I n) (w n) (B n) ⊆
        C n ∩ SoficGroups.matchedRadiusBad
          (P n) (I n) (w n) (B n ∪ E n) := by
    intro x hx
    obtain ⟨hxC, hxB⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr
      ⟨hxC, matchedRadiusBad_mono_bad
        (P n) (I n) (w n)
        (Finset.subset_union_left : B n ⊆ B n ∪ E n) hxB⟩
  have hcard :
      ((C n ∩ SoficGroups.matchedRadiusBad
        (P n) (I n) (w n) (B n)).card : ℝ) ≤
        (C n ∩ SoficGroups.matchedRadiusBad
          (P n) (I n) (w n) (B n ∪ E n)).card := by
    exact_mod_cast Finset.card_le_card hsubset
  exact div_le_div_of_nonneg_right hcard (by positivity)
end SoficGroups.KunGuardedCanonicalMatchedDensity
