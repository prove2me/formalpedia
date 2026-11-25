-- Prove2me | solution 1 for OptimalAffinity.stationaryY_positive_near_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:05:47.749309+00:00
-- url     : https://prove2.me/submissions/f79eeedb-66e6-4c00-9a1f-23e586c0a880

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
public import Theorems.Thm_OptimalAffinity_stationaryY_one
public import Theorems.Thm_OptimalAffinity_stationaryY_continuous

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution :
    ∀ᶠ x : ℝ in nhds 1, 0 < stationaryY x := by
  have h := (stationaryY_continuous.continuousAt).eventually
    (isOpen_Ioi.mem_nhds (by rw [stationaryY_one]; norm_num :
      stationaryY 1 ∈ Set.Ioi (0 : ℝ)))
  exact h
end OptimalAffinity
