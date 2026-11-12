-- Prove2me | solution 1 for PGDMap20261031.joint_bregman_optimum
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:05:49.424485+00:00
-- url     : https://prove2.me/submissions/461b32e3-c423-4c85-be09-9c601238684d

import Mathlib.Tactic
import Theorems.Thm_PGDMap20261031_entropy_exact_performance
import Theorems.Thm_PGDMap20261031_entropy_unique_optimum
import Theorems.Thm_PGDMap20261031_entropy_necessary_alternation
import Theorems.Thm_PGDMap20261031_entropy_alternation_certificate
import Theorems.Thm_PGDMap20261031_entropy_common_horizon
import Theorems.Thm_PGDMap20261031_entropy_single_profile
import Theorems.Thm_PGDMap20261031_entropy_pure_geometry_gap
open PGDMap20261031

theorem solution : FullMapTheorem := by
  exact ⟨PGDMap20261031.entropy_exact_performance,
    PGDMap20261031.entropy_unique_optimum,
    PGDMap20261031.entropy_necessary_alternation,
    PGDMap20261031.entropy_alternation_certificate,
    PGDMap20261031.entropy_common_horizon,
    PGDMap20261031.entropy_single_profile,
    PGDMap20261031.entropy_pure_geometry_gap⟩
