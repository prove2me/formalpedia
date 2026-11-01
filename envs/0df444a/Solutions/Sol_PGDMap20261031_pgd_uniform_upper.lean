-- Prove2me | solution 1 for PGDMap20261031.pgd_uniform_upper
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:05:24.710806+00:00
-- url     : https://prove2.me/submissions/db19829a-fd87-4b59-afcd-0d5e7c31862c

import Mathlib.Tactic
import Theorems.Thm_PGDMap20261031_pgd_prefix_certificate
import Theorems.Thm_PGDMap20261031_pgd_prefix_to_upper
open PGDMap20261031

theorem solution : UniformUpperClaim := by
  exact PGDMap20261031.pgd_prefix_to_upper PGDMap20261031.pgd_prefix_certificate
