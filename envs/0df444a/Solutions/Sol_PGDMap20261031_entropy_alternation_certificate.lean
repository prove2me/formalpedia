-- Prove2me | solution 1 for PGDMap20261031.entropy_alternation_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:05:38.403598+00:00
-- url     : https://prove2.me/submissions/326c2193-4d9a-4adf-abb5-587aa6f546ee

import Mathlib.Tactic
import Theorems.Thm_PGDMap20261031_power_single_crossing
import Theorems.Thm_PGDMap20261031_entropy_alternation_reduction
open PGDMap20261031

theorem solution : AlternationCertificateClaim := by
  exact PGDMap20261031.entropy_alternation_reduction PGDMap20261031.power_single_crossing
