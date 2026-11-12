-- Prove2me | solution 1 for PGDMap20261031.entropy_unique_optimum
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:05:43.907316+00:00
-- url     : https://prove2.me/submissions/0f4e6321-6140-48ee-97b3-eaee39053c67

import Mathlib.Tactic
import Theorems.Thm_PGDMap20261031_entropy_located_existence
import Theorems.Thm_PGDMap20261031_entropy_necessary_alternation
import Theorems.Thm_PGDMap20261031_entropy_alternation_certificate
open PGDMap20261031

theorem solution : UniqueLocatedOptimumClaim := by
  intro M
  obtain ⟨z, hopt, hbounds⟩ := PGDMap20261031.entropy_located_existence M
  obtain ⟨hbound, halt⟩ := PGDMap20261031.entropy_necessary_alternation M z hopt
  have cert := PGDMap20261031.entropy_alternation_certificate
    M z.1 z.2 (contraction M z.1 z.2) hopt.1 hbounds.2.2.2.2.2.1 hbound halt
  have hunique : ∀ u, IsGeometryOptimum M u → u = z := by
    intro u hu
    exact cert.2.2 u hu
  refine ⟨⟨z, hopt, hunique⟩, ?_⟩
  intro u hu
  rw [hunique u hu]
  exact hbounds
