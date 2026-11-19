-- Prove2me | solution 1 for TightCoreset2027.Euclidean.discrete_projections_discrepancy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:00:19.125434+00:00
-- url     : https://prove2.me/submissions/dac92f5d-4651-4774-b5ef-f54c888b173d

import Theorems.Thm_TightCoreset2027_Euclidean_binary_code_exists
import Theorems.Thm_TightCoreset2027_Euclidean_projection_family_of_binary_code
set_option autoImplicit false
open TightCoreset2027.Euclidean
 theorem solution (L q : ℕ) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hcode : q + Nat.choose q 3 < 2 ^ L) :
    ∃ G : ProjectionFamily L q, ProjectionSpecification G := by
  obtain ⟨S, hS, hfour⟩ := binary_code_exists L q hcode
  exact projection_family_of_binary_code L q hL hq S hS hfour
