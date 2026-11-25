-- Prove2me | solution 1 for OptimalAffinity.oa2x2_polynomialCertificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:56:57.818501+00:00
-- url     : https://prove2.me/submissions/c83c42ca-750f-43c3-8734-bf4e5d804cad

module
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution (x y : ℝ) :
    12 * (3 * x - 2 * y - 7 * y ^ 2 + 6 * x ^ 2 * y) =
      (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) +
      (3 * x - 2 * y - 1) *
        (4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12) := by
  ring
end OptimalAffinity
