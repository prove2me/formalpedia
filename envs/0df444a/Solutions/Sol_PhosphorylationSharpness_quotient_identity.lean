-- Prove2me | solution 1 for PhosphorylationSharpness.quotient_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:21:37.049032+00:00
-- url     : https://prove2.me/submissions/23e2c15e-b616-43c9-9f88-90b0693a89b9

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution (p q : ℝ[X]) (r : ℝ) :
    (X-C r)*quotient p q r = conversionNumerator p q r := by
  apply mul_divByMonic_eq_iff_isRoot.mpr
  simp [IsRoot, conversionNumerator]
  ring
end PhosphorylationSharpness
