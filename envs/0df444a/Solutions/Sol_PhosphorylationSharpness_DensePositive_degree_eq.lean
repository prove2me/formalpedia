-- Prove2me | solution 1 for PhosphorylationSharpness.DensePositive.degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:21:26.650765+00:00
-- url     : https://prove2.me/submissions/7ad6d857-e774-42a7-be28-591ef3211f19

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
namespace DensePositive
theorem _root_.solution {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) :
    p.natDegree = m :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr hp.2)
    (ne_of_gt (hp.1 m le_rfl))
end DensePositive
end PhosphorylationSharpness
