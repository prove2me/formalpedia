-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_X_sub_mul_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:50.711481+00:00
-- url     : https://prove2.me/submissions/b0b7c89f-afbc-4ee9-bc9d-20fb3759f59e

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {s : Finset ℂ} {z : ℂ} (hz : z ∈ s) :
    (X - C z) * Lagrange.basis s id z = C (Lagrange.nodalWeight s id z) * Lagrange.nodal s id := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hz, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero z) (Lagrange.X_sub_C_dvd_nodal id hz)
end ReciprocityTheory.ChartRestriction.DS
