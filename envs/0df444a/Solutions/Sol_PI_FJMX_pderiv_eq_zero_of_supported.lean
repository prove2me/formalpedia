-- Prove2me | solution 1 for PI.FJMX.pderiv_eq_zero_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:43.177674+00:00
-- url     : https://prove2.me/submissions/953aac24-6165-42ec-a13b-fbf7d7497978

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.FJMX
theorem _root_.solution {S : Set σ} {f : MvPolynomial σ R} (hf : f ∈ supported R S)
    {v : σ} (hv : v ∉ S) : pderiv v f = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  exact hv ((mem_supported.1 hf) h)
end PI.FJMX
