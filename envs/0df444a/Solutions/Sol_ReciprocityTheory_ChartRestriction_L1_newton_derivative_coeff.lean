-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.newton_derivative_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:50:02.732128+00:00
-- url     : https://prove2.me/submissions/d92a7651-347d-44d2-8507-52af702db8a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_exists_poly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (i : ℕ) :
    ‖P.derivative.coeff i‖ ≤ 1 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  rw [Polynomial.derivative_map, Polynomial.coeff_map]
  exact ((Polynomial.derivative Q).coeff i).2
end ReciprocityTheory.ChartRestriction.L1
