-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.phiM_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:39:15.813672+00:00
-- url     : https://prove2.me/submissions/d70cfd20-4122-4dd9-8ab3-13a919b22fa9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero

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
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (x : ℂ_[l]) (hx : x ∈ Rmu l) : ∃ f, phiM l f = x := by
  have : Rmu l ≤ (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).range := by
    refine Subring.closure_le.2 fun ζ hζ => ⟨MonoidAlgebra.single ⟨ζ, hζ⟩ 1, ?_⟩
    simp [phiM]
  exact this hx
end ReciprocityTheory.ChartRestriction.L1
