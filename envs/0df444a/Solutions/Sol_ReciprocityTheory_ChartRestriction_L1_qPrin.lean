-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.qPrin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:37.462417+00:00
-- url     : https://prove2.me/submissions/4b5e8814-1e25-49e3-b57e-45c901211499

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_integral_poly_of_qExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R (qExpansion 1 f)) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by
  obtain ⟨P, h1, h2, h3, -⟩ := exists_integral_poly_of_qExpansion R N f hf hR
  exact ⟨P, h1, h2, h3⟩
end ReciprocityTheory.ChartRestriction.L1
