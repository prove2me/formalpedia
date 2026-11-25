-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lcB_path
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:31.061693+00:00
-- url     : https://prove2.me/submissions/ae5a7b99-9f09-43b9-8e80-fd8207f4bb67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Set
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (z Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 := by
  have h1 := hasDerivAt_exp_smul_const Y ((0 : ℝ) : ℂ)
  have hof : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 (0 : ℝ) := Complex.ofRealCLM.hasDerivAt
  have h2 := HasDerivAt.scomp (h := fun y : ℝ => (y : ℂ)) (0 : ℝ) h1 hof
  have h3 := h2.const_mul z
  exact h3.congr_deriv (by simp)
end ReciprocityTheory.ChartRestriction.DS.S7
