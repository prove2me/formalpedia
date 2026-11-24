-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.IsMF.ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:16.584903+00:00
-- url     : https://prove2.me/submissions/c0ccd684-ccaa-4477-b745-ec6412ef43f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_hasSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_hasSum


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
namespace IsMF
theorem _root_.solution {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) : ev (qExpansion 1 f) (qm 1 τ) = f τ := by
  exact (hf.hasSum τ).tsum_eq
end IsMF
end ReciprocityTheory.ChartRestriction.L1
