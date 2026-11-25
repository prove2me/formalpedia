-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_none_d3bb72b9d852
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:24:58.86042+00:00
-- url     : https://prove2.me/submissions/b4a5db5c-bb14-4216-9e50-76051d7806e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSec_newEmb_injective_b04c3e7a8d69

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSec
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.YPlusSec
theorem _root_.solution (m : (Σ _ : Unit, Fin (D.size + 1)) →₀ ℕ) (j : Fin (D.extSizes none + 1)) :
    Finsupp.mapDomain (newEmb D) m ⟨none, j⟩ = m ⟨(), j⟩ :=
  Finsupp.mapDomain_apply (newEmb_injective D) m ⟨(), j⟩
end GroundTheory.Heights₂.Heights.YPlusSec
