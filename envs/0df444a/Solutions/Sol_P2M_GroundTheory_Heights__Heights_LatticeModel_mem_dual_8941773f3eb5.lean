-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_8941773f3eb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:44.791964+00:00
-- url     : https://prove2.me/submissions/2109f969-f48d-4fe0-9eb3-51b5640c6a48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_iff_40d47eed4618

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hφ : IsDualBasis L φ) (b : Fin (N + 1)) : φ b ∈ latticeDual L :=
  (mem_dual_iff hφ _).mpr ⟨Pi.single b 1, by simp [Pi.single_apply]⟩
end GroundTheory.Heights₂.Heights.LatticeModel
