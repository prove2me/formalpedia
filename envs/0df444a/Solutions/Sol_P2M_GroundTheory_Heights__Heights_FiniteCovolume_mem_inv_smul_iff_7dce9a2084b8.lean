-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:22.662117+00:00
-- url     : https://prove2.me/submissions/9b3cf31d-aed4-405e-a5c3-c84186c003a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdaptedReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {g : h.unitaryGroup} {La : AddSubgroup W} {x : W} :
    x ∈ g⁻¹ • La ↔ g • x ∈ La := by
  change x ∈ ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) • La ↔ _
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
