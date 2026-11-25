-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_lineCoeffs_inv_smul_46e4714a8745
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:09.013079+00:00
-- url     : https://prove2.me/submissions/99a8a386-9200-4c82-91f6-4f6fea447c16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdaptedReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_scalar_smul_5c8918aaa95a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8

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
theorem _root_.solution (g : h.unitaryGroup) (La : AddSubgroup W) (x : W) :
    lineCoeffs (E := E) (g⁻¹ • La) x = lineCoeffs (E := E) La (g • x) := by
  ext a
  change a • x ∈ g⁻¹ • La ↔ a • (g • x) ∈ La
  rw [mem_inv_smul_iff, unitary_smul_scalar_smul]
end GroundTheory.Heights₂.Heights.FiniteCovolume
