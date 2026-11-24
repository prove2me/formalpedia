-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_C_comp_c5112b1b05c1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:55.332105+00:00
-- url     : https://prove2.me/submissions/93f25c03-ca57-4f78-9df5-1bc3028dad05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall

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
open GroundTheory.Heights₂.Heights.YPlusSmall
namespace GroundTheory.Heights₂.Heights.YPlusSmall
theorem _root_.solution {σ : Type*} {Ω : Type*} [Field Ω] {ι : Type*} (v : σ → Ω) (F : MvPolynomial σ ℤ) :
    aeval (fun p ↦ (C (v p) : MvPolynomial ι Ω)) F = C (aeval v F) := by
  have := congrArg (fun φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial ι Ω ↦ φ F)
    (MvPolynomial.comp_aeval (R := ℤ) (f := v) (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial ι Ω)))
  simpa [MvPolynomial.algebraMap_eq] using this.symm
end GroundTheory.Heights₂.Heights.YPlusSmall
