-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_aeval_of_hom_cce1d9985939
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:11.261129+00:00
-- url     : https://prove2.me/submissions/3471ebaf-a58e-4e97-9383-04a8372cc303

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading

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
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {Ω : Type} [Field Ω] (φ : MvPolynomial (Coord n) ℤ →+* Ω)
    (f : MvPolynomial (Coord n) ℤ) : aeval (fun v ↦ φ (X v)) f = φ f := by
  have h : (aeval (fun v ↦ φ (X v)) : _ →ₐ[ℤ] Ω).toRingHom = φ :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ by simp)
  exact congrArg (fun ψ : _ →+* _ ↦ ψ f) h
end GroundTheory.Heights₂.Heights
