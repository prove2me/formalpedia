-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_segre_apply_0b8426073082
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:53.519938+00:00
-- url     : https://prove2.me/submissions/aef9d22d-a58c-43ea-8550-73cb640e2e46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegPos

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualGeometricDegreePositive
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualGeometricDegreePositive
theorem _root_.solution (z : (Σ _ : Unit, T) → ℂ) (s : (k : Unit) → dualBlocks T k) :
    segre (ι := dualBlocks T) z s = z ⟨(), s ()⟩ := by
  simp [segre]
end GroundTheory.Heights₂.Heights.DualGeometricDegreePositive
