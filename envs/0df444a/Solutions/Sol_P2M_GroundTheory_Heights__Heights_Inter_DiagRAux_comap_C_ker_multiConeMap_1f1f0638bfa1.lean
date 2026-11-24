-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_comap_C_ker_multiConeMap_1f1f0638bfa1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:20.374136+00:00
-- url     : https://prove2.me/submissions/eb2d3f73-6f39-46c3-b605-b4bcfb309496

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c c' : (Σ k, ι k) → Φ) :
    (RingHom.ker (T.multiConeMap c)).comap (C : ℤ →+* MRing ι) =
      (RingHom.ker (T.multiConeMap c')).comap (C : ℤ →+* MRing ι) := by
  rw [RingHom.comap_ker, RingHom.comap_ker,
    RingHom.ext_int ((T.multiConeMap c).comp C) ((T.multiConeMap c').comp C)]
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
