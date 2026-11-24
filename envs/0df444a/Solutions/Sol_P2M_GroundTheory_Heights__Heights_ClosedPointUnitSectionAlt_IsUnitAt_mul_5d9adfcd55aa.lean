-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_mul_5d9adfcd55aa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:42.291056+00:00
-- url     : https://prove2.me/submissions/55be2e68-beaf-4928-9e04-a8a9673cc090

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection

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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
namespace IsUnitAt
theorem _root_.solution {P : HeightOneSpectrum (𝓞 K')} {a b : ℕ} {g h : K'} (hg : IsUnitAt y P a g)
    (hh : IsUnitAt y P b h) : IsUnitAt y P (a + b) (g * h) := fun u => by
  rw [pow_add, map_mul]
  exact mul_le_mul' (hg u) (hh u)
end IsUnitAt
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
