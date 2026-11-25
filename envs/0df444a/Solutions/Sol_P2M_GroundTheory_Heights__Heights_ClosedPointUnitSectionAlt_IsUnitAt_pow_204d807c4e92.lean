-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_pow_204d807c4e92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:48.040977+00:00
-- url     : https://prove2.me/submissions/74fd1bf2-13bd-4291-b10d-da1cc6bd3e23

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
theorem _root_.solution {P : HeightOneSpectrum (𝓞 K')} {a : ℕ} {g : K'} (hg : IsUnitAt y P a g) (n : ℕ) :
    IsUnitAt y P (a * n) (g ^ n) := fun u => by
  rw [pow_mul, map_pow]
  exact pow_le_pow_left' (hg u) n
end IsUnitAt
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
