-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_le_of_mem_add946ce0df5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:42.856858+00:00
-- url     : https://prove2.me/submissions/11095a2a-175d-4405-b4d2-a3b1fe6bf686

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integer_of_mem_chartRingZ_a503b6b08454


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
theorem _root_.solution {P : HeightOneSpectrum (𝓞 K')} {t : T} (ht0 : y ⟨(), t⟩ ≠ 0)
    (ht : ∀ u, P.valuation K' (y ⟨(), u⟩) ≤ P.valuation K' (y ⟨(), t⟩)) {d : ℕ} {g : K'}
    (hg : g ∈ chartLat y 1 d) : P.valuation K' g ≤ P.valuation K' (y ⟨(), t⟩) ^ d := by
  have h1 := CurveAffineCharts.mem_integer_of_mem_chartRingZ y P t ht ((mem_chartLat_iff y).mp hg t ht0)
  rw [Valuation.mem_integer_iff, map_div₀, map_pow] at h1
  have hpos : P.valuation K' (y ⟨(), t⟩) ^ d ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr ht0)
  exact (div_le_one₀ (zero_lt_iff.mpr hpos)).mp h1
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
