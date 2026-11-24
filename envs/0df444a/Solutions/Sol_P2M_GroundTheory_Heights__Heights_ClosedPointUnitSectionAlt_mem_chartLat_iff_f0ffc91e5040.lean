-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:50.700176+00:00
-- url     : https://prove2.me/submissions/c7dfd84a-cc9d-4526-b1d5-dff9a21b9cad

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
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution {d : ℕ} {g : K'} :
    g ∈ chartLat y 1 d ↔
      ∀ t : T, y ⟨(), t⟩ ≠ 0 → g / y ⟨(), t⟩ ^ d ∈ chartRingZ y (fun _ => t) := by
  have key : ∀ c : Unit → T, c = fun _ => c () := fun c => funext fun u => by cases u; rfl
  show (∀ c : Unit → T, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      g * ∏ k, y ⟨k, c k⟩ ^ (-((d : ℤ) * (1 : Unit → ℤ) k)) ∈ chartRingZ y c) ↔ _
  constructor
  · intro h t ht
    have := h (fun _ => t) (fun _ => ht)
    simpa [div_eq_mul_inv, zpow_neg, zpow_natCast] using this
  · intro h c hc
    have := h (c ()) (hc ())
    rw [key c]
    simpa [div_eq_mul_inv, zpow_neg, zpow_natCast] using this
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
