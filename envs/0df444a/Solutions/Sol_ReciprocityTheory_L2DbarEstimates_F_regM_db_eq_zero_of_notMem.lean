-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.regM_db_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:14.351151+00:00
-- url     : https://prove2.me/submissions/576db41c-de00-4d07-b422-6a821903c334

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} (z : M → V n) (j : Fin n) (φ : M → ℂ) (x : M)
    (hx : x ∉ tsupport φ) : db n z j φ x = 0 := by
  unfold db
  split_ifs with h
  · obtain ⟨hch, hxs⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := hch hxs
    have h0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    have htend : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have := (e.continuousAt_symm (e.map_source hxs)).tendsto
      rwa [e.left_inv hxs] at this
    have h1 : (φ ∘ e.symm) =ᶠ[𝓝 (e x)] (fun _ => (0 : ℂ)) := h0.comp_tendsto htend
    rw [hzx, wdb, h1.fderiv_eq]
    simp
  · rfl
end ReciprocityTheory.L2DbarEstimates.F
