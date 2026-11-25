-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_target_0b55a0c19207
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:28.99715+00:00
-- url     : https://prove2.me/submissions/bb3bae98-6683-444b-80c0-bb70ab40585a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
theorem _root_.solution (A : FinHolAtlas e X) (k : Fin A.n) {F : (Fin e → ℂ) → ℝ}
    (hF : ContinuousOn F (A.chart k).target) {S : Set X} (hS : IsCompact S)
    (hSk : S ⊆ (A.chart k).source)
    (hz : ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ S → F y = 0) :
    IntegrableOn F (A.chart k).target := by
  have hC : IsCompact ((A.chart k) '' S) :=
    hS.image_of_continuousOn ((A.chart k).continuousOn.mono hSk)
  have hCt : (A.chart k) '' S ⊆ (A.chart k).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart k).map_source (hSk hx)
  refine ((hF.mono hCt).integrableOn_compact hC).of_forall_sdiff_eq_zero
    (A.chart k).open_target.measurableSet ?_
  rintro y ⟨hy, hyC⟩
  exact hz y hy fun h => hyC ⟨_, h, (A.chart k).right_inv hy⟩
end GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
