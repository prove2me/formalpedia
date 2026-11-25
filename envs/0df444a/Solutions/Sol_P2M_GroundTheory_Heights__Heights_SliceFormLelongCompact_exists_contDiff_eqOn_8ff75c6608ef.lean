-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_exists_contDiff_eqOn_8ff75c6608ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:00.322093+00:00
-- url     : https://prove2.me/submissions/969f6560-8caa-472e-9b0c-00a3395ca00a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceFormLelongCompact
theorem _root_.solution {Z : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (hZ : IsClosed Z)
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by
  obtain ⟨U, hU, hZU, hfU⟩ := hf
  have hK : IsCompact (Z ∩ tsupport f) := hfc.isCompact.inter_left hZ
  obtain ⟨V, hVo, hKV, hVU, -⟩ := exists_open_between_and_isCompact_closure hK hU
    (Set.inter_subset_left.trans hZU)
  obtain ⟨θ, hθ, -, h0, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, Fin n → ℂ)) (n := ⊤) hVo.isClosed_compl hK.isClosed
    (Set.disjoint_compl_left_iff_subset.2 hKV)
  have hθc : ContDiff ℝ ∞ θ := contMDiff_iff_contDiff.1 hθ
  have hsupp : tsupport θ ⊆ U := by
    refine (closure_mono fun y hy => ?_).trans hVU
    by_contra hyV
    exact hy ((h0 y).1 hyV)
  refine ⟨fun x => θ x * f x, contDiff_iff_contDiffAt.2 fun x => ?_, hfc.mul_left, fun x hx => ?_⟩
  · by_cases hxU : x ∈ U
    · exact hθc.contDiffAt.mul (hfU.contDiffAt (hU.mem_nhds hxU))
    · have hθ0 : θ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hxU (hsupp h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hθ0] with y hy
      simp [hy]
  · show θ x * f x = f x
    by_cases hxf : x ∈ tsupport f
    · rw [(h1 x).1 ⟨hx, hxf⟩, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero]
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
