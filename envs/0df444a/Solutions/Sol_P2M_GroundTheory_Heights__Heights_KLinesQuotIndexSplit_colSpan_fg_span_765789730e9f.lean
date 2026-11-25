-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesQuotIndexSplit_colSpan_fg_span_765789730e9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:16.819838+00:00
-- url     : https://prove2.me/submissions/906683be-1e9e-4866-93b9-a0c69ecf4766

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndexSplit

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
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesQuotIndexSplit
namespace GroundTheory.Heights₂.Heights.KLinesQuotIndexSplit
theorem _root_.solution (K : Type) [Field K] [NumberField K] (k : ℕ)
    (V : Matrix (Fin k) (Fin k) K) (hV : V.det ≠ 0) :
    ((Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).restrictScalars
        ℤ).FG ∧
      Submodule.span K ((Submodule.span (𝓞 K)
          (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K)) : Submodule (𝓞 K) (Fin k → K)) :
            Set (Fin k → K)) = ⊤ := by
  refine ⟨(Submodule.fg_span (Set.finite_range _)).restrictScalars, ?_⟩
  rw [Submodule.span_span_of_tower]
  have hr : (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K)) =
      (Matrix.mulVecLin V) '' Set.range (Pi.basisFun K (Fin k)) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    simp [Pi.basisFun_apply]
  have hs : Function.Surjective (Matrix.mulVecLin V) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det V).mpr hV.isUnit)
  rw [hr, Submodule.span_image, (Pi.basisFun K (Fin k)).span_eq, Submodule.map_top,
    LinearMap.range_eq_top.mpr hs]
end GroundTheory.Heights₂.Heights.KLinesQuotIndexSplit
