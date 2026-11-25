-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesStdIndexDet_span_toAddSubgroup_eq_closure_4928e3faf5ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:48.411492+00:00
-- url     : https://prove2.me/submissions/836c55a6-5ed6-4525-9c6c-f6cc1dfe44cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesStdIndexDet

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
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesStdIndexDet
namespace GroundTheory.Heights₂.Heights.KLinesStdIndexDet
theorem _root_.solution (K : Type) [Field K] [NumberField K] (k : ℕ)
    (f : (Fin k → K) →ₗ[K] (Fin k → K)) :
    (Submodule.span (𝓞 K) (Set.range fun j : Fin k => f (Pi.single j 1))).toAddSubgroup =
      AddSubgroup.closure (Set.range fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k =>
        integralBasis K p.1 • f (Pi.single p.2 1)) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  have hs : Submodule.span ℤ (Set.range (RingOfIntegers.basis K)) = ⊤ :=
    (RingOfIntegers.basis K).span_eq
  have h := Submodule.span_smul_of_span_eq_top hs
    (Set.range fun j : Fin k => f (Pi.single j 1))
  have hr : (Set.range (RingOfIntegers.basis K) • Set.range fun j : Fin k => f (Pi.single j 1)) =
      Set.range fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k =>
        integralBasis K p.1 • f (Pi.single p.2 1) := by
    rw [Set.range_smul_range]
    congr 1
    funext p
    rw [integralBasis_apply, algebraMap_smul]
  rw [hr] at h
  rw [h]
  rfl
end GroundTheory.Heights₂.Heights.KLinesStdIndexDet
