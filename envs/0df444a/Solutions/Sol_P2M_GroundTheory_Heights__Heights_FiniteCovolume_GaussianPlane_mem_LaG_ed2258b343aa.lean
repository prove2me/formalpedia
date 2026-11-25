-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_mem_LaG_ed2258b343aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:23:27.095873+00:00
-- url     : https://prove2.me/submissions/eb455b08-80f3-4089-a303-9df0604e20e5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
theorem _root_.solution {x : Fin 2 → Eg} : x ∈ LaG ↔ ∀ i, x i ∈ integralClosure ℤ Eg := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (mem_integralClosure_iff ℤ Eg).2 (RingOfIntegers.isIntegral_coe (y i))
  · intro hx
    exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
