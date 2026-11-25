-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_disjoint_nonZeroDivisors_549f4b0b165b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:19.761251+00:00
-- url     : https://prove2.me/submissions/f4934764-6526-4d3e-8d99-6d083b8ff1a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericCycleCorresp
variable {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericCycleCorresp
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) (W : Ideal (MRing ι O)) [W.IsPrime]
    (hW : (C ϖ : MRing ι O) ∉ W) :
    Disjoint (((nonZeroDivisors O).map (C (σ := (Σ k, ι k)) (R := O)) : Submonoid (MRing ι O)) :
      Set (MRing ι O)) W := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ haW
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hϖ
  have hpow : (C ϖ : MRing ι O) ^ k ∈ W := by
    rw [← map_pow, ← hu, map_mul]
    exact W.mul_mem_right _ haW
  exact hW (‹W.IsPrime›.mem_of_pow_mem k hpow)
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericCycleCorresp
