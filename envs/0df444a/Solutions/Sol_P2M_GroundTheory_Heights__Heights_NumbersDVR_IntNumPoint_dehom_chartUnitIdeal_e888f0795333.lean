-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_chartUnitIdeal_e888f0795333
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.805149+00:00
-- url     : https://prove2.me/submissions/95215f4e-810e-444f-9c28-d1bd448fbb44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_xc_ne_zero_ee20e72cfa3f

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
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
variable (V : Ideal (MRing ι F)) [V.IsPrime]
variable {V}
variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
theorem _root_.solution {f : MRing ι F} (hf : f ∈ chartUnitIdeal i) : dehom V i f = 0 := by
  have : chartUnitIdeal (F := F) i ≤ RingHom.ker (dehom V i) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, dehom, aeval_X]
    rw [div_self (xc_ne_zero (hi k)), sub_self]
  exact this hf
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
