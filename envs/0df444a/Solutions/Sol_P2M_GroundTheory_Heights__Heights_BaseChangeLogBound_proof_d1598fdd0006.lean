-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_proof_d1598fdd0006
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:31.852416+00:00
-- url     : https://prove2.me/submissions/b9396ea8-6f35-4a4f-b8cb-83210f1e170b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PBaseChangeLogBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_map__27b43c6efe6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5


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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace BaseChangeLogBound
theorem _root_.solution (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hC : ConeLogBound.Statement) : BaseChangeLogBound.Statement := by
  intro K _ _ n e δ h I f u σ hI hf hδ hu
  obtain ⟨hprime, c, hc, g, hg, heq⟩ := hB K n (e + 1) I f σ hI hf
  have hδσ : IsMultiHomog δ (MvPolynomial.map σ f) :=
    (isMultiHomog_iff _ _).mpr fun i => IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) σ
  have hne : MvPolynomial.map σ f ≠ 0 := fun h0 =>
    hf.1 (map_injective σ σ.injective (by rw [h0, map_zero]))
  rw [heq] at hδσ hne
  obtain ⟨δW, hδW, hsum⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) _ c g hg hδσ hne
  unfold cycleIntegral
  calc ∑ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support,
        ((fundCycle (I.map (MvPolynomial.map σ))) W : ℝ) * coneIntegral h W e (fsLog h fun j => σ (u j))
      ≤ ∑ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support,
        ((fundCycle (I.map (MvPolynomial.map σ))) W : ℝ) * (δW W * Real.log (h.norm fun j => σ (u j))) :=
        Finset.sum_le_sum fun W hW => mul_le_mul_of_nonneg_left
          (hC n e (δW W) h W (g W) _ (hprime W hW) (hg W hW) (hδW W hW) (hAv K n I u σ hI hu W hW))
          (Nat.cast_nonneg _)
    _ = δ * Real.log (h.norm fun j => σ (u j)) := by
        rw [← hsum]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun W _ => ?_
        ring
end BaseChangeLogBound
end GroundTheory.Heights₂.Heights
