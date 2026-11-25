-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_sup_span_eq_96e87095134c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:46.964382+00:00
-- url     : https://prove2.me/submissions/66c63a4b-a6c8-4bef-8505-20f3b33cec3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_sup_span_mul_9bb1c97ab66a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_subsingleton_of_not_le_5e934b8b52e3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
theorem _root_.solution {P W : Ideal (MRing ι)} [P.IsPrime] (hW : W.IsPrime) (hPW : P ≤ W)
    {g h u v : MRing ι} (hu : u ∉ W) (hv : v ∉ W) (hm : u * g - v * h ∈ P) :
    multAt (P ⊔ Ideal.span {g}) W = multAt (P ⊔ Ideal.span {h}) W := by
  have := hW
  have hlen : ∀ {s w : MRing ι}, w ∉ W →
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {w * s}))) =
        Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {s}))) := by
    intro s w hw
    rw [NumbersDVR.length_localizedQuot_sup_span_mul P W s (fun h' => hw (hPW h')),
      Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W
        (fun hle => hw (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))), add_zero]
  have heq : P ⊔ Ideal.span {u * g} = P ⊔ Ideal.span {v * h} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : u * g = (u * g - v * h) + v * h := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hm)
  unfold multAt
  rw [dif_pos hW, dif_pos hW, ← hlen (s := g) hu, heq, hlen hv]
end GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
