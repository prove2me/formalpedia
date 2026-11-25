-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mem_chartIdeal_of_dehom_eq_zero_3eb777d45518
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:57.520131+00:00
-- url     : https://prove2.me/submissions/d4c0a598-5a95-48c3-9a6d-97a694a4c074

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_exists_homog_congr_b695ff76f041
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_eq_zero_iff_7938877721c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_mul_of_isMultiHomog_db1b22d71340
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_chartUnitIdeal_e888f0795333

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
theorem _root_.solution {f : MRing ι F} (hf : dehom V i f = 0) :
    f ∈ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i := by
  obtain ⟨N, hN⟩ := exists_homog_congr i f
  obtain ⟨h, hh, hc⟩ := hN N le_rfl
  have hfh : f - h ∈ chartUnitIdeal i := Ideal.Quotient.eq.mp hc
  have h0 : dehom V i h = 0 := by
    have := dehom_chartUnitIdeal i hi hfh
    rwa [map_sub, hf, zero_sub, neg_eq_zero] at this
  have hV : h ∈ V := by
    rw [← cls_eq_zero_iff, ← dehom_mul_of_isMultiHomog i hi hh, h0, zero_mul]
  have : f = (f - h) + h := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hV)
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
