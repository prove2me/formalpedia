-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mul_mem_span_1d57a849979c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:46.333832+00:00
-- url     : https://prove2.me/submissions/140e30f5-4003-45fa-9a17-57d6ae66c2fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutNonempty
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_3a0d7bd51278


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {L : SubSystem k x Ω} {s : Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    {z : Poly k N} (hz : z ∈ zeroIdeal L s) {δ : Ω} (hδ : δ ∈ L.sub (singleChart hj)) :
    ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * δ ∈
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hfc, hf⟩ := hf
    obtain ⟨o, ho, he⟩ := hf (singleChart hj) δ hδ
    rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton] at ho
    obtain ⟨b, rfl⟩ := ho
    rw [Submodule.mem_span_singleton]
    refine ⟨b, ?_⟩
    rw [coe_aeval_ratio hj hfc, chartRing_smul_def, div_mul_eq_mul_div, he, chartRing_smul_def,
      zpow_natCast]
    field_simp
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, Subalgebra.coe_add, add_mul]
    exact Submodule.add_mem _ ha hb
  | smul g z _ hz =>
    rw [smul_eq_mul, map_mul, Subalgebra.coe_mul, mul_assoc]
    exact Submodule.smul_mem _ (aeval (ratio (S := k) hj) g) hz
end GroundTheory.Heights₂.Heights.Kleiman
