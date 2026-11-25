-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_65efbe4a3982
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:44:00.652095+00:00
-- url     : https://prove2.me/submissions/c965a3fa-5c5b-410d-96dd-d684c85f71dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_union_split_d0b5eb59111d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I K : Chart x) (b : Ω)
    (hb : b ∈ chartRing S x (chartUnion I K)) :
    ∃ u ∈ monos (S := S) I.1, ∃ d : ℕ, u.IsHomogeneous d ∧ aeval x u * b ∈ twistMod S x (d : ℤ) K := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hb
  obtain ⟨u, hu, v, hv, rfl⟩ := monos_union_split hs
  obtain ⟨du, hdu⟩ := monos_isHomogeneous hu
  obtain ⟨dv, hdv⟩ := monos_isHomogeneous hv
  have huv0 := eval_ne_zero_of_mem_monos (chartUnion I K) hs
  have hu0 := eval_ne_zero_of_mem_monos I hu
  have hv0 := eval_ne_zero_of_mem_monos K hv
  have he : du + dv = e := (hdu.mul hdv).inj_right hse (fun h => huv0 (by rw [h, map_zero]))
  refine ⟨u, hu, du, hdu, Submodule.subset_span ⟨f, v, dv, e, hv, hf, hdv, by omega, ?_⟩⟩
  rw [map_mul]
  field_simp
end GroundTheory.Heights₂.Heights.Kleiman
