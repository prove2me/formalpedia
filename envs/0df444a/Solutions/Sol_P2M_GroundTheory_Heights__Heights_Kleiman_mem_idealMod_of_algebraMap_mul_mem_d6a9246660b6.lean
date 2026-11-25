-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_idealMod_of_algebraMap_mul_mem_d6a9246660b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:51.631938+00:00
-- url     : https://prove2.me/submissions/c9b7fa2d-348b-4c05-be65-af7bca702d1d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_div_of_mem_idealMod_28db016029d7

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
theorem _root_.solution {qq : Ideal (Poly S N)} (hq : qq.IsPrime)
    (hle : ∀ (p : Poly S N) (d : ℕ), p.IsHomogeneous d → aeval x p = 0 → p ∈ qq) (I : Chart x) {s : S}
    (hs : (C s : Poly S N) ∉ qq) {a : Ω} (ha : a ∈ chartRing S x I)
    (hsa : algebraMap S Ω s * a ∈ idealMod qq I) : a ∈ idealMod qq I := by
  obtain ⟨g, n, d, hn, hg, hnd, rfl⟩ := ha
  obtain ⟨f, m, e, hf, hm, hfe, hme, hfm⟩ := exists_eq_div_of_mem_idealMod hsa
  have hn0 := eval_ne_zero_of_mem_monos I hn
  have hm0 := eval_ne_zero_of_mem_monos I hm

  have h1 : (C s * (g * m)).IsHomogeneous (d + e) := by
    simpa using (isHomogeneous_C (Fin (N + 1)) s).mul (hg.mul hme)
  have h2 : (f * n).IsHomogeneous (d + e) := by
    have h := hfe.mul hnd
    rwa [add_comm e d] at h
  have hker : C s * (g * m) - f * n ∈ qq := by
    refine hle _ (d + e) (by rw [sub_eq_add_neg]; exact h1.add h2.neg) ?_
    rw [mul_div_assoc', div_eq_div_iff hn0 hm0] at hfm
    simp only [map_sub, map_mul, aeval_C]
    linear_combination hfm
  have h3 : C s * (g * m) ∈ qq := by
    have h4 : C s * (g * m) = (C s * (g * m) - f * n) + f * n := by ring
    rw [h4]
    exact qq.add_mem hker (qq.mul_mem_right n hf)
  have hgm : g * m ∈ qq := (hq.mem_or_mem h3).resolve_left hs
  exact Submodule.subset_span ⟨g * m, n * m, d + e, hgm, mul_mem hn hm, hg.mul hme, hnd.mul hme, by
    rw [map_mul, map_mul, mul_div_mul_right _ _ hm0]⟩
end GroundTheory.Heights₂.Heights.Kleiman
