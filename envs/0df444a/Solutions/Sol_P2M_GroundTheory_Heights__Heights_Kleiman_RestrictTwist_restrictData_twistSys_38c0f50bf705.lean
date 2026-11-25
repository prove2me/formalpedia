-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twistSys_38c0f50bf705
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:41.147852+00:00
-- url     : https://prove2.me/submissions/27c0e9c5-3bc7-4fbe-8b07-ad1ded4e687f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_add_c90e5fd76ad2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_mul_3dd39e0d5705
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_isFrac_46d7eee3b227
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_eq_5dea7de76ecb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_mem_e8907ed686b4

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (c : ℤ) :
    RestrictData (twistSys S x c) hxy (twistSys S y c) (twistRes S x y c) where
  mem I q hq := twistRes_mem hxy hle c I hq
  add I q hq q' hq' := by
    obtain ⟨t, ht⟩ := exists_isFrac hq
    obtain ⟨t', ht'⟩ := exists_isFrac hq'
    have hsum := isFrac_add (fun s hs => eval_ne_zero_of_mem_monos (liftChart hxy I) hs) ht ht'
    rw [twistRes_eq hxy hle I hsum, twistRes_eq hxy hle I ht, twistRes_eq hxy hle I ht']
    simp only [map_add, map_mul]
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I ht.1) (eval_ne_zero_of_mem_monos I ht'.1)]
  smul I q hq f s e hs hf hse := by
    obtain ⟨t, ht⟩ := exists_isFrac hq
    rw [twistRes_eq hxy hle I (isFrac_mul hs hf hse ht), twistRes_eq hxy hle I ht]
    simp only [map_mul, div_mul_div_comm]
  span I := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨q, hq, rfl⟩
      exact twistRes_mem hxy hle c I hq
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
      exact Submodule.subset_span ⟨aeval x f / aeval x s,
        Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩,
        twistRes_eq (t := (f, s, e, e')) hxy hle I ⟨hs, hf, hse, hc, rfl⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
