-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_isFrac_46d7eee3b227
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:56.480896+00:00
-- url     : https://prove2.me/submissions/f0525ddd-6d07-4e18-8d17-440b5767ac38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_add_c90e5fd76ad2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_mul_3dd39e0d5705

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
theorem _root_.solution {x : Fin (N + 1) → Ω} {c : ℤ} {I : Chart x} {z : Ω}
    (hz : z ∈ twistMod S x c I) : ∃ t, IsFrac (S := S) x c I.1 z t := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩ := hz
    exact ⟨(f, s, e, e'), hs, hf, hse, hc, rfl⟩
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    have h0 : (0 : ℤ) ≤ ((-c).toNat : ℤ) + c := by
      have := Int.self_le_toNat (-c); omega
    refine ⟨(0, X i ^ (-c).toNat, (-c).toNat, (((-c).toNat : ℤ) + c).toNat),
      pow_mem (X_mem_monos hi) _, isHomogeneous_zero _ _ _, isHomogeneous_X_pow _ _, ?_, by simp⟩
    exact Int.toNat_of_nonneg h0
  | add a b _ _ ha hb =>
    obtain ⟨t, ht⟩ := ha
    obtain ⟨t', ht'⟩ := hb
    exact ⟨_, isFrac_add (fun s hs => eval_ne_zero_of_mem_monos I hs) ht ht'⟩
  | smul a z _ hz =>
    obtain ⟨t, ht⟩ := hz
    obtain ⟨g, u, d, hu, hg, hud, hga⟩ := a.2
    refine ⟨(g * t.1, u * t.2.1, d + t.2.2.1, d + t.2.2.2), ?_⟩
    rw [chartRing_smul_def, hga]
    exact isFrac_mul hu hg hud ht
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
