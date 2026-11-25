-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_one_not_mem_idealMod_1352903a0e1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:09.697054+00:00
-- url     : https://prove2.me/submissions/02b49191-e395-406d-ab66-6da9f53947be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_not_mem_6334cbda5c89


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
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {pp : Ideal (Poly k N)}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
theorem _root_.solution (hW : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp) {I : Chart x}
    (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) : (1 : Ω) ∉ idealMod pp I := by
  have := hW
  intro h1
  obtain ⟨g, s, d, hg, hs, hgd, hsd, h1g⟩ := idealMod_mem_form pp I h1
  have hs0 := eval_ne_zero_of_mem_monos I hs
  rw [eq_div_iff hs0, one_mul] at h1g
  have hgs : g - s ∈ pp := hle ((mem_primeOf_of_isHomogeneous x (hgd.sub hsd)).mpr (by
    rw [map_sub, h1g, sub_self]))
  have hsp : s ∈ pp := by
    have := pp.sub_mem hg hgs
    rwa [sub_sub_cancel] at this
  exact monos_not_mem (pp := pp) hI hs hsp
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
