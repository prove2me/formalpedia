-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_idealMod_prime_39c5dd2dd8c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:25:14.826073+00:00
-- url     : https://prove2.me/submissions/e6359eef-8c67-49d3-8129-e40fb881b70b

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
    (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) :
    ∀ a ∈ (1 : Submodule (chartRing k x I) Ω), ∀ b ∈ (1 : Submodule (chartRing k x I) Ω),
      a * b ∈ idealMod pp I → a ∈ idealMod pp I ∨ b ∈ idealMod pp I := by
  have := hW
  intro a ha b hb hab
  obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
  obtain ⟨b', rfl⟩ := Submodule.mem_one.mp hb
  obtain ⟨f, s, e, hs, hf, hse, hfa⟩ := a'.2
  obtain ⟨g, t, e', ht, hg, hte, hgb⟩ := b'.2
  change (a' : Ω) * (b' : Ω) ∈ idealMod pp I at hab
  obtain ⟨h, m, d, hh, hm, hhd, hmd, hab'⟩ := idealMod_mem_form pp I hab
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have ht0 := eval_ne_zero_of_mem_monos I ht
  have hm0 := eval_ne_zero_of_mem_monos I hm
  rw [hfa, hgb, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hs0 ht0) hm0] at hab'
  have hval : aeval x (f * g * m - h * (s * t)) = 0 := by
    simp only [map_sub, map_mul]
    linear_combination hab'
  have h1 : (f * g * m).IsHomogeneous (e + e' + d) := (hf.mul hg).mul hmd
  have h2 : (h * (s * t)).IsHomogeneous (e + e' + d) := by
    have := hhd.mul (hse.mul hte)
    rwa [show d + (e + e') = e + e' + d by ring] at this
  have hmem : f * g * m - h * (s * t) ∈ pp :=
    hle ((mem_primeOf_of_isHomogeneous x (h1.sub h2)).mpr hval)
  have hfgm : f * g * m ∈ pp := by
    have := pp.add_mem hmem (pp.mul_mem_right (s * t) hh)
    rwa [sub_add_cancel] at this
  have hfg : f * g ∈ pp := (hW.mem_or_mem hfgm).resolve_right (monos_not_mem hI hm)
  rcases hW.mem_or_mem hfg with hfp | hgp
  · left
    change (a' : Ω) ∈ idealMod pp I
    rw [hfa]
    exact Submodule.subset_span ⟨f, s, e, hfp, hs, hf, hse, rfl⟩
  · right
    change (b' : Ω) ∈ idealMod pp I
    rw [hgb]
    exact Submodule.subset_span ⟨g, t, e', hgp, ht, hg, hte, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
