-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_mem_idealMod_of_mul_6e0f843cd020
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:04.364869+00:00
-- url     : https://prove2.me/submissions/1083697c-563e-4e9c-81e2-970599885b9f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_not_mem_of_mem_monos_7b959cd146fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_exists_eq_of_mem_idealMod_3bbfd4d1f565
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_one_mem_idealMod_30c22dbb3514
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
theorem _root_.solution {pp : Ideal (Poly k N)} (hp : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp)
    {i j : Fin (N + 1)} (hi : (X i : Poly k N) ∉ pp) {I : Chart x} {r q : Ω} (hr : r ∈ chartRing k x I)
    (hq : q ∈ idealMod pp I) (h : x i * r = x j * q) : r ∈ idealMod pp I := by
  by_cases hI : ∃ l ∈ I.1, (X l : Poly k N) ∈ pp
  · obtain ⟨l, hl, hX⟩ := hI
    have := Submodule.smul_mem (idealMod pp I) (⟨r, hr⟩ : chartRing k x I) (one_mem_idealMod hl hX)
    rwa [chartRing_smul_def, mul_one] at this
  push Not at hI
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hr
  obtain ⟨g, s', e', hg, hs', hge, hse', rfl⟩ := exists_eq_of_mem_idealMod hq
  have h0 := eval_ne_zero_of_mem_monos I hs
  have h0' := eval_ne_zero_of_mem_monos I hs'
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff h0 h0'] at h
  have hhom : (X i * f * s' - X j * g * s).IsHomogeneous (1 + e + e') := by
    refine (((isHomogeneous_X k i).mul hf).mul hse').sub ?_
    have := ((isHomogeneous_X k j).mul hge).mul hse
    rwa [show 1 + e' + e = 1 + e + e' by omega] at this
  have hev : aeval x (X i * f * s' - X j * g * s) = 0 := by
    simp only [map_sub, map_mul, aeval_X]
    rw [h, sub_self]
  have hmem : X i * f * s' ∈ pp := by
    have h1 := pp.add_mem (hle ((mem_primeOf_of_isHomogeneous x hhom).mpr hev))
      (pp.mul_mem_right s (pp.mul_mem_left (X j) hg))
    rwa [sub_add_cancel] at h1
  have hf' : f ∈ pp := by
    rcases hp.mem_or_mem hmem with h2 | h2
    · rcases hp.mem_or_mem h2 with h3 | h3
      · exact absurd h3 hi
      · exact h3
    · exact absurd h2 (not_mem_of_mem_monos hp hI hs')
  exact Submodule.subset_span ⟨f, s, e, hf', hs, hf, hse, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
