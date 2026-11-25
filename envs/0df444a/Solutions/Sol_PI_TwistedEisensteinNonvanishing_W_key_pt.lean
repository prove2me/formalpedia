-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.key_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:06.831634+00:00
-- url     : https://prove2.me/submissions/aa2938ec-6891-4912-a618-557e927df1d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TwistedEisensteinOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
private lemma intAt_add_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {a b : E}
    (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 + r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h' | h'
    · exact hs1 h'
    · exact hs2 h'
  · rw [map_mul, map_add, map_mul, map_mul, ← h1, ← h2]
    ring
private lemma intAt_neg_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {a : E}
    (h : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, hr⟩ := h
  exact ⟨-r, s, hs, by rw [mul_neg, hr, map_neg]⟩
private lemma intAt_qOf_pow_mul {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} (k : ℕ) {a : E}
    (h : IntAt P a) : IntAt P ((qOf P : E) ^ k * a) := by
  obtain ⟨r, s, hs, hr⟩ := h
  refine ⟨(qOf P : 𝓞 E) ^ k * r, s, hs, ?_⟩
  rw [map_mul, map_pow, map_natCast, ← hr]
  ring
end PI.TwistedEisensteinNonvanishing.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {D j : ℕ} (hjD : j ≤ D)
    {P : HeightOneSpectrum (𝓞 E)} {psi : E → K} (hpsi : PsiOk D P psi) {C gx gy : K} (hC : C ≠ 0)
    {cx cy c0 : E} (hg : gx = C * gy) (hc : cy = cx + c0)
    (hbx : gx ≠ 0 → IntAt P ((qOf P : E) ^ j * cx)) (hby : gy ≠ 0 → IntAt P ((qOf P : E) ^ j * cy)) :
    gx * psi (-cx) = (C * psi c0) * (gy * psi (-cy)) := by
  by_cases hgy : gy = 0
  · rw [hg, hgy]
    ring
  · have hgx : gx ≠ 0 := by
      rw [hg]
      exact mul_ne_zero hC hgy
    have ix := hbx hgx
    have iy := hby hgy
    have lift : ∀ t : E, IntAt P ((qOf P : E) ^ j * t) → IntAt P ((qOf P : E) ^ D * t) := by
      intro t ht
      have h := intAt_qOf_pow_mul (D - j) ht
      rwa [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjD] at h
    have i_cx := lift cx ix
    have i_cy := lift cy iy
    have i_c0 : IntAt P ((qOf P : E) ^ D * c0) := by
      have e : (qOf P : E) ^ D * c0 = (qOf P : E) ^ D * cy + -((qOf P : E) ^ D * cx) := by
        rw [hc]
        ring
      rw [e]
      exact intAt_add_twisted_eisenstein_coset i_cy (intAt_neg_twisted_eisenstein_coset i_cx)
    have i_ncy : IntAt P ((qOf P : E) ^ D * (-cy)) := by
      rw [mul_neg]
      exact intAt_neg_twisted_eisenstein_coset i_cy
    have hsplit := hpsi.1 (-cy) c0 i_ncy i_c0
    have e : -cy + c0 = -cx := by
      rw [hc]
      ring
    rw [e] at hsplit
    rw [hsplit, hg]
    ring
end PI.TwistedEisensteinNonvanishing.W
