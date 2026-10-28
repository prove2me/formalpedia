-- Prove2me | solution 1 for SCInfoDesign.Intersecting.hypotheses_equiv
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:33:36.858019+00:00
-- url     : https://prove2.me/submissions/c338a075-3c3c-4819-8ab8-b35e91b0797e

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

namespace Aux_SCID_hyp

lemma key (u d s : ℝ) (hu : 0 < u) (hd : 0 < d) (hs : 0 < s) :
    ((2 * u < d ∧ max (d - 2 * u) (d * u / (d - 2 * u)) < s) ↔
      (d / (s + d) < (d - 2 * u) / (d - u) ∧ (d - 2 * u) / (d - u) < s / (s + u))) := by
  constructor
  · rintro ⟨h2, hmax⟩
    rw [max_lt_iff] at hmax
    obtain ⟨h1, h3⟩ := hmax
    have hdu : 0 < d - u := by linarith
    have hd2u : 0 < d - 2 * u := by linarith
    rw [div_lt_iff₀ hd2u] at h3
    constructor
    · rw [div_lt_div_iff₀ (by positivity) hdu]; nlinarith
    · rw [div_lt_div_iff₀ hdu (by positivity)]; nlinarith
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy (d - u) 0 with hneg | hz | hpos
    · exfalso
      have h3 : 1 < (d - 2 * u) / (d - u) := by rw [lt_div_iff_of_neg hneg]; linarith
      have h4 : s / (s + u) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      linarith
    · exfalso
      rw [hz, div_zero] at h1
      have : 0 < d / (s + d) := by positivity
      linarith
    · rw [div_lt_div_iff₀ (by positivity) hpos] at h1
      rw [div_lt_div_iff₀ hpos (by positivity)] at h2
      have h2u : 2 * u < d := by nlinarith
      refine ⟨h2u, max_lt_iff.mpr ⟨by nlinarith, ?_⟩⟩
      rw [div_lt_iff₀ (by linarith)]
      nlinarith

end Aux_SCID_hyp

open SCInfoDesign.Intersecting in
theorem solution (P : Params) (hu : 0 < P.δu) (hd : 0 < P.δd) (hIS : 0 < P.δIS) :
    P.τbarIS 1 = P.δIS / (P.δIS + P.δu) ∧
    P.τlowIS 0 = P.δd / (P.δIS + P.δd) ∧
    ((2 * P.δu < P.δd ∧ max (P.δd - 2 * P.δu) (P.δd * P.δu / (P.δd - 2 * P.δu)) < P.δIS) ↔
      (P.τlowIS 0 < P.ξbreve ∧ P.ξbreve < P.τbarIS 1)) := by
  have e1 : P.τbarIS 1 = P.δIS / (P.δIS + P.δu) := by
    unfold Params.τbarIS
    unfold Params.δIS Params.δu at *
    have h1 : P.b₁ - P.a₀ + (P.b₀ - P.b₁) = P.b₀ - P.a₀ := by ring
    rw [h1]
    have hne : P.b₀ - P.a₀ ≠ 0 := by linarith
    field_simp <;> ring
  have e2 : P.τlowIS 0 = P.δd / (P.δIS + P.δd) := by
    unfold Params.τlowIS
    unfold Params.δIS Params.δd at *
    have h1 : P.b₁ - P.a₀ + (P.a₀ - P.a₁) = P.b₁ - P.a₁ := by ring
    rw [h1]
    ring
  have e3 : P.ξbreve = (P.δd - 2 * P.δu) / (P.δd - P.δu) := rfl
  refine ⟨e1, e2, ?_⟩
  rw [e1, e2, e3]
  exact Aux_SCID_hyp.key P.δu P.δd P.δIS hu hd hIS
