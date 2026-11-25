-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_le_gaussNormOf_mul_a9f651f2e985
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:30.704521+00:00
-- url     : https://prove2.me/submissions/1f5252a3-b99a-4f97-a9d8-7309bdd78172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_pos_f7b56068fd3a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)
variable {w}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hna : IsNonarchimedean w) {f g : MvPolynomial ι R} (hf : f ≠ 0)
    (hg : g ≠ 0) : gaussNormOf w f * gaussNormOf w g ≤ gaussNormOf w (f * g) := by
  classical
  let _ : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hNf := gaussNormOf_pos w hf
  have hNg := gaussNormOf_pos w hg
  obtain ⟨i, hi, hmin_i⟩ :=
    (f.support.filter fun a => w (f.coeff a) = gaussNormOf w f).exists_min_image toLex (by
      obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hf
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h.symm⟩⟩)
  obtain ⟨j, hj, hmin_j⟩ :=
    (g.support.filter fun a => w (g.coeff a) = gaussNormOf w g).exists_min_image toLex (by
      obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hg
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h.symm⟩⟩)
  have hi' : w (f.coeff i) = gaussNormOf w f := (Finset.mem_filter.mp hi).2
  have hj' : w (g.coeff j) = gaussNormOf w g := (Finset.mem_filter.mp hj).2
  have ltf : ∀ a, toLex a < toLex i → w (f.coeff a) < gaussNormOf w f := by
    intro a ha
    refine lt_of_le_of_ne (le_gaussNormOf w f a) fun h => ?_
    have ha' : a ∈ f.support.filter fun a => w (f.coeff a) = gaussNormOf w f := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h⟩
      rw [h0, map_zero] at h
      exact hNf.ne h
    exact absurd (hmin_i a ha') (not_le.mpr ha)
  have ltg : ∀ a, toLex a < toLex j → w (g.coeff a) < gaussNormOf w g := by
    intro a ha
    refine lt_of_le_of_ne (le_gaussNormOf w g a) fun h => ?_
    have ha' : a ∈ g.support.filter fun a => w (g.coeff a) = gaussNormOf w g := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h⟩
      rw [h0, map_zero] at h
      exact hNg.ne h
    exact absurd (hmin_j a ha') (not_le.mpr ha)
  have key : w ((f * g).coeff (i + j)) = gaussNormOf w f * gaussNormOf w g := by
    rw [coeff_mul]
    have hk : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [hna.apply_sum_eq_of_lt (fun a => (w.map_neg a).symm) hk ?_, map_mul, hi', hj']
    intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_mul, map_mul, hi', hj']
    rcases lt_trichotomy (toLex p.1) (toLex i) with h | h | h
    · calc w (f.coeff p.1) * w (g.coeff p.2) ≤ w (f.coeff p.1) * gaussNormOf w g :=
            mul_le_mul_of_nonneg_left (le_gaussNormOf w g _) (w.nonneg _)
        _ < gaussNormOf w f * gaussNormOf w g := mul_lt_mul_of_pos_right (ltf _ h) hNg
    · have h1 : p.1 = i := toLex.injective h
      have h2 : p.2 = j := by
        rw [h1] at hp
        exact add_left_cancel hp
      exact absurd (Prod.ext h1 h2) hne
    · have h2 : toLex p.2 < toLex j := by
        by_contra hc
        rw [not_lt] at hc
        have hlt : toLex i + toLex j < toLex p.1 + toLex p.2 := add_lt_add_of_lt_of_le h hc
        have e : toLex p.1 + toLex p.2 = toLex i + toLex j := by
          rw [← toLex_add, ← toLex_add, hp]
        rw [e] at hlt
        exact lt_irrefl _ hlt
      calc w (f.coeff p.1) * w (g.coeff p.2) ≤ gaussNormOf w f * w (g.coeff p.2) :=
            mul_le_mul_of_nonneg_right (le_gaussNormOf w f _) (w.nonneg _)
        _ < gaussNormOf w f * gaussNormOf w g := mul_lt_mul_of_pos_left (ltg _ h2) hNf
  rw [← key]
  exact le_gaussNormOf w _ _
end GroundTheory.Heights₂.Heights
