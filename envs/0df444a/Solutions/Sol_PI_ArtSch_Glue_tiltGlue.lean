-- Prove2me | solution 1 for PI.ArtSch.Glue.tiltGlue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:58.401138+00:00
-- url     : https://prove2.me/submissions/efd20e25-c321-421f-98ce-96c79f472d5e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero
import Theorems.Thm_PI_ArtSch_Glue_valb_le_of_coeff_eq_zero
import Theorems.Thm_PI_ArtSch_Glue_exists_small
import Theorems.Thm_PI_ArtSch_Glue_frob_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.Glue
open scoped NNReal
noncomputable section
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.ArtSch.Glue
theorem _root_.solution : TiltGlue := by
  intro hR hD hS l _ a
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (OCb l)) a
  have hs0 : (s : OCb l) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  obtain ⟨c, hc⟩ : ∃ c : OCb l, c = (s : OCb l) ^ (l - 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : OCb l, b = x * (s : OCb l) ^ (l - 1) := ⟨_, rfl⟩
  have hvs : 0 < valb l ((s : OCb l) ^ l) := by
    rw [pos_iff_ne_zero, Ne, PreTilt.map_eq_zero]
    exact pow_ne_zero _ hs0
  obtain ⟨n, hn⟩ := exists_small (l := l) (valb l ((s : OCb l) ^ l)) hvs
  obtain ⟨z0, hz0⟩ := hR l (PreTilt.coeff n c) (PreTilt.coeff n b)
  obtain ⟨z, hz'⟩ : ∃ z : OCb l, PreTilt.coeff n z = z0 :=
    Perfection.coeff_surjective (frob_surj (l := l) hR) n z0
  obtain ⟨rr, hrr⟩ : ∃ rr : OCb l, rr = z ^ l - c * z - b := ⟨_, rfl⟩
  have hcr : PreTilt.coeff n rr = 0 := by
    rw [hrr, map_sub, map_sub, map_mul, map_pow, hz']
    exact hz0
  have hvr : valb l rr < valb l ((s : OCb l) ^ l) :=
    lt_of_le_of_lt (valb_le_of_coeff_eq_zero rr n hcr) hn
  obtain ⟨e, he⟩ := hD l rr ((s : OCb l) ^ l) hvr.le
  have hve : valb l e < 1 := by
    by_contra hge
    push_neg at hge
    have h3 : valb l ((s : OCb l) ^ l) ≤ valb l rr := by
      rw [he, map_mul]
      exact le_mul_of_one_le_right zero_le hge
    exact absurd hvr (not_lt.mpr h3)
  obtain ⟨w, hw⟩ := hS l (-e) (by rwa [Valuation.map_neg])
  obtain ⟨Z, hZ⟩ : ∃ Z : OCb l, Z = z + (s : OCb l) * w := ⟨_, rfl⟩
  have hfrob : Z ^ l = z ^ l + (s : OCb l) ^ l * w ^ l := by
    rw [hZ, add_pow_char, mul_pow]
  have hcs : c * (s : OCb l) = (s : OCb l) ^ l := by
    rw [hc, ← pow_succ, Nat.sub_add_cancel hl1]
  have he1 : z ^ l - c * z - b = (s : OCb l) ^ l * e := by rw [← hrr]; exact he
  have key : Z ^ l - c * Z - b = 0 := by
    linear_combination hfrob + he1 + (s : OCb l) ^ l * hw - w * hcs - c * hZ
  refine ⟨IsLocalization.mk' (Cb l) Z s, ?_⟩
  simp only [IsFractionRing.mk'_eq_div]
  have hS0 : algebraMap (OCb l) (Cb l) (s : OCb l) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hmap := congrArg (algebraMap (OCb l) (Cb l)) key
  rw [map_sub, map_sub, map_mul, map_pow, map_zero, hc, hb, map_mul, map_pow] at hmap
  have hT0 : algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) ≠ 0 := pow_ne_zero _ hS0
  have hSl : algebraMap (OCb l) (Cb l) (s : OCb l) ^ l =
      algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) * algebraMap (OCb l) (Cb l) (s : OCb l) := by
    rw [← pow_succ, Nat.sub_add_cancel hl1]
  rw [div_pow, hSl, show algebraMap (OCb l) (Cb l) Z ^ l =
      algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) * algebraMap (OCb l) (Cb l) Z +
        algebraMap (OCb l) (Cb l) x * algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) by
      linear_combination hmap]
  field_simp
  ring
end PI.ArtSch.Glue
