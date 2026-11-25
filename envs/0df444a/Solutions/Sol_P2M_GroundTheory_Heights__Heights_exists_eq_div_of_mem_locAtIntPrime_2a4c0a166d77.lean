-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_eq_div_of_mem_locAtIntPrime_2a4c0a166d77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:42.833012+00:00
-- url     : https://prove2.me/submissions/2e3ca3c5-11ed-4bc6-a7ab-0d9defcfda92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : Subalgebra ℤ Ω) {u : Ω}
    (hu : u ∈ locAtIntPrime p A.toSubring) :
    ∃ a ∈ A, ∃ t : ℕ, ¬ p ∣ t ∧ u = a * (t : Ω)⁻¹ := by
  induction hu using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨s, hs, rfl⟩
    · exact ⟨x, hx, 1, hp.not_dvd_one, by simp⟩
    · obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg s
      · exact ⟨1, one_mem _, n, fun h => hs (Int.natCast_dvd_natCast.2 h), by simp⟩
      · refine ⟨-1, neg_mem (one_mem _), n, fun h => hs (by
          rw [Int.dvd_neg]; exact Int.natCast_dvd_natCast.2 h), by simp [inv_neg]⟩
  | zero => exact ⟨0, zero_mem _, 1, hp.not_dvd_one, by simp⟩
  | one => exact ⟨1, one_mem _, 1, hp.not_dvd_one, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    obtain ⟨b, hb, t', ht', rfl⟩ := hy
    have h0 : (t : Ω) ≠ 0 := by
      rintro h; exact ht (by rw [show t = 0 by exact_mod_cast h]; exact dvd_zero p)
    have h0' : (t' : Ω) ≠ 0 := by
      rintro h; exact ht' (by rw [show t' = 0 by exact_mod_cast h]; exact dvd_zero p)
    refine ⟨a * t' + b * t, add_mem (mul_mem ha (A.natCast_mem _)) (mul_mem hb (A.natCast_mem _)),
      t * t', fun h => (hp.dvd_mul.1 h).elim ht ht', ?_⟩
    push_cast
    field_simp
  | neg x _ hx =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    exact ⟨-a, neg_mem ha, t, ht, by ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    obtain ⟨b, hb, t', ht', rfl⟩ := hy
    refine ⟨a * b, mul_mem ha hb, t * t', fun h => (hp.dvd_mul.1 h).elim ht ht', ?_⟩
    push_cast
    rw [mul_inv]
    ring
end GroundTheory.Heights₂.Heights
