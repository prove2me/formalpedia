-- Prove2me | solution 1 for PI.SqfRootShift.W.good_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:26.498711+00:00
-- url     : https://prove2.me/submissions/d3e550a2-fafb-4d60-bd41-752a381e249b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
import Theorems.Thm_PI_SqfRootShift_W_frob_fix
import Theorems.Thm_P2M_PI_SqfRootShift_W_aeval_eq_zero_of_dvd__aabcf90c1878

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootShift.W
theorem _root_.solution (c : (ZMod g)ˣ) (P : (ZMod g)[X]) (hP : Good c P) (z : Fbar g)
    (hz : z ∈ (P.map (algebraMap (ZMod g) (Fbar g))).roots) :
    (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (g ^ P.natDegree - 1) = 1 ∧
      ∃ ℓ, ℓ.Prime ∧ ∃ j, (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (ℓ ^ j) = 1 := by
  obtain ⟨hmon, hirr, ℓ, hℓ, j, hdvd⟩ := hP
  set c' := algebraMap (ZMod g) (Fbar g) (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := by
    rw [hc']; exact (_root_.map_ne_zero _).2 c.ne_zero
  have hz0 : aeval z P = 0 := by
    rw [mem_roots_map hmon.ne_zero] at hz
    rwa [aeval_def]
  have hmin : P = minpoly (ZMod g) z := minpoly.eq_of_irreducible_of_monic hirr hz0 hmon
  have hfix : z ^ (g ^ P.natDegree) = z := by rw [hmin]; exact frob_fix z
  have hℓj : z ^ (ℓ ^ j) = c' ^ (ℓ ^ j) := by
    have := aeval_eq_zero_of_dvd' hdvd hz0
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    rw [sub_eq_zero] at this
    exact this
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hℓ.pos j).ne'] at hℓj
    exact pow_ne_zero _ hc0 hℓj.symm
  have hcfix : c' ^ (g ^ P.natDegree) = c' := by
    rw [hc', ← map_pow, ZMod.pow_card_pow]
  set y := z * c'⁻¹ with hy
  have hy0 : y ≠ 0 := mul_ne_zero hzne (inv_ne_zero hc0)
  have hyfix : y ^ (g ^ P.natDegree) = y := by
    rw [hy, mul_pow, inv_pow, hfix, hcfix]
  have hpos : 1 ≤ g ^ P.natDegree := Nat.one_le_pow _ _ (Fact.out : g.Prime).pos
  refine ⟨?_, ℓ, hℓ, j, ?_⟩
  · have h2 : y ^ (g ^ P.natDegree - 1) * y = 1 * y := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hyfix, one_mul]
    exact mul_right_cancel₀ hy0 h2
  · rw [hy, mul_pow, inv_pow, hℓj, mul_inv_cancel₀ (pow_ne_zero _ hc0)]
end PI.SqfRootShift.W
