-- Prove2me | solution 1 for PI.SqfRootShift.W.eiii_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:45.480862+00:00
-- url     : https://prove2.me/submissions/72f0371c-3c41-4d85-8ad6-0d94ddb2e80e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountD
import Theorems.Thm_PI_SqfRootShift_W_frob_fix
import Theorems.Thm_PI_SqfRootShift_W_ptp_eq_imp


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
namespace PI.SqfRootShift.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] {r : ℕ} (c : (ZMod g)ˣ) {f : (ZMod g)[X]}
    (hf : Eiii g r c f) :
    ∃ P, Good c P ∧ P ∣ f ∧ 1 ≤ P.natDegree ∧ P.natDegree ≤ r := by
  obtain ⟨hlab, -, hneg⟩ := hf
  push Not at hneg
  obtain ⟨ℓ, hℓ, -, x, hx, hxc⟩ := hneg
  have hf0 : f ≠ 0 := hlab.1.ne_zero
  have hxroot : aeval x f = 0 := by
    unfold rootsBar at hx
    rw [mem_roots_map hf0] at hx
    rw [aeval_def]; exact hx
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hPd : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hint
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, aeval_def, eval₂_at_zero] at hxroot
    exact hlab.2.2 ((_root_.map_eq_zero_iff _ (algebraMap (ZMod g) (Fbar g)).injective).1 hxroot)
  have hfix := frob_fix x
  have hg2 := (Fact.out : g.Prime).two_le
  have hpos : 1 ≤ g ^ (minpoly (ZMod g) x).natDegree := Nat.one_le_pow _ _ (by omega)
  have hgk : g ≤ g ^ (minpoly (ZMod g) x).natDegree := Nat.le_self_pow (by omega) g
  have hxo : 0 < orderOf x := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨g ^ (minpoly (ZMod g) x).natDegree - 1, by omega, ?_⟩
    have h2 : x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
    exact mul_right_cancel₀ hx0 h2
  have hco : 0 < orderOf (algebraMap (ZMod g) (Fbar g) (c : ZMod g)) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨g - 1, by omega, ?_⟩
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one]
  obtain ⟨j, hj⟩ := ptp_eq_imp ℓ hℓ x _ hxo hco hxc
  refine ⟨minpoly (ZMod g) x, ⟨minpoly.monic hint, minpoly.irreducible hint, ℓ, hℓ, j,
    minpoly.dvd _ _ ?_⟩, minpoly.dvd _ _ hxroot, hPd, ?_⟩
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [hj, sub_self]
  · have := natDegree_le_of_dvd (minpoly.dvd _ _ hxroot) hf0
    rw [hlab.2.1] at this
    exact this
end PI.SqfRootShift.W
