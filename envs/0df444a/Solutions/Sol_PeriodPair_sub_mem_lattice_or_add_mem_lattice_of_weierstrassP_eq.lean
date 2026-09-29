-- Prove2me | solution 1 for PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fc44cd7e-8a1a-5fd4-a970-38ca53ae42c8

import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_isUniformization_toPoint
import Theorems.Thm_PeriodPair_discriminant_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq

set_option autoImplicit false

noncomputable section

open PeriodPair

theorem solution (L : PeriodPair) {a b : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (h : L.weierstrassP a = L.weierstrassP b) :
    a - b ∈ L.lattice ∨ a + b ∈ L.lattice := by
  have hΔ : L.DiscriminantNeZero := PeriodPair.discriminant_ne_zero L
  obtain ⟨hadd, -, hker⟩ := PeriodPair.isUniformization_toPoint L hΔ

  have hsq : L.derivWeierstrassP a ^ 2 = L.derivWeierstrassP b ^ 2 := by
    rw [L.derivWeierstrassP_sq a ha, L.derivWeierstrassP_sq b hb, h]

  have hneg : ∀ z : ℂ, L.toPoint hΔ (-z) = -L.toPoint hΔ z := by
    intro z
    have h0 := hadd z (-z)
    rw [add_neg_cancel, toPoint_zero] at h0
    exact (neg_eq_of_add_eq_zero_right h0.symm).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hd | hd
  ·
    left
    apply hker
    have hab : L.toPoint hΔ a = L.toPoint hΔ b := by
      rw [toPoint_of_notMem L hΔ ha, toPoint_of_notMem L hΔ hb]
      congr 1 <;> simp [hd]
    rw [sub_eq_add_neg, hadd, hneg, hab, add_neg_cancel]
  ·
    right
    apply hker
    have hab : L.toPoint hΔ a = -L.toPoint hΔ b := by
      rw [toPoint_of_notMem L hΔ ha, toPoint_of_notMem L hΔ hb,
        WeierstrassCurve.Affine.Point.neg_some]
      congr 1 <;> simp [WeierstrassCurve.Affine.negY, h, hd, neg_div]
    rw [hadd, hab, neg_add_cancel]

end
end S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq
end P2MW
export P2MW.S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq (solution)
