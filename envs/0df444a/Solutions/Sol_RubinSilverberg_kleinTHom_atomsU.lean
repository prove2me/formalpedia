-- Prove2me | solution 1 for RubinSilverberg.kleinTHom_atomsU
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1a81291e-bfa3-5584-a15f-a89d6981d179

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Theorems.Thm_RubinSilverberg_icoU_THom_slots_p1
import Theorems.Thm_RubinSilverberg_icoU_THom_slots_p2
import Theorems.Thm_RubinSilverberg_icoU_THom_slots_p3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_kleinTHom_atomsU

open RubinSilverberg

set_option maxRecDepth 20000

theorem solution {K : Type*} [Field K] [CharZero K] (α β s n d : K)
    (h1 : α * β = -s) (h2 : 2 * α ^ 2 = -5 - s) (h3 : 2 * β ^ 2 = s - 5) (h4 : s ^ 2 = 5) :
    kleinTHom (-α * n + β * d) (β * n + α * d) = s ^ 30 * kleinTHom n d := by
  obtain ⟨cT_0_30, cT_1_29, cT_2_28, cT_3_27, cT_4_26, cT_5_25, cT_6_24, cT_7_23, cT_8_22, cT_9_21⟩ :=
    RubinSilverberg.icoU_THom_slots_p1 α β s h1 h2 h3 h4
  obtain ⟨cT_10_20, cT_11_19, cT_12_18, cT_13_17, cT_14_16, cT_16_14, cT_17_13, cT_18_12, cT_19_11, cT_20_10⟩ :=
    RubinSilverberg.icoU_THom_slots_p2 α β s h1 h2 h3 h4
  obtain ⟨cT_21_9, cT_22_8, cT_23_7, cT_24_6, cT_25_5, cT_26_4, cT_27_3, cT_28_2, cT_29_1, cT_30_0⟩ :=
    RubinSilverberg.icoU_THom_slots_p3 α β s h1 h2 h3 h4
  unfold kleinTHom
  linear_combination (d^30) * (cT_0_30) + (n*d^29) * (cT_1_29) + (n^2*d^28) * (cT_2_28) + (n^3*d^27) * (cT_3_27) + (n^4*d^26) * (cT_4_26) + (n^5*d^25) * (cT_5_25) + (n^6*d^24) * (cT_6_24) + (n^7*d^23) * (cT_7_23) + (n^8*d^22) * (cT_8_22) + (n^9*d^21) * (cT_9_21) + (n^10*d^20) * (cT_10_20) + (n^11*d^19) * (cT_11_19) + (n^12*d^18) * (cT_12_18) + (n^13*d^17) * (cT_13_17) + (n^14*d^16) * (cT_14_16) + (n^16*d^14) * (cT_16_14) + (n^17*d^13) * (cT_17_13) + (n^18*d^12) * (cT_18_12) + (n^19*d^11) * (cT_19_11) + (n^20*d^10) * (cT_20_10) + (n^21*d^9) * (cT_21_9) + (n^22*d^8) * (cT_22_8) + (n^23*d^7) * (cT_23_7) + (n^24*d^6) * (cT_24_6) + (n^25*d^5) * (cT_25_5) + (n^26*d^4) * (cT_26_4) + (n^27*d^3) * (cT_27_3) + (n^28*d^2) * (cT_28_2) + (n^29*d) * (cT_29_1) + (n^30) * (cT_30_0) + (-((1 : K)*s^28 + (5 : K)*s^26 + (25 : K)*s^24 + (125 : K)*s^22 + (625 : K)*s^20 + (3125 : K)*s^18 + (15625 : K)*s^16 + (78125 : K)*s^14 + (390625 : K)*s^12 + (1953125 : K)*s^10 + (9765625 : K)*s^8 + (48828125 : K)*s^6 + (244140625 : K)*s^4 + (1220703125 : K)*s^2 + (6103515625 : K)) * (n ^ 30 + 522 * n ^ 25 * d ^ 5 - 10005 * n ^ 20 * d ^ 10 - 10005 * n ^ 10 * d ^ 20 - 522 * n ^ 5 * d ^ 25 + d ^ 30)) * h4

end S_RubinSilverberg_kleinTHom_atomsU
end P2MW
export P2MW.S_RubinSilverberg_kleinTHom_atomsU (solution)
