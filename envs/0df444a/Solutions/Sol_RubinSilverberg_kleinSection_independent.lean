-- Prove2me | solution 1 for RubinSilverberg.kleinSection_independent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9dd0a78b-3bda-585f-a108-5b117b2f2e37

import Theorems.Thm_RubinSilverberg_pt_kleinCurve_ne_zero_and_five_smul
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Abel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_kleinSection_independent
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "WeierstrassCurve~cusp WeierstrassCurve.Affine WeierstrassCurve.Affine.Point RubinSilverberg"

namespace M4cP4RS

section Indep

variable {K : Type*} [Field K]

theorem twelve_mul_kleinX [CharZero K] (u : K) :
    12 * kleinX u = (u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1) := by
  unfold kleinX
  ring

theorem twelve_mul_kleinX_rotate [CharZero K] (ζ u : K) (hζ5 : ζ ^ 5 = 1) :
    12 * kleinX (ζ * u) = (u ^ 10 + 12 * ζ ^ 3 * u ^ 8 - 12 * ζ ^ 2 * u ^ 7 + 24 * ζ * u ^ 6 + 30 * u ^ 5 + 60 * ζ ^ 4 * u ^ 4 + 36 * ζ ^ 3 * u ^ 3 + 24 * ζ ^ 2 * u ^ 2 + 12 * ζ * u + 1) := by
  unfold kleinX
  linear_combination (
      (1 : K) * ζ ^ 5 * u ^ 10 + (1 : K) * u ^ 10 + (12 : K) * ζ ^ 3 * u ^ 8
        + (-12 : K) * ζ ^ 2 * u ^ 7 + (24 : K) * ζ * u ^ 6 + (30 : K) * u ^ 5) * hζ5

set_option maxHeartbeats 16000000 in

theorem cert_x_ne (ζ u : K) (hΦ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    60 * kleinV u ^ 2 = ((u ^ 10 + 12 * ζ ^ 3 * u ^ 8 - 12 * ζ ^ 2 * u ^ 7 + 24 * ζ * u ^ 6 + 30 * u ^ 5 + 60 * ζ ^ 4 * u ^ 4 + 36 * ζ ^ 3 * u ^ 3 + 24 * ζ ^ 2 * u ^ 2 + 12 * ζ * u + 1) - (u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1)) * (
      (-2 : K) * ζ ^ 3 * u ^ 14 + (1 : K) * ζ ^ 2 * u ^ 14 + (-1 : K) * ζ * u ^ 14
        + (-3 : K) * u ^ 14 + (2 : K) * ζ ^ 3 * u ^ 13 + (4 : K) * ζ ^ 2 * u ^ 13
        + (1 : K) * ζ * u ^ 13 + (3 : K) * u ^ 13 + (11 : K) * ζ ^ 3 * u ^ 12
        + (-3 : K) * ζ ^ 2 * u ^ 12 + (8 : K) * ζ * u ^ 12 + (4 : K) * u ^ 12
        + (-19 : K) * ζ ^ 3 * u ^ 11 + (-13 : K) * ζ ^ 2 * u ^ 11 + (-7 : K) * ζ * u ^ 11
        + (-26 : K) * u ^ 11 + (-15 : K) * ζ ^ 3 * u ^ 10 + (20 : K) * ζ ^ 2 * u ^ 10
        + (-20 : K) * ζ * u ^ 10 + (15 : K) * u ^ 10 + (48 : K) * ζ ^ 3 * u ^ 9
        + (26 : K) * ζ ^ 2 * u ^ 9 + (24 : K) * ζ * u ^ 9 + (22 : K) * u ^ 9
        + (-13 : K) * ζ ^ 3 * u ^ 8 + (-26 : K) * ζ ^ 2 * u ^ 8 + (31 : K) * ζ * u ^ 8
        + (-57 : K) * u ^ 8 + (-24 : K) * ζ ^ 3 * u ^ 7 + (2 : K) * ζ ^ 2 * u ^ 7
        + (-22 : K) * ζ * u ^ 7 + (-11 : K) * u ^ 7 + (26 : K) * ζ ^ 3 * u ^ 6
        + (2 : K) * ζ ^ 2 * u ^ 6 + (-22 : K) * ζ * u ^ 6 + (4 : K) * u ^ 6
        + (-20 : K) * ζ ^ 3 * u ^ 5 + (-15 : K) * ζ ^ 2 * u ^ 5 + (15 : K) * ζ * u ^ 5
        + (20 : K) * u ^ 5 + (12 : K) * ζ ^ 3 * u ^ 4 + (19 : K) * ζ ^ 2 * u ^ 4
        + (6 : K) * ζ * u ^ 4 + (-7 : K) * u ^ 4 + (-7 : K) * ζ ^ 3 * u ^ 3
        + (-14 : K) * ζ ^ 2 * u ^ 3 + (-16 : K) * ζ * u ^ 3 + (2 : K) * u ^ 3
        + (4 : K) * ζ ^ 3 * u ^ 2 + (8 : K) * ζ ^ 2 * u ^ 2 + (12 : K) * ζ * u ^ 2
        + (6 : K) * u ^ 2 + (-1 : K) * ζ ^ 3 * u + (-2 : K) * ζ ^ 2 * u + (-3 : K) * ζ * u
        + (-4 : K) * u) := by
  unfold kleinV
  linear_combination (
      (24 : K) * ζ ^ 2 * u ^ 22 + (-36 : K) * ζ * u ^ 22 + (24 : K) * u ^ 22
        + (-24 : K) * ζ ^ 2 * u ^ 21 + (-48 : K) * ζ * u ^ 21 + (72 : K) * u ^ 21
        + (-132 : K) * ζ ^ 2 * u ^ 20 + (192 : K) * ζ * u ^ 20 + (-60 : K) * u ^ 20
        + (228 : K) * ζ ^ 2 * u ^ 19 + (60 : K) * ζ * u ^ 19 + (-288 : K) * u ^ 19
        + (120 : K) * ζ ^ 3 * u ^ 18 + (-528 : K) * ζ * u ^ 18 + (408 : K) * u ^ 18
        + (-120 : K) * ζ ^ 3 * u ^ 17 + (-624 : K) * ζ ^ 2 * u ^ 17 + (156 : K) * ζ * u ^ 17
        + (852 : K) * u ^ 17 + (-660 : K) * ζ ^ 3 * u ^ 16 + (924 : K) * ζ ^ 2 * u ^ 16
        + (48 : K) * ζ * u ^ 16 + (-312 : K) * u ^ 16 + (1140 : K) * ζ ^ 3 * u ^ 15
        + (-468 : K) * ζ ^ 2 * u ^ 15 + (-372 : K) * ζ * u ^ 15 + (-300 : K) * u ^ 15
        + (900 : K) * ζ ^ 3 * u ^ 14 + (-1728 : K) * ζ ^ 2 * u ^ 14 + (1920 : K) * ζ * u ^ 14
        + (-1092 : K) * u ^ 14 + (-2880 : K) * ζ ^ 3 * u ^ 13 + (2100 : K) * ζ ^ 2 * u ^ 13
        + (-432 : K) * ζ * u ^ 13 + (1212 : K) * u ^ 13 + (780 : K) * ζ ^ 3 * u ^ 12
        + (-1092 : K) * ζ ^ 2 * u ^ 12 + (-2592 : K) * ζ * u ^ 12 + (4332 : K) * u ^ 12
        + (1440 : K) * ζ ^ 3 * u ^ 11 + (-1008 : K) * ζ ^ 2 * u ^ 11 + (984 : K) * ζ * u ^ 11
        + (-1416 : K) * u ^ 11 + (-1560 : K) * ζ ^ 3 * u ^ 10 + (2256 : K) * ζ ^ 2 * u ^ 10
        + (684 : K) * ζ * u ^ 10 + (-1380 : K) * u ^ 10 + (1200 : K) * ζ ^ 3 * u ^ 9
        + (-1224 : K) * ζ ^ 2 * u ^ 9 + (-300 : K) * ζ * u ^ 9 + (324 : K) * u ^ 9
        + (-720 : K) * ζ ^ 3 * u ^ 8 + (300 : K) * ζ ^ 2 * u ^ 8 + (-36 : K) * ζ * u ^ 8
        + (456 : K) * u ^ 8 + (420 : K) * ζ ^ 3 * u ^ 7 + (-12 : K) * ζ ^ 2 * u ^ 7
        + (348 : K) * ζ * u ^ 7 + (-1020 : K) * u ^ 7 + (-240 : K) * ζ ^ 3 * u ^ 6
        + (12 : K) * ζ ^ 2 * u ^ 6 + (-276 : K) * ζ * u ^ 6 + (504 : K) * u ^ 6
        + (60 : K) * ζ ^ 3 * u ^ 5 + (-84 : K) * ζ ^ 2 * u ^ 5 + (84 : K) * ζ * u ^ 5
        + (-60 : K) * u ^ 5 + (36 : K) * ζ ^ 2 * u ^ 4 + (-60 : K) * ζ * u ^ 4 + (24 : K) * u ^ 4
        + (24 : K) * ζ * u ^ 3 + (-24 : K) * u ^ 3 + (12 : K) * u ^ 2) * hΦ

set_option maxHeartbeats 16000000 in

theorem cert_x_ne_double (ζ u : K) (hΦ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    20736 * kleinV u ^ 5 = (4 * ((u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1) ^ 3 - 3 * kleinH u * (u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1) + 2 * kleinT u) * (u ^ 10 + 12 * ζ ^ 3 * u ^ 8 - 12 * ζ ^ 2 * u ^ 7 + 24 * ζ * u ^ 6 + 30 * u ^ 5 + 60 * ζ ^ 4 * u ^ 4 + 36 * ζ ^ 3 * u ^ 3 + 24 * ζ ^ 2 * u ^ 2 + 12 * ζ * u + 1)
        - 9 * ((u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1) ^ 2 - kleinH u) ^ 2
        + 8 * (u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1) * ((u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1) ^ 3 - 3 * kleinH u * (u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1) + 2 * kleinT u)) * (
      (1 : K) * u ^ 20 + (-1 : K) * ζ ^ 3 * u ^ 19 + (-2 : K) * ζ ^ 3 * u ^ 18
        + (1 : K) * ζ ^ 2 * u ^ 18 + (1 : K) * ζ * u ^ 18 + (-8 : K) * u ^ 18
        + (8 : K) * ζ ^ 3 * u ^ 17 + (3 : K) * ζ ^ 2 * u ^ 17 + (3 : K) * ζ * u ^ 17
        + (8 : K) * u ^ 17 + (10 : K) * ζ ^ 3 * u ^ 16 + (-5 : K) * ζ ^ 2 * u ^ 16
        + (-5 : K) * ζ * u ^ 16 + (25 : K) * u ^ 16 + (-40 : K) * ζ ^ 3 * u ^ 15
        + (-15 : K) * ζ ^ 2 * u ^ 15 + (-15 : K) * ζ * u ^ 15 + (-51 : K) * u ^ 15
        + (-19 : K) * ζ ^ 3 * u ^ 14 + (25 : K) * ζ ^ 2 * u ^ 14 + (25 : K) * ζ * u ^ 14
        + (-10 : K) * u ^ 14 + (112 : K) * ζ ^ 3 * u ^ 13 + (44 : K) * ζ ^ 2 * u ^ 13
        + (44 : K) * ζ * u ^ 13 + (118 : K) * u ^ 13 + (-13 : K) * ζ ^ 3 * u ^ 12
        + (-68 : K) * ζ ^ 2 * u ^ 12 + (-68 : K) * ζ * u ^ 12 + (-113 : K) * u ^ 12
        + (-165 : K) * ζ ^ 3 * u ^ 11 + (-55 : K) * ζ ^ 2 * u ^ 11 + (-55 : K) * ζ * u ^ 11
        + (-75 : K) * u ^ 11 + (110 : K) * ζ ^ 3 * u ^ 10 + (110 : K) * ζ ^ 2 * u ^ 10
        + (110 : K) * ζ * u ^ 10 + (217 : K) * u ^ 10 + (88 : K) * ζ ^ 3 * u ^ 9
        + (-110 : K) * u ^ 9 + (-149 : K) * ζ ^ 3 * u ^ 8 + (-88 : K) * ζ ^ 2 * u ^ 8
        + (-88 : K) * ζ * u ^ 8 + (-76 : K) * u ^ 8 + (56 : K) * ζ ^ 3 * u ^ 7
        + (61 : K) * ζ ^ 2 * u ^ 7 + (61 : K) * ζ * u ^ 7 + (131 : K) * u ^ 7
        + (40 : K) * ζ ^ 3 * u ^ 6 + (5 : K) * ζ ^ 2 * u ^ 6 + (5 : K) * ζ * u ^ 6
        + (-75 : K) * u ^ 6 + (-60 : K) * ζ ^ 3 * u ^ 5 + (-35 : K) * ζ ^ 2 * u ^ 5
        + (-35 : K) * ζ * u ^ 5 + (12 : K) * u ^ 5 + (33 : K) * ζ ^ 3 * u ^ 4
        + (25 : K) * ζ ^ 2 * u ^ 4 + (25 : K) * ζ * u ^ 4 + (10 : K) * u ^ 4
        + (-9 : K) * ζ ^ 3 * u ^ 3 + (-8 : K) * ζ ^ 2 * u ^ 3 + (-8 : K) * ζ * u ^ 3
        + (-6 : K) * u ^ 3 + (1 : K) * ζ ^ 3 * u ^ 2 + (1 : K) * ζ ^ 2 * u ^ 2
        + (1 : K) * ζ * u ^ 2 + (1 : K) * u ^ 2) := by
  unfold kleinV kleinH kleinT
  linear_combination (
      (20736 : K) * ζ ^ 2 * u ^ 53 + (-20736 : K) * ζ * u ^ 53 + (82944 : K) * ζ ^ 2 * u ^ 52
        + (-124416 : K) * ζ * u ^ 52 + (20736 : K) * u ^ 52 + (103680 : K) * ζ ^ 2 * u ^ 51
        + (-290304 : K) * ζ * u ^ 51 + (145152 : K) * u ^ 51 + (-311040 : K) * ζ * u ^ 50
        + (269568 : K) * u ^ 50 + (103680 : K) * ζ ^ 3 * u ^ 49 + (-311040 : K) * ζ ^ 2 * u ^ 49
        + (207360 : K) * u ^ 49 + (414720 : K) * ζ ^ 3 * u ^ 48 + (-62208 : K) * ζ ^ 2 * u ^ 48
        + (-248832 : K) * ζ * u ^ 48 + (518400 : K) * ζ ^ 3 * u ^ 47
        + (2032128 : K) * ζ ^ 2 * u ^ 47 + (-3877632 : K) * ζ * u ^ 47 + (456192 : K) * u ^ 47
        + (3006720 : K) * ζ ^ 2 * u ^ 46 + (-10222848 : K) * ζ * u ^ 46 + (5370624 : K) * u ^ 46
        + (-1036800 : K) * ζ ^ 3 * u ^ 45 + (-11093760 : K) * ζ * u ^ 45 + (10285056 : K) * u ^ 45
        + (1969920 : K) * ζ ^ 3 * u ^ 44 + (-9538560 : K) * ζ ^ 2 * u ^ 44
        + (7568640 : K) * u ^ 44 + (14100480 : K) * ζ ^ 3 * u ^ 43
        + (-17024256 : K) * ζ ^ 2 * u ^ 43 + (7485696 : K) * ζ * u ^ 43
        + (18662400 : K) * ζ ^ 3 * u ^ 42 + (6345216 : K) * ζ ^ 2 * u ^ 42
        + (-37200384 : K) * ζ * u ^ 42 + (-953856 : K) * u ^ 42 + (24053760 : K) * ζ ^ 2 * u ^ 41
        + (-125888256 : K) * ζ * u ^ 41 + (70979328 : K) * u ^ 41
        + (-34732800 : K) * ζ ^ 3 * u ^ 40 + (-139034880 : K) * ζ * u ^ 40
        + (142912512 : K) * u ^ 40 + (-10679040 : K) * ζ ^ 3 * u ^ 39
        + (-88231680 : K) * ζ ^ 2 * u ^ 39 + (98910720 : K) * u ^ 39
        + (163088640 : K) * ζ ^ 3 * u ^ 38 + (-237779712 : K) * ζ ^ 2 * u ^ 38
        + (149548032 : K) * ζ * u ^ 38 + (237945600 : K) * ζ ^ 3 * u ^ 37
        + (-157033728 : K) * ζ ^ 2 * u ^ 37 + (-73260288 : K) * ζ * u ^ 37
        + (-85370112 : K) * u ^ 37 + (-4458240 : K) * ζ ^ 2 * u ^ 36
        + (-604081152 : K) * ζ * u ^ 36 + (378245376 : K) * u ^ 36
        + (-390355200 : K) * ζ ^ 3 * u ^ 35 + (-681799680 : K) * ζ * u ^ 35
        + (841860864 : K) * u ^ 35 + (-394813440 : K) * ζ ^ 3 * u ^ 34
        + (-139034880 : K) * ζ ^ 2 * u ^ 34 + (533848320 : K) * u ^ 34
        + (677341440 : K) * ζ ^ 3 * u ^ 33 + (-901580544 : K) * ζ ^ 2 * u ^ 33
        + (762545664 : K) * ζ * u ^ 33 + (1215648000 : K) * ζ ^ 3 * u ^ 32
        + (-1009241856 : K) * ζ ^ 2 * u ^ 32 + (354357504 : K) * ζ * u ^ 32
        + (-619052544 : K) * u ^ 32 + (-412646400 : K) * ζ ^ 2 * u ^ 31
        + (-767003904 : K) * ζ * u ^ 31 + (524765952 : K) * u ^ 31
        + (-1498176000 : K) * ζ ^ 3 * u ^ 30 + (-825292800 : K) * ζ * u ^ 30
        + (1668584448 : K) * u ^ 30 + (-1910822400 : K) * ζ ^ 3 * u ^ 29
        + (955411200 : K) * ζ ^ 2 * u ^ 29 + (955411200 : K) * u ^ 29
        + (412646400 : K) * ζ ^ 3 * u ^ 28 + (430645248 : K) * ζ ^ 2 * u ^ 28
        + (524765952 : K) * ζ * u ^ 28 + (1780704000 : K) * ζ ^ 3 * u ^ 27
        + (-35831808 : K) * ζ ^ 2 * u ^ 27 + (-22457088 : K) * ζ * u ^ 27
        + (-1067530752 : K) * u ^ 27 + (677341440 : K) * ζ ^ 2 * u ^ 26
        + (26915328 : K) * ζ * u ^ 26 + (-762545664 : K) * u ^ 26
        + (-282528000 : K) * ζ ^ 3 * u ^ 25 + (681799680 : K) * ζ * u ^ 25
        + (-457560576 : K) * u ^ 25 + (394813440 : K) * ζ ^ 3 * u ^ 24
        + (-533848320 : K) * ζ ^ 2 * u ^ 24 + (139034880 : K) * u ^ 24
        + (-4458240 : K) * ζ ^ 3 * u ^ 23 + (-155602944 : K) * ζ ^ 2 * u ^ 23
        + (-378245376 : K) * ζ * u ^ 23 + (-542764800 : K) * ζ ^ 3 * u ^ 22
        + (144923904 : K) * ζ ^ 2 * u ^ 22 + (-67205376 : K) * ζ * u ^ 22
        + (234752256 : K) * u ^ 22 + (-163088640 : K) * ζ ^ 2 * u ^ 21
        + (91259136 : K) * ζ * u ^ 21 + (149548032 : K) * u ^ 21
        + (152409600 : K) * ζ ^ 3 * u ^ 20 + (-139034880 : K) * ζ * u ^ 20
        + (64343808 : K) * u ^ 20 + (-10679040 : K) * ζ ^ 3 * u ^ 19
        + (98910720 : K) * ζ ^ 2 * u ^ 19 + (-88231680 : K) * u ^ 19
        + (-24053760 : K) * ζ ^ 3 * u ^ 18 + (27931392 : K) * ζ ^ 2 * u ^ 18
        + (70979328 : K) * ζ * u ^ 18 + (50803200 : K) * ζ ^ 3 * u ^ 17
        + (-29901312 : K) * ζ ^ 2 * u ^ 17 + (16754688 : K) * ζ * u ^ 17 + (-6801408 : K) * u ^ 17
        + (14100480 : K) * ζ ^ 2 * u ^ 16 + (-19761408 : K) * ζ * u ^ 16 + (-7485696 : K) * u ^ 16
        + (-16070400 : K) * ζ ^ 3 * u ^ 15 + (11093760 : K) * ζ * u ^ 15 + (-8169984 : K) * u ^ 15
        + (-1969920 : K) * ζ ^ 3 * u ^ 14 + (-7568640 : K) * ζ ^ 2 * u ^ 14
        + (9538560 : K) * u ^ 14 + (3006720 : K) * ζ ^ 3 * u ^ 13
        + (-2198016 : K) * ζ ^ 2 * u ^ 13 + (-5370624 : K) * ζ * u ^ 13
        + (-1555200 : K) * ζ ^ 3 * u ^ 12 + (2301696 : K) * ζ ^ 2 * u ^ 12
        + (-1430784 : K) * ζ * u ^ 12 + (-1161216 : K) * u ^ 12 + (-414720 : K) * ζ ^ 2 * u ^ 11
        + (1534464 : K) * ζ * u ^ 11 + (-248832 : K) * u ^ 11 + (518400 : K) * ζ ^ 3 * u ^ 10
        + (-311040 : K) * ζ * u ^ 10 + (663552 : K) * u ^ 10 + (103680 : K) * ζ ^ 3 * u ^ 9
        + (207360 : K) * ζ ^ 2 * u ^ 9 + (-311040 : K) * u ^ 9 + (-103680 : K) * ζ ^ 3 * u ^ 8
        + (62208 : K) * ζ ^ 2 * u ^ 8 + (145152 : K) * ζ * u ^ 8 + (-62208 : K) * ζ ^ 2 * u ^ 7
        + (41472 : K) * ζ * u ^ 7 + (62208 : K) * u ^ 7 + (-41472 : K) * ζ * u ^ 6
        + (20736 : K) * u ^ 6 + (-20736 : K) * u ^ 5) * hΦ

theorem indep_of_five_smul {G : Type*} [AddCommGroup G] {Q R : G} (hQ0 : Q ≠ 0)
    (hQ5 : (5 : ℤ) • Q = 0) (hR0 : R ≠ 0) (hR5 : (5 : ℤ) • R = 0) (h1 : R ≠ Q) (h1' : R ≠ -Q)
    (h2 : R ≠ (2 : ℤ) • Q) (h2' : R ≠ -((2 : ℤ) • Q)) {i j : ℤ} (h : i • Q + j • R = 0) :
    (5 : ℤ) ∣ i ∧ (5 : ℤ) ∣ j := by

  have red : ∀ {P : G}, (5 : ℤ) • P = 0 → ∀ n : ℤ, n • P = (n % 5) • P := by
    intro P hP n
    have e : n = n % 5 + n / 5 * 5 := by omega
    conv_lhs => rw [e, add_zsmul, mul_zsmul, hP, zsmul_zero, add_zero]

  have scale : ∀ c : ℤ, (c * i % 5) • Q + (c * j % 5) • R = 0 := by
    intro c
    have hc : c • (i • Q + j • R) = 0 := by rw [h, zsmul_zero]
    rwa [zsmul_add, ← mul_zsmul, ← mul_zsmul, red hQ5 (c * i), red hR5 (c * j)] at hc

  have excl : ∀ r : ℤ, 0 ≤ r → r < 5 → r • Q + R = 0 → False := by
    intro r hr0 hr5 hr
    have hR : R = -(r • Q) := eq_neg_of_add_eq_zero_right hr
    interval_cases r
    · rw [zero_zsmul, _root_.neg_zero] at hR
      exact hR0 hR
    · rw [one_zsmul] at hR
      exact h1' hR
    · exact h2' hR
    · refine h2 ?_
      rw [hR, neg_eq_iff_add_eq_zero, ← add_zsmul]
      exact hQ5
    · refine h1 ?_
      rw [hR, neg_eq_iff_add_eq_zero, ← add_one_zsmul]
      exact hQ5

  have inv : ∀ n : ℤ, ¬ (5 : ℤ) ∣ n → ∃ c : ℤ, c * n % 5 = 1 := by
    intro n hn
    have h0 := Int.emod_nonneg n (by norm_num : (5 : ℤ) ≠ 0)
    have h4 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 5)
    have hne : n % 5 ≠ 0 := fun h0 => hn (Int.dvd_of_emod_eq_zero h0)
    generalize hr : n % 5 = r at h0 h4 hne
    interval_cases r
    · exact (hne rfl).elim
    · exact ⟨1, by rw [Int.mul_emod, hr]; norm_num⟩
    · exact ⟨3, by rw [Int.mul_emod, hr]; norm_num⟩
    · exact ⟨2, by rw [Int.mul_emod, hr]; norm_num⟩
    · exact ⟨4, by rw [Int.mul_emod, hr]; norm_num⟩
  have hj : (5 : ℤ) ∣ j := by
    by_contra hj
    obtain ⟨c, hc⟩ := inv j hj
    have hs := scale c
    rw [hc, one_zsmul] at hs
    exact excl _ (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) hs
  refine ⟨?_, hj⟩
  by_contra hi
  obtain ⟨c, hc⟩ := inv i hi
  have hs := scale c
  have hcj : c * j % 5 = 0 := Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_right hj c)
  rw [hc, one_zsmul, hcj, zero_zsmul, add_zero] at hs
  exact hQ0 hs

theorem main [CharZero K] [DecidableEq K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (u : K)
    (hV : kleinV u ≠ 0) (i j : ℤ)
    (h : i • pt (kleinCurve u) (kleinX u) (kleinY u)
      + j • pt (kleinCurve u) (kleinX (ζ * u)) (kleinY (ζ * u)) = 0) :
    (5 : ℤ) ∣ i ∧ (5 : ℤ) ∣ j := by

  have hζ5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hΦ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    have hs := hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hs
    linear_combination hs

  obtain ⟨hQ0, hQ5⟩ := RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul u u hV rfl
  obtain ⟨hR0, hR5⟩ := RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul u (ζ * u) hV (by rw [mul_pow, hζ5, one_mul])
  have hnsQ : (kleinCurve u).toAffine.Nonsingular (kleinX u) (kleinY u) := by
    by_contra hn
    exact hQ0 (pt_eq_zero hn)
  have hnsR : (kleinCurve u).toAffine.Nonsingular (kleinX (ζ * u)) (kleinY (ζ * u)) := by
    by_contra hn
    exact hR0 (pt_eq_zero hn)
  rw [pt_eq_some hnsQ, pt_eq_some hnsR] at h
  rw [pt_eq_some hnsQ] at hQ0 hQ5
  rw [pt_eq_some hnsR] at hR0 hR5

  have hX := twelve_mul_kleinX u
  have hXR := twelve_mul_kleinX_rotate ζ u hζ5

  have hx1 : kleinX (ζ * u) ≠ kleinX u := by
    intro he
    have c1 := cert_x_ne ζ u hΦ
    have hlit : (u ^ 10 + 12 * ζ ^ 3 * u ^ 8 - 12 * ζ ^ 2 * u ^ 7 + 24 * ζ * u ^ 6 + 30 * u ^ 5 + 60 * ζ ^ 4 * u ^ 4 + 36 * ζ ^ 3 * u ^ 3 + 24 * ζ ^ 2 * u ^ 2 + 12 * ζ * u + 1) = (u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 12 * u + 1) := by
      rw [← hX, ← hXR, he]
    rw [hlit, sub_self, zero_mul] at c1
    have : kleinV u ^ 2 = 0 := by
      have := mul_eq_zero.mp c1
      exact this.resolve_left (by norm_num)
    exact hV (pow_eq_zero_iff (by norm_num) |>.mp this)
  have h1 : Point.some _ _ hnsR ≠ Point.some _ _ hnsQ := fun he => hx1 (Point.some.inj he).1
  have h1' : Point.some _ _ hnsR ≠ -Point.some _ _ hnsQ := by
    rw [neg_some]
    exact fun he => hx1 (Point.some.inj he).1

  have hy : kleinY u ≠ (kleinCurve u).toAffine.negY (kleinX u) (kleinY u) := by
    intro he
    have h2 : Point.some _ _ hnsQ + Point.some _ _ hnsQ = 0 := add_self_of_Y_eq he
    apply hQ0
    have e : Point.some _ _ hnsQ
        = (5 : ℤ) • Point.some _ _ hnsQ - (2 : ℤ) • (Point.some _ _ hnsQ + Point.some _ _ hnsQ) := by
      rw [← two_zsmul, ← mul_zsmul]
      norm_num
      abel
    rw [e, hQ5, h2, zsmul_zero, sub_zero]

  have h2Q : Point.some _ _ hnsQ + Point.some _ _ hnsQ
      = Point.some _ _ (nonsingular_add hnsQ hnsQ fun hxy => hy hxy.right) := add_self_of_Y_ne hy
  have hy0 : (2 : K) * kleinY u ≠ 0 := by
    intro h0
    apply hy
    show kleinY u = -kleinY u - 0 * kleinX u - 0
    linear_combination h0
  have hL : (kleinCurve u).toAffine.slope (kleinX u) (kleinX u) (kleinY u) (kleinY u)
      = (3 * kleinX u ^ 2 + (-kleinH u / 48)) / (2 * kleinY u) := by
    rw [slope_of_Y_ne rfl hy]
    show (3 * kleinX u ^ 2 + 2 * 0 * kleinX u + (-kleinH u / 48) - 0 * kleinY u)
        / (kleinY u - (-kleinY u - 0 * kleinX u - 0)) = _
    congr 1 <;> ring
  have hx2 : kleinX (ζ * u) ≠ (kleinCurve u).toAffine.addX (kleinX u) (kleinX u)
      ((kleinCurve u).toAffine.slope (kleinX u) (kleinX u) (kleinY u) (kleinY u)) := by
    intro he
    have he' : kleinX (ζ * u) = ((3 * kleinX u ^ 2 + (-kleinH u / 48)) / (2 * kleinY u)) ^ 2
        - 2 * kleinX u := by
      rw [he, hL]
      show _ ^ 2 + 0 * _ - 0 - kleinX u - kleinX u = _
      ring

    have key : (kleinX (ζ * u) + 2 * kleinX u) * (2 * kleinY u) ^ 2
        = (3 * kleinX u ^ 2 + (-kleinH u / 48)) ^ 2 := by
      rw [he', div_pow, sub_add_cancel, div_mul_cancel₀ _ (pow_ne_zero 2 hy0)]

    have hyeq : kleinY u ^ 2 = kleinX u ^ 3 + (-kleinH u / 48) * kleinX u + kleinT u / 864 := by
      have heq : kleinY u ^ 2 + 0 * kleinX u * kleinY u + 0 * kleinY u
          = kleinX u ^ 3 + 0 * kleinX u ^ 2 + (-kleinH u / 48) * kleinX u + kleinT u / 864 :=
        (WeierstrassCurve.Affine.equation_iff ..).mp hnsQ.left
      linear_combination heq

    have hN2 : 4 * (kleinX u ^ 3 + (-kleinH u / 48) * kleinX u + kleinT u / 864) * kleinX (ζ * u)
        - ((3 * kleinX u ^ 2 + (-kleinH u / 48)) ^ 2
          - 8 * kleinX u * (kleinX u ^ 3 + (-kleinH u / 48) * kleinX u + kleinT u / 864)) = 0 := by
      linear_combination key - (4 * (kleinX (ζ * u) + 2 * kleinX u)) * hyeq

    have hM2 : 4 * ((12 * kleinX u) ^ 3 - 3 * kleinH u * (12 * kleinX u) + 2 * kleinT u)
          * (12 * kleinX (ζ * u))
        - 9 * ((12 * kleinX u) ^ 2 - kleinH u) ^ 2
        + 8 * (12 * kleinX u) * ((12 * kleinX u) ^ 3 - 3 * kleinH u * (12 * kleinX u)
          + 2 * kleinT u) = 0 := by
      linear_combination (20736 : K) * hN2
    rw [hX, hXR] at hM2
    have c2 := cert_x_ne_double ζ u hΦ
    rw [hM2, zero_mul] at c2
    have : kleinV u ^ 5 = 0 := (mul_eq_zero.mp c2).resolve_left (by norm_num)
    exact hV (pow_eq_zero_iff (by norm_num) |>.mp this)
  have h2 : Point.some _ _ hnsR ≠ (2 : ℤ) • Point.some _ _ hnsQ := by
    rw [two_zsmul, h2Q]
    exact fun he => hx2 (Point.some.inj he).1
  have h2' : Point.some _ _ hnsR ≠ -((2 : ℤ) • Point.some _ _ hnsQ) := by
    rw [two_zsmul, h2Q, neg_some]
    exact fun he => hx2 (Point.some.inj he).1
  exact indep_of_five_smul hQ0 hQ5 hR0 hR5 h1 h1' h2 h2' h

end Indep

end M4cP4RS

theorem solution {K : Type*} [Field K] [CharZero K] [DecidableEq K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5)
    (u : K) (hV : kleinV u ≠ 0) (i j : ℤ)
    (h : i • pt (kleinCurve u) (kleinX u) (kleinY u)
      + j • pt (kleinCurve u) (kleinX (ζ * u)) (kleinY (ζ * u)) = 0) :
    (5 : ℤ) ∣ i ∧ (5 : ℤ) ∣ j :=
  M4cP4RS.main ζ hζ u hV i j h

end S_RubinSilverberg_kleinSection_independent
end P2MW
export P2MW.S_RubinSilverberg_kleinSection_independent (solution)
