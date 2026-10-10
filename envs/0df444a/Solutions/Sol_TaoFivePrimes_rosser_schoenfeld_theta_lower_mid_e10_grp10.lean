-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:54:34.409056+00:00
-- url     : https://prove2.me/submissions/c0d2be59-eb50-40e5-8e2e-c8eb39e9f954

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0451
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0452
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0453
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0454
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0455
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0456
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0457
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0458
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0459
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0460
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0461
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0462
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0463
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0464
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0465
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0466
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0467
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0468
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0469
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0470
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0471
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0472
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0473
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0474
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0475
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0476
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0477
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0478
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0479
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0480
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0481
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0482
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0483
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0484
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0485
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0486
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0487
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0488
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0489
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0490
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0491
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0492
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0493
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0494
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0495
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0496
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0497
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0498
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0499
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0500

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp10` (the range 3907634390 <= n <= 4239430051 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0451` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0500`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (4296440043854818217785 : Real) / 2 ^ 40 <= Chebyshev.theta (3907634390 : Real))
    (n : Nat) (h1 : 3907634390 <= n) (h2 : n <= 4239430051) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((4661206139401073931926 : Real) / 2 ^ 40 <= Chebyshev.theta (4239430052 : Real)) := by
  have hb0 := hbase
  have hb1 : (4303722035789512595801 : Real) / 2 ^ 40 <= Chebyshev.theta (3914264202 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0451 hb0 3907634390 le_rfl (by norm_num)).2
  have hb2 : (4311004586654072757959 : Real) / 2 ^ 40 <= Chebyshev.theta (3920894532 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0452 hb1 3914264202 le_rfl (by norm_num)).2
  have hb3 : (4318287694850756149888 : Real) / 2 ^ 40 <= Chebyshev.theta (3927525654 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0453 hb2 3920894532 le_rfl (by norm_num)).2
  have hb4 : (4325571359203258075102 : Real) / 2 ^ 40 <= Chebyshev.theta (3934148420 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0454 hb3 3927525654 le_rfl (by norm_num)).2
  have hb5 : (4332855578712407983121 : Real) / 2 ^ 40 <= Chebyshev.theta (3940771202 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0455 hb4 3934148420 le_rfl (by norm_num)).2
  have hb6 : (4340140352390385305510 : Real) / 2 ^ 40 <= Chebyshev.theta (3947396400 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0456 hb5 3940771202 le_rfl (by norm_num)).2
  have hb7 : (4347425678981435471470 : Real) / 2 ^ 40 <= Chebyshev.theta (3954015758 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0457 hb6 3947396400 le_rfl (by norm_num)).2
  have hb8 : (4354711557897964328597 : Real) / 2 ^ 40 <= Chebyshev.theta (3960645192 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0458 hb7 3954015758 le_rfl (by norm_num)).2
  have hb9 : (4361997988187131580986 : Real) / 2 ^ 40 <= Chebyshev.theta (3967263920 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0459 hb8 3960645192 le_rfl (by norm_num)).2
  have hb10 : (4369284969483691085137 : Real) / 2 ^ 40 <= Chebyshev.theta (3973897440 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0460 hb9 3967263920 le_rfl (by norm_num)).2
  have hb11 : (4376572500851548420294 : Real) / 2 ^ 40 <= Chebyshev.theta (3980530650 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0461 hb10 3973897440 le_rfl (by norm_num)).2
  have hb12 : (4383860581413777924556 : Real) / 2 ^ 40 <= Chebyshev.theta (3987158742 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0462 hb11 3980530650 le_rfl (by norm_num)).2
  have hb13 : (4391149210545014193795 : Real) / 2 ^ 40 <= Chebyshev.theta (3993795428 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0463 hb12 3987158742 le_rfl (by norm_num)).2
  have hb14 : (4398438386914146219048 : Real) / 2 ^ 40 <= Chebyshev.theta (4000420314 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0464 hb13 3993795428 le_rfl (by norm_num)).2
  have hb15 : (4405728109327379167564 : Real) / 2 ^ 40 <= Chebyshev.theta (4007051292 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0465 hb14 4000420314 le_rfl (by norm_num)).2
  have hb16 : (4413018377656327996543 : Real) / 2 ^ 40 <= Chebyshev.theta (4013685582 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0466 hb15 4007051292 le_rfl (by norm_num)).2
  have hb17 : (4420309191278418281049 : Real) / 2 ^ 40 <= Chebyshev.theta (4020321984 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0467 hb16 4013685582 le_rfl (by norm_num)).2
  have hb18 : (4427600548400724988602 : Real) / 2 ^ 40 <= Chebyshev.theta (4026951222 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0468 hb17 4020321984 le_rfl (by norm_num)).2
  have hb19 : (4434892448837927100900 : Real) / 2 ^ 40 <= Chebyshev.theta (4033585352 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0469 hb18 4026951222 le_rfl (by norm_num)).2
  have hb20 : (4442184891405160918603 : Real) / 2 ^ 40 <= Chebyshev.theta (4040219784 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0470 hb19 4033585352 le_rfl (by norm_num)).2
  have hb21 : (4449477875505529025336 : Real) / 2 ^ 40 <= Chebyshev.theta (4046855648 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0471 hb20 4040219784 le_rfl (by norm_num)).2
  have hb22 : (4456771400154001831854 : Real) / 2 ^ 40 <= Chebyshev.theta (4053489002 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0472 hb21 4046855648 le_rfl (by norm_num)).2
  have hb23 : (4464065463998256887341 : Real) / 2 ^ 40 <= Chebyshev.theta (4060117730 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0473 hb22 4053489002 le_rfl (by norm_num)).2
  have hb24 : (4471360066233189727751 : Real) / 2 ^ 40 <= Chebyshev.theta (4066746420 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0474 hb23 4060117730 le_rfl (by norm_num)).2
  have hb25 : (4478655206617659750957 : Real) / 2 ^ 40 <= Chebyshev.theta (4073395172 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0475 hb24 4066746420 le_rfl (by norm_num)).2
  have hb26 : (4485950884669013622146 : Real) / 2 ^ 40 <= Chebyshev.theta (4080032322 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0476 hb25 4073395172 le_rfl (by norm_num)).2
  have hb27 : (4493247099193642573845 : Real) / 2 ^ 40 <= Chebyshev.theta (4086666954 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0477 hb26 4080032322 le_rfl (by norm_num)).2
  have hb28 : (4500543849001659144171 : Real) / 2 ^ 40 <= Chebyshev.theta (4093302378 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0478 hb27 4086666954 le_rfl (by norm_num)).2
  have hb29 : (4507841133266933492503 : Real) / 2 ^ 40 <= Chebyshev.theta (4099944732 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0479 hb28 4093302378 le_rfl (by norm_num)).2
  have hb30 : (4515138951662921053461 : Real) / 2 ^ 40 <= Chebyshev.theta (4106582352 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0480 hb29 4099944732 le_rfl (by norm_num)).2
  have hb31 : (4522437302719147923797 : Real) / 2 ^ 40 <= Chebyshev.theta (4113222168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0481 hb30 4106582352 le_rfl (by norm_num)).2
  have hb32 : (4529736185582876927935 : Real) / 2 ^ 40 <= Chebyshev.theta (4119846800 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0482 hb31 4113222168 le_rfl (by norm_num)).2
  have hb33 : (4537035598983840403281 : Real) / 2 ^ 40 <= Chebyshev.theta (4126482258 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0483 hb32 4119846800 le_rfl (by norm_num)).2
  have hb34 : (4544335542516602105981 : Real) / 2 ^ 40 <= Chebyshev.theta (4133113124 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0484 hb33 4126482258 le_rfl (by norm_num)).2
  have hb35 : (4551636015297910154633 : Real) / 2 ^ 40 <= Chebyshev.theta (4139759784 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0485 hb34 4133113124 le_rfl (by norm_num)).2
  have hb36 : (4558937017559974017952 : Real) / 2 ^ 40 <= Chebyshev.theta (4146400178 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0486 hb35 4139759784 le_rfl (by norm_num)).2
  have hb37 : (4566238547734449455716 : Real) / 2 ^ 40 <= Chebyshev.theta (4153040678 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0487 hb36 4146400178 le_rfl (by norm_num)).2
  have hb38 : (4573540605170666185797 : Real) / 2 ^ 40 <= Chebyshev.theta (4159683768 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0488 hb37 4153040678 le_rfl (by norm_num)).2
  have hb39 : (4580843189412950338898 : Real) / 2 ^ 40 <= Chebyshev.theta (4166337398 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0489 hb38 4159683768 le_rfl (by norm_num)).2
  have hb40 : (4588146299828307834436 : Real) / 2 ^ 40 <= Chebyshev.theta (4172983590 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0490 hb39 4166337398 le_rfl (by norm_num)).2
  have hb41 : (4595449935517113046420 : Real) / 2 ^ 40 <= Chebyshev.theta (4179632544 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0491 hb40 4172983590 le_rfl (by norm_num)).2
  have hb42 : (4602754095446889739354 : Real) / 2 ^ 40 <= Chebyshev.theta (4186274840 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0492 hb41 4179632544 le_rfl (by norm_num)).2
  have hb43 : (4610058778509433109019 : Real) / 2 ^ 40 <= Chebyshev.theta (4192922880 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0493 hb42 4186274840 le_rfl (by norm_num)).2
  have hb44 : (4617363984194180028690 : Real) / 2 ^ 40 <= Chebyshev.theta (4199562668 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0494 hb43 4192922880 le_rfl (by norm_num)).2
  have hb45 : (4624669710862453582524 : Real) / 2 ^ 40 <= Chebyshev.theta (4206196122 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0495 hb44 4199562668 le_rfl (by norm_num)).2
  have hb46 : (4631975958042392221914 : Real) / 2 ^ 40 <= Chebyshev.theta (4212843530 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0496 hb45 4206196122 le_rfl (by norm_num)).2
  have hb47 : (4639282725165566518236 : Real) / 2 ^ 40 <= Chebyshev.theta (4219486022 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0497 hb46 4212843530 le_rfl (by norm_num)).2
  have hb48 : (4646590011486971092696 : Real) / 2 ^ 40 <= Chebyshev.theta (4226131800 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0498 hb47 4219486022 le_rfl (by norm_num)).2
  have hb49 : (4653897816604891007029 : Real) / 2 ^ 40 <= Chebyshev.theta (4232783942 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0499 hb48 4226131800 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0500 hb49 4232783942 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 4073395172 with hc25 | hc25
  · rcases Nat.lt_or_ge n 3987158742 with hc12 | hc12
    · rcases Nat.lt_or_ge n 3947396400 with hc6 | hc6
      · rcases Nat.lt_or_ge n 3927525654 with hc3 | hc3
        · rcases Nat.lt_or_ge n 3914264202 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0451 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3920894532 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0452 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0453 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3934148420 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0454 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3940771202 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0455 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0456 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3967263920 with hc9 | hc9
        · rcases Nat.lt_or_ge n 3954015758 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0457 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3960645192 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0458 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0459 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3973897440 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0460 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3980530650 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0461 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0462 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 4026951222 with hc18 | hc18
      · rcases Nat.lt_or_ge n 4007051292 with hc15 | hc15
        · rcases Nat.lt_or_ge n 3993795428 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0463 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4000420314 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0464 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0465 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4013685582 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0466 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4020321984 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0467 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0468 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4046855648 with hc21 | hc21
        · rcases Nat.lt_or_ge n 4033585352 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0469 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4040219784 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0470 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0471 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4060117730 with hc23 | hc23
          · rcases Nat.lt_or_ge n 4053489002 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0472 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0473 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4066746420 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0474 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0475 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 4153040678 with hc37 | hc37
    · rcases Nat.lt_or_ge n 4113222168 with hc31 | hc31
      · rcases Nat.lt_or_ge n 4093302378 with hc28 | hc28
        · rcases Nat.lt_or_ge n 4080032322 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0476 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4086666954 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0477 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0478 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4099944732 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0479 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4106582352 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0480 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0481 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4133113124 with hc34 | hc34
        · rcases Nat.lt_or_ge n 4119846800 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0482 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4126482258 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0483 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0484 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4139759784 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0485 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4146400178 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0486 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0487 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 4192922880 with hc43 | hc43
      · rcases Nat.lt_or_ge n 4172983590 with hc40 | hc40
        · rcases Nat.lt_or_ge n 4159683768 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0488 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4166337398 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0489 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0490 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4179632544 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0491 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4186274840 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0492 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0493 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4212843530 with hc46 | hc46
        · rcases Nat.lt_or_ge n 4199562668 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0494 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4206196122 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0495 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0496 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4226131800 with hc48 | hc48
          · rcases Nat.lt_or_ge n 4219486022 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0497 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0498 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4232783942 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0499 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0500 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (4296440043854818217785 : Real) / 2 ^ 40 <= Chebyshev.theta (3907634390 : Real))
    (n : Nat) (h1 : 3907634390 <= n) (h2 : n <= 4239430051) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((4661206139401073931926 : Real) / 2 ^ 40 <= Chebyshev.theta (4239430052 : Real)) :=
  TFPLink.blk hbase n h1 h2
