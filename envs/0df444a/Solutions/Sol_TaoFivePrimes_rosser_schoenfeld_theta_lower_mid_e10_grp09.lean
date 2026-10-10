-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp09
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:51:20.870385+00:00
-- url     : https://prove2.me/submissions/b1a13461-228e-4ef1-80d4-28d394751b1f

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0401
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0402
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0403
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0404
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0405
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0406
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0407
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0408
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0409
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0410
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0411
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0412
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0413
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0414
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0415
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0416
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0417
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0418
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0419
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0420
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0421
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0422
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0423
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0424
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0425
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0426
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0427
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0428
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0429
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0430
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0431
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0432
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0433
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0434
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0435
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0436
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0437
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0438
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0439
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0440
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0441
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0442
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0443
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0444
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0445
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0446
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0447
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0448
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0449
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0450

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp09` (the range 3577176104 <= n <= 3907634389 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0401` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0450`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (3933072480233213816578 : Real) / 2 ^ 40 <= Chebyshev.theta (3577176104 : Real))
    (n : Nat) (h1 : 3577176104 <= n) (h2 : n <= 3907634389) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((4296440043854818217785 : Real) / 2 ^ 40 <= Chebyshev.theta (3907634390 : Real)) := by
  have hb0 := hbase
  have hb1 : (3940325364704120373684 : Real) / 2 ^ 40 <= Chebyshev.theta (3583764452 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0401 hb0 3577176104 le_rfl (by norm_num)).2
  have hb2 : (3947578856095965974343 : Real) / 2 ^ 40 <= Chebyshev.theta (3590366702 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0402 hb1 3583764452 le_rfl (by norm_num)).2
  have hb3 : (3954832954130583025823 : Real) / 2 ^ 40 <= Chebyshev.theta (3596968058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0403 hb2 3590366702 le_rfl (by norm_num)).2
  have hb4 : (3962087656871590165212 : Real) / 2 ^ 40 <= Chebyshev.theta (3603571062 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0404 hb3 3596968058 le_rfl (by norm_num)).2
  have hb5 : (3969342963196269496495 : Real) / 2 ^ 40 <= Chebyshev.theta (3610167750 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0405 hb4 3603571062 le_rfl (by norm_num)).2
  have hb6 : (3976598872832035385324 : Real) / 2 ^ 40 <= Chebyshev.theta (3616774590 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0406 hb5 3610167750 le_rfl (by norm_num)).2
  have hb7 : (3983855383770871336209 : Real) / 2 ^ 40 <= Chebyshev.theta (3623366108 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0407 hb6 3616774590 le_rfl (by norm_num)).2
  have hb8 : (3991112494821587430310 : Real) / 2 ^ 40 <= Chebyshev.theta (3629960600 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0408 hb7 3623366108 le_rfl (by norm_num)).2
  have hb9 : (3998370205005294232605 : Real) / 2 ^ 40 <= Chebyshev.theta (3636565838 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0409 hb8 3629960600 le_rfl (by norm_num)).2
  have hb10 : (4005628513495117641355 : Real) / 2 ^ 40 <= Chebyshev.theta (3643156020 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0410 hb9 3636565838 le_rfl (by norm_num)).2
  have hb11 : (4012887418613120966761 : Real) / 2 ^ 40 <= Chebyshev.theta (3649751508 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0411 hb10 3643156020 le_rfl (by norm_num)).2
  have hb12 : (4020146919862882043332 : Real) / 2 ^ 40 <= Chebyshev.theta (3656354532 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0412 hb11 3649751508 le_rfl (by norm_num)).2
  have hb13 : (4027407017070057704253 : Real) / 2 ^ 40 <= Chebyshev.theta (3662966258 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0413 hb12 3656354532 le_rfl (by norm_num)).2
  have hb14 : (4034667708654953727258 : Real) / 2 ^ 40 <= Chebyshev.theta (3669561804 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0414 hb13 3662966258 le_rfl (by norm_num)).2
  have hb15 : (4041928993013873469034 : Real) / 2 ^ 40 <= Chebyshev.theta (3676164162 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0415 hb14 3669561804 le_rfl (by norm_num)).2
  have hb16 : (4049190869317151848653 : Real) / 2 ^ 40 <= Chebyshev.theta (3682765772 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0416 hb15 3676164162 le_rfl (by norm_num)).2
  have hb17 : (4056453337511388130921 : Real) / 2 ^ 40 <= Chebyshev.theta (3689380944 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0417 hb16 3682765772 le_rfl (by norm_num)).2
  have hb18 : (4063716396167973100459 : Real) / 2 ^ 40 <= Chebyshev.theta (3695982128 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0418 hb17 3689380944 le_rfl (by norm_num)).2
  have hb19 : (4070980044150233965297 : Real) / 2 ^ 40 <= Chebyshev.theta (3702595124 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0419 hb18 3695982128 le_rfl (by norm_num)).2
  have hb20 : (4078244280617527793021 : Real) / 2 ^ 40 <= Chebyshev.theta (3709204440 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0420 hb19 3702595124 le_rfl (by norm_num)).2
  have hb21 : (4085509104578870905445 : Real) / 2 ^ 40 <= Chebyshev.theta (3715808210 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0421 hb20 3709204440 le_rfl (by norm_num)).2
  have hb22 : (4092774514224592394940 : Real) / 2 ^ 40 <= Chebyshev.theta (3722401920 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0422 hb21 3715808210 le_rfl (by norm_num)).2
  have hb23 : (4100040508428625190463 : Real) / 2 ^ 40 <= Chebyshev.theta (3729012998 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0423 hb22 3722401920 le_rfl (by norm_num)).2
  have hb24 : (4107307086556300623916 : Real) / 2 ^ 40 <= Chebyshev.theta (3735614480 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0424 hb23 3729012998 le_rfl (by norm_num)).2
  have hb25 : (4114574247657941509144 : Real) / 2 ^ 40 <= Chebyshev.theta (3742223568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0425 hb24 3735614480 le_rfl (by norm_num)).2
  have hb26 : (4121841991026313719077 : Real) / 2 ^ 40 <= Chebyshev.theta (3748834082 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0426 hb25 3742223568 le_rfl (by norm_num)).2
  have hb27 : (4129110315966277369805 : Real) / 2 ^ 40 <= Chebyshev.theta (3755448980 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0427 hb26 3748834082 le_rfl (by norm_num)).2
  have hb28 : (4136379221442379181361 : Real) / 2 ^ 40 <= Chebyshev.theta (3762056984 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0428 hb27 3755448980 le_rfl (by norm_num)).2
  have hb29 : (4143648706250032534787 : Real) / 2 ^ 40 <= Chebyshev.theta (3768665544 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0429 hb28 3762056984 le_rfl (by norm_num)).2
  have hb30 : (4150918769335177622175 : Real) / 2 ^ 40 <= Chebyshev.theta (3775283592 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0430 hb29 3768665544 le_rfl (by norm_num)).2
  have hb31 : (4158189409924527142260 : Real) / 2 ^ 40 <= Chebyshev.theta (3781892034 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0431 hb30 3775283592 le_rfl (by norm_num)).2
  have hb32 : (4165460627104686638375 : Real) / 2 ^ 40 <= Chebyshev.theta (3788508392 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0432 hb31 3781892034 le_rfl (by norm_num)).2
  have hb33 : (4172732420167863787609 : Real) / 2 ^ 40 <= Chebyshev.theta (3795123552 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0433 hb32 3788508392 le_rfl (by norm_num)).2
  have hb34 : (4180004787682658395393 : Real) / 2 ^ 40 <= Chebyshev.theta (3801739442 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0434 hb33 3795123552 le_rfl (by norm_num)).2
  have hb35 : (4187277728593150001024 : Real) / 2 ^ 40 <= Chebyshev.theta (3808347528 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0435 hb34 3801739442 le_rfl (by norm_num)).2
  have hb36 : (4194551242303557579803 : Real) / 2 ^ 40 <= Chebyshev.theta (3814966950 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0436 hb35 3808347528 le_rfl (by norm_num)).2
  have hb37 : (4201825327242745912316 : Real) / 2 ^ 40 <= Chebyshev.theta (3821576744 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0437 hb36 3814966950 le_rfl (by norm_num)).2
  have hb38 : (4209099983119150705714 : Real) / 2 ^ 40 <= Chebyshev.theta (3828197732 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0438 hb37 3821576744 le_rfl (by norm_num)).2
  have hb39 : (4216375208953510394414 : Real) / 2 ^ 40 <= Chebyshev.theta (3834809802 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0439 hb38 3828197732 le_rfl (by norm_num)).2
  have hb40 : (4223651003573799783357 : Real) / 2 ^ 40 <= Chebyshev.theta (3841427820 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0440 hb39 3834809802 le_rfl (by norm_num)).2
  have hb41 : (4230927366590584242719 : Real) / 2 ^ 40 <= Chebyshev.theta (3848059212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0441 hb40 3841427820 le_rfl (by norm_num)).2
  have hb42 : (4238204297273557550781 : Real) / 2 ^ 40 <= Chebyshev.theta (3854678424 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0442 hb41 3848059212 le_rfl (by norm_num)).2
  have hb43 : (4245481794383338881333 : Real) / 2 ^ 40 <= Chebyshev.theta (3861298742 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0443 hb42 3854678424 le_rfl (by norm_num)).2
  have hb44 : (4252759856401263423757 : Real) / 2 ^ 40 <= Chebyshev.theta (3867915378 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0444 hb43 3861298742 le_rfl (by norm_num)).2
  have hb45 : (4260038482410587546357 : Real) / 2 ^ 40 <= Chebyshev.theta (3874534998 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0445 hb44 3867915378 le_rfl (by norm_num)).2
  have hb46 : (4267317671823903162007 : Real) / 2 ^ 40 <= Chebyshev.theta (3881153180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0446 hb45 3874534998 le_rfl (by norm_num)).2
  have hb47 : (4274597423189342895400 : Real) / 2 ^ 40 <= Chebyshev.theta (3887772194 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0447 hb46 3881153180 le_rfl (by norm_num)).2
  have hb48 : (4281877736299630025264 : Real) / 2 ^ 40 <= Chebyshev.theta (3894395384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0448 hb47 3887772194 le_rfl (by norm_num)).2
  have hb49 : (4289158610379988728099 : Real) / 2 ^ 40 <= Chebyshev.theta (3901023048 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0449 hb48 3894395384 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0450 hb49 3901023048 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 3742223568 with hc25 | hc25
  · rcases Nat.lt_or_ge n 3656354532 with hc12 | hc12
    · rcases Nat.lt_or_ge n 3616774590 with hc6 | hc6
      · rcases Nat.lt_or_ge n 3596968058 with hc3 | hc3
        · rcases Nat.lt_or_ge n 3583764452 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0401 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3590366702 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0402 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0403 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3603571062 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0404 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3610167750 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0405 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0406 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3636565838 with hc9 | hc9
        · rcases Nat.lt_or_ge n 3623366108 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0407 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3629960600 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0408 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0409 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3643156020 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0410 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3649751508 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0411 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0412 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 3695982128 with hc18 | hc18
      · rcases Nat.lt_or_ge n 3676164162 with hc15 | hc15
        · rcases Nat.lt_or_ge n 3662966258 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0413 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3669561804 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0414 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0415 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3682765772 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0416 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3689380944 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0417 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0418 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3715808210 with hc21 | hc21
        · rcases Nat.lt_or_ge n 3702595124 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0419 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3709204440 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0420 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0421 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3729012998 with hc23 | hc23
          · rcases Nat.lt_or_ge n 3722401920 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0422 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0423 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3735614480 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0424 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0425 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 3821576744 with hc37 | hc37
    · rcases Nat.lt_or_ge n 3781892034 with hc31 | hc31
      · rcases Nat.lt_or_ge n 3762056984 with hc28 | hc28
        · rcases Nat.lt_or_ge n 3748834082 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0426 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3755448980 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0427 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0428 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3768665544 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0429 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3775283592 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0430 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0431 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3801739442 with hc34 | hc34
        · rcases Nat.lt_or_ge n 3788508392 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0432 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3795123552 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0433 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0434 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3808347528 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0435 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3814966950 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0436 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0437 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 3861298742 with hc43 | hc43
      · rcases Nat.lt_or_ge n 3841427820 with hc40 | hc40
        · rcases Nat.lt_or_ge n 3828197732 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0438 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3834809802 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0439 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0440 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3848059212 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0441 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3854678424 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0442 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0443 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3881153180 with hc46 | hc46
        · rcases Nat.lt_or_ge n 3867915378 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0444 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3874534998 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0445 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0446 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3894395384 with hc48 | hc48
          · rcases Nat.lt_or_ge n 3887772194 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0447 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0448 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3901023048 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0449 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0450 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (3933072480233213816578 : Real) / 2 ^ 40 <= Chebyshev.theta (3577176104 : Real))
    (n : Nat) (h1 : 3577176104 <= n) (h2 : n <= 3907634389) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((4296440043854818217785 : Real) / 2 ^ 40 <= Chebyshev.theta (3907634390 : Real)) :=
  TFPLink.blk hbase n h1 h2
