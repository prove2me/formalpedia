-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:58:07.399485+00:00
-- url     : https://prove2.me/submissions/7573b09d-d29c-4063-9be8-59f31d3d4f9c

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0501
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0502
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0503
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0504
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0505
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0506
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0507
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0508
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0509
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0510
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0511
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0512
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0513
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0514
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0515
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0516
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0517
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0518
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0519
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0520
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0521
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0522
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0523
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0524
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0525
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0526
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0527
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0528
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0529
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0530
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0531
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0532
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0533
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0534
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0535
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0536
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0537
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0538
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0539
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0540
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0541
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0542
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0543
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0544
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0545
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0546
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0547
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0548
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0549
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0550

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp11` (the range 4239430052 <= n <= 4572345229 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0501` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0550`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (4661206139401073931926 : Real) / 2 ^ 40 <= Chebyshev.theta (4239430052 : Real))
    (n : Nat) (h1 : 4239430052 <= n) (h2 : n <= 4572345229) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((5027265814990202898813 : Real) / 2 ^ 40 <= Chebyshev.theta (4572345230 : Real)) := by
  have hb0 := hbase
  have hb1 : (4668514979402169796546 : Real) / 2 ^ 40 <= Chebyshev.theta (4246077762 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0501 hb0 4239430052 le_rfl (by norm_num)).2
  have hb2 : (4675824335387590367901 : Real) / 2 ^ 40 <= Chebyshev.theta (4252725630 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0502 hb1 4246077762 le_rfl (by norm_num)).2
  have hb3 : (4683134207051258261346 : Real) / 2 ^ 40 <= Chebyshev.theta (4259378772 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0503 hb2 4252725630 le_rfl (by norm_num)).2
  have hb4 : (4690444593588627208674 : Real) / 2 ^ 40 <= Chebyshev.theta (4266027644 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0504 hb3 4259378772 le_rfl (by norm_num)).2
  have hb5 : (4697755494057648700187 : Real) / 2 ^ 40 <= Chebyshev.theta (4272676394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0505 hb4 4266027644 le_rfl (by norm_num)).2
  have hb6 : (4705066907017991407903 : Real) / 2 ^ 40 <= Chebyshev.theta (4279313808 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0506 hb5 4272676394 le_rfl (by norm_num)).2
  have hb7 : (4712378831759258095000 : Real) / 2 ^ 40 <= Chebyshev.theta (4285956600 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0507 hb6 4279313808 le_rfl (by norm_num)).2
  have hb8 : (4719691268164227635445 : Real) / 2 ^ 40 <= Chebyshev.theta (4292617410 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0508 hb7 4285956600 le_rfl (by norm_num)).2
  have hb9 : (4727004215745595062439 : Real) / 2 ^ 40 <= Chebyshev.theta (4299270840 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0509 hb8 4292617410 le_rfl (by norm_num)).2
  have hb10 : (4734317673647832221214 : Real) / 2 ^ 40 <= Chebyshev.theta (4305926748 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0510 hb9 4299270840 le_rfl (by norm_num)).2
  have hb11 : (4741631641249667143790 : Real) / 2 ^ 40 <= Chebyshev.theta (4312581788 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0511 hb10 4305926748 le_rfl (by norm_num)).2
  have hb12 : (4748946117325487834634 : Real) / 2 ^ 40 <= Chebyshev.theta (4319228430 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0512 hb11 4312581788 le_rfl (by norm_num)).2
  have hb13 : (4756261101166943774999 : Real) / 2 ^ 40 <= Chebyshev.theta (4325883042 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0513 hb12 4319228430 le_rfl (by norm_num)).2
  have hb14 : (4763576591713462872196 : Real) / 2 ^ 40 <= Chebyshev.theta (4332529632 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0514 hb13 4325883042 le_rfl (by norm_num)).2
  have hb15 : (4770892588001413044115 : Real) / 2 ^ 40 <= Chebyshev.theta (4339176422 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0515 hb14 4332529632 le_rfl (by norm_num)).2
  have hb16 : (4778209089577539270091 : Real) / 2 ^ 40 <= Chebyshev.theta (4345835574 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0516 hb15 4339176422 le_rfl (by norm_num)).2
  have hb17 : (4785526096478310344890 : Real) / 2 ^ 40 <= Chebyshev.theta (4352489334 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0517 hb16 4345835574 le_rfl (by norm_num)).2
  have hb18 : (4792843606923267609753 : Real) / 2 ^ 40 <= Chebyshev.theta (4359137198 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0518 hb17 4352489334 le_rfl (by norm_num)).2
  have hb19 : (4800161620055580452955 : Real) / 2 ^ 40 <= Chebyshev.theta (4365785814 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0519 hb18 4359137198 le_rfl (by norm_num)).2
  have hb20 : (4807480135874504613379 : Real) / 2 ^ 40 <= Chebyshev.theta (4372441968 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0520 hb19 4365785814 le_rfl (by norm_num)).2
  have hb21 : (4814799153527302915447 : Real) / 2 ^ 40 <= Chebyshev.theta (4379096274 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0521 hb20 4372441968 le_rfl (by norm_num)).2
  have hb22 : (4822118672118071038757 : Real) / 2 ^ 40 <= Chebyshev.theta (4385753610 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0522 hb21 4379096274 le_rfl (by norm_num)).2
  have hb23 : (4829438691428182279992 : Real) / 2 ^ 40 <= Chebyshev.theta (4392414558 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0523 hb22 4385753610 le_rfl (by norm_num)).2
  have hb24 : (4836759210900929323131 : Real) / 2 ^ 40 <= Chebyshev.theta (4399082550 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0524 hb23 4392414558 le_rfl (by norm_num)).2
  have hb25 : (4844080229587937438975 : Real) / 2 ^ 40 <= Chebyshev.theta (4405738092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0525 hb24 4399082550 le_rfl (by norm_num)).2
  have hb26 : (4851401746379699366349 : Real) / 2 ^ 40 <= Chebyshev.theta (4412390322 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0526 hb25 4405738092 le_rfl (by norm_num)).2
  have hb27 : (4858723760388497657145 : Real) / 2 ^ 40 <= Chebyshev.theta (4419049430 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0527 hb26 4412390322 le_rfl (by norm_num)).2
  have hb28 : (4866046271470131719814 : Real) / 2 ^ 40 <= Chebyshev.theta (4425715368 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0528 hb27 4419049430 le_rfl (by norm_num)).2
  have hb29 : (4873369278675110433481 : Real) / 2 ^ 40 <= Chebyshev.theta (4432368290 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0529 hb28 4425715368 le_rfl (by norm_num)).2
  have hb30 : (4880692781118321263949 : Real) / 2 ^ 40 <= Chebyshev.theta (4439035568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0530 hb29 4432368290 le_rfl (by norm_num)).2
  have hb31 : (4888016779016902392301 : Real) / 2 ^ 40 <= Chebyshev.theta (4445701238 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0531 hb30 4439035568 le_rfl (by norm_num)).2
  have hb32 : (4895341271181338487212 : Real) / 2 ^ 40 <= Chebyshev.theta (4452369672 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0532 hb31 4445701238 le_rfl (by norm_num)).2
  have hb33 : (4902666256730052254794 : Real) / 2 ^ 40 <= Chebyshev.theta (4459028220 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0533 hb32 4452369672 le_rfl (by norm_num)).2
  have hb34 : (4909991734778675421969 : Real) / 2 ^ 40 <= Chebyshev.theta (4465691552 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0534 hb33 4459028220 le_rfl (by norm_num)).2
  have hb35 : (4917317704925865181031 : Real) / 2 ^ 40 <= Chebyshev.theta (4472356998 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0535 hb34 4465691552 le_rfl (by norm_num)).2
  have hb36 : (4924644166847681880511 : Real) / 2 ^ 40 <= Chebyshev.theta (4479029432 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0536 hb35 4472356998 le_rfl (by norm_num)).2
  have hb37 : (4931971119315164349847 : Real) / 2 ^ 40 <= Chebyshev.theta (4485697262 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0537 hb36 4479029432 le_rfl (by norm_num)).2
  have hb38 : (4939298561821470767901 : Real) / 2 ^ 40 <= Chebyshev.theta (4492357614 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0538 hb37 4485697262 le_rfl (by norm_num)).2
  have hb39 : (4946626493243883238660 : Real) / 2 ^ 40 <= Chebyshev.theta (4499012732 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0539 hb38 4492357614 le_rfl (by norm_num)).2
  have hb40 : (4953954912263943192161 : Real) / 2 ^ 40 <= Chebyshev.theta (4505676620 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0540 hb39 4499012732 le_rfl (by norm_num)).2
  have hb41 : (4961283819170051811504 : Real) / 2 ^ 40 <= Chebyshev.theta (4512343064 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0541 hb40 4505676620 le_rfl (by norm_num)).2
  have hb42 : (4968613213164361178540 : Real) / 2 ^ 40 <= Chebyshev.theta (4519009934 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0542 hb41 4512343064 le_rfl (by norm_num)).2
  have hb43 : (4975943093611644429333 : Real) / 2 ^ 40 <= Chebyshev.theta (4525673444 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0543 hb42 4519009934 le_rfl (by norm_num)).2
  have hb44 : (4983273459566503879155 : Real) / 2 ^ 40 <= Chebyshev.theta (4532344700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0544 hb43 4525673444 le_rfl (by norm_num)).2
  have hb45 : (4990604310422552782380 : Real) / 2 ^ 40 <= Chebyshev.theta (4539003798 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0545 hb44 4532344700 le_rfl (by norm_num)).2
  have hb46 : (4997935645048328174861 : Real) / 2 ^ 40 <= Chebyshev.theta (4545673724 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0546 hb45 4539003798 le_rfl (by norm_num)).2
  have hb47 : (5005267463896154750866 : Real) / 2 ^ 40 <= Chebyshev.theta (4552347002 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0547 hb46 4545673724 le_rfl (by norm_num)).2
  have hb48 : (5012599765832894958733 : Real) / 2 ^ 40 <= Chebyshev.theta (4559013660 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0548 hb47 4552347002 le_rfl (by norm_num)).2
  have hb49 : (5019932549824397975452 : Real) / 2 ^ 40 <= Chebyshev.theta (4565677184 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0549 hb48 4559013660 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0550 hb49 4565677184 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 4405738092 with hc25 | hc25
  · rcases Nat.lt_or_ge n 4319228430 with hc12 | hc12
    · rcases Nat.lt_or_ge n 4279313808 with hc6 | hc6
      · rcases Nat.lt_or_ge n 4259378772 with hc3 | hc3
        · rcases Nat.lt_or_ge n 4246077762 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0501 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4252725630 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0502 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0503 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4266027644 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0504 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4272676394 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0505 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0506 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4299270840 with hc9 | hc9
        · rcases Nat.lt_or_ge n 4285956600 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0507 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4292617410 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0508 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0509 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4305926748 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0510 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4312581788 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0511 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0512 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 4359137198 with hc18 | hc18
      · rcases Nat.lt_or_ge n 4339176422 with hc15 | hc15
        · rcases Nat.lt_or_ge n 4325883042 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0513 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4332529632 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0514 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0515 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4345835574 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0516 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4352489334 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0517 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0518 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4379096274 with hc21 | hc21
        · rcases Nat.lt_or_ge n 4365785814 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0519 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4372441968 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0520 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0521 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4392414558 with hc23 | hc23
          · rcases Nat.lt_or_ge n 4385753610 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0522 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0523 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4399082550 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0524 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0525 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 4485697262 with hc37 | hc37
    · rcases Nat.lt_or_ge n 4445701238 with hc31 | hc31
      · rcases Nat.lt_or_ge n 4425715368 with hc28 | hc28
        · rcases Nat.lt_or_ge n 4412390322 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0526 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4419049430 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0527 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0528 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4432368290 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0529 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4439035568 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0530 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0531 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4465691552 with hc34 | hc34
        · rcases Nat.lt_or_ge n 4452369672 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0532 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4459028220 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0533 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0534 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4472356998 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0535 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4479029432 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0536 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0537 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 4525673444 with hc43 | hc43
      · rcases Nat.lt_or_ge n 4505676620 with hc40 | hc40
        · rcases Nat.lt_or_ge n 4492357614 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0538 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4499012732 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0539 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0540 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4512343064 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0541 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4519009934 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0542 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0543 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4545673724 with hc46 | hc46
        · rcases Nat.lt_or_ge n 4532344700 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0544 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4539003798 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0545 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0546 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4559013660 with hc48 | hc48
          · rcases Nat.lt_or_ge n 4552347002 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0547 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0548 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4565677184 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0549 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0550 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (4661206139401073931926 : Real) / 2 ^ 40 <= Chebyshev.theta (4239430052 : Real))
    (n : Nat) (h1 : 4239430052 <= n) (h2 : n <= 4572345229) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((5027265814990202898813 : Real) / 2 ^ 40 <= Chebyshev.theta (4572345230 : Real)) :=
  TFPLink.blk hbase n h1 h2
