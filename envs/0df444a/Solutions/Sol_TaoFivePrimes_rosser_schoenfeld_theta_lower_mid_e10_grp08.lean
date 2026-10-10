-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp08
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:47:29.462501+00:00
-- url     : https://prove2.me/submissions/218516c3-cf1f-47cd-bc2f-1b56273e420c

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0351
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0352
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0353
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0354
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0355
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0356
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0357
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0358
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0359
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0360
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0361
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0362
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0363
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0364
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0365
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0366
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0367
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0368
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0369
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0370
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0371
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0372
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0373
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0374
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0375
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0376
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0377
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0378
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0379
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0380
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0381
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0382
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0383
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0384
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0385
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0386
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0387
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0388
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0389
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0390
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0391
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0392
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0393
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0394
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0395
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0396
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0397
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0398
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0399
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0400

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp08` (the range 3248089460 <= n <= 3577176103 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0351` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0400`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (3571226616548090907563 : Real) / 2 ^ 40 <= Chebyshev.theta (3248089460 : Real))
    (n : Nat) (h1 : 3248089460 <= n) (h2 : n <= 3577176103) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((3933072480233213816578 : Real) / 2 ^ 40 <= Chebyshev.theta (3577176104 : Real)) := by
  have hb0 := hbase
  have hb1 : (3578447712964641267981 : Real) / 2 ^ 40 <= Chebyshev.theta (3254651360 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0351 hb0 3248089460 le_rfl (by norm_num)).2
  have hb2 : (3585669474117822815242 : Real) / 2 ^ 40 <= Chebyshev.theta (3261218120 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0352 hb1 3254651360 le_rfl (by norm_num)).2
  have hb3 : (3592891899730770413570 : Real) / 2 ^ 40 <= Chebyshev.theta (3267796440 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0353 hb2 3261218120 le_rfl (by norm_num)).2
  have hb4 : (3600114989063688511995 : Real) / 2 ^ 40 <= Chebyshev.theta (3274374114 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0354 hb3 3267796440 le_rfl (by norm_num)).2
  have hb5 : (3607338740098327024660 : Real) / 2 ^ 40 <= Chebyshev.theta (3280940718 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0355 hb4 3274374114 le_rfl (by norm_num)).2
  have hb6 : (3614563151257782708490 : Real) / 2 ^ 40 <= Chebyshev.theta (3287510198 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0356 hb5 3280940718 le_rfl (by norm_num)).2
  have hb7 : (3621788221330398463908 : Real) / 2 ^ 40 <= Chebyshev.theta (3294081278 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0357 hb6 3287510198 le_rfl (by norm_num)).2
  have hb8 : (3629013949390313460526 : Real) / 2 ^ 40 <= Chebyshev.theta (3300661328 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0358 hb7 3294081278 le_rfl (by norm_num)).2
  have hb9 : (3636240333986218518876 : Real) / 2 ^ 40 <= Chebyshev.theta (3307224998 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0359 hb8 3300661328 le_rfl (by norm_num)).2
  have hb10 : (3643467373692295402770 : Real) / 2 ^ 40 <= Chebyshev.theta (3313803614 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0360 hb9 3307224998 le_rfl (by norm_num)).2
  have hb11 : (3650695067473462962801 : Real) / 2 ^ 40 <= Chebyshev.theta (3320368452 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0361 hb10 3313803614 le_rfl (by norm_num)).2
  have hb12 : (3657923413160572171503 : Real) / 2 ^ 40 <= Chebyshev.theta (3326940218 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0362 hb11 3320368452 le_rfl (by norm_num)).2
  have hb13 : (3665152410127699428911 : Real) / 2 ^ 40 <= Chebyshev.theta (3333512598 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0363 hb12 3326940218 le_rfl (by norm_num)).2
  have hb14 : (3672382057321529188234 : Real) / 2 ^ 40 <= Chebyshev.theta (3340094060 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0364 hb13 3333512598 le_rfl (by norm_num)).2
  have hb15 : (3679612354095856734049 : Real) / 2 ^ 40 <= Chebyshev.theta (3346671198 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0365 hb14 3340094060 le_rfl (by norm_num)).2
  have hb16 : (3686843298887733719238 : Real) / 2 ^ 40 <= Chebyshev.theta (3353248950 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0366 hb15 3346671198 le_rfl (by norm_num)).2
  have hb17 : (3694074890729806756102 : Real) / 2 ^ 40 <= Chebyshev.theta (3359836968 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0367 hb16 3353248950 le_rfl (by norm_num)).2
  have hb18 : (3701307128333387719385 : Real) / 2 ^ 40 <= Chebyshev.theta (3366413570 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0368 hb17 3359836968 le_rfl (by norm_num)).2
  have hb19 : (3708540010249958408811 : Real) / 2 ^ 40 <= Chebyshev.theta (3372987824 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0369 hb18 3366413570 le_rfl (by norm_num)).2
  have hb20 : (3715773535015929336470 : Real) / 2 ^ 40 <= Chebyshev.theta (3379567914 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0370 hb19 3372987824 le_rfl (by norm_num)).2
  have hb21 : (3723007702225306062670 : Real) / 2 ^ 40 <= Chebyshev.theta (3386153228 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0371 hb20 3379567914 le_rfl (by norm_num)).2
  have hb22 : (3730242509732941980990 : Real) / 2 ^ 40 <= Chebyshev.theta (3392731620 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0372 hb21 3386153228 le_rfl (by norm_num)).2
  have hb23 : (3737477956812810371137 : Real) / 2 ^ 40 <= Chebyshev.theta (3399310530 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0373 hb22 3392731620 le_rfl (by norm_num)).2
  have hb24 : (3744714041997042243775 : Real) / 2 ^ 40 <= Chebyshev.theta (3405890168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0374 hb23 3399310530 le_rfl (by norm_num)).2
  have hb25 : (3751950764558680552215 : Real) / 2 ^ 40 <= Chebyshev.theta (3412476462 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0375 hb24 3405890168 le_rfl (by norm_num)).2
  have hb26 : (3759188123018134194517 : Real) / 2 ^ 40 <= Chebyshev.theta (3419057600 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0376 hb25 3412476462 le_rfl (by norm_num)).2
  have hb27 : (3766426115716073008823 : Real) / 2 ^ 40 <= Chebyshev.theta (3425631198 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0377 hb26 3419057600 le_rfl (by norm_num)).2
  have hb28 : (3773664741590622445489 : Real) / 2 ^ 40 <= Chebyshev.theta (3432215742 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0378 hb27 3425631198 le_rfl (by norm_num)).2
  have hb29 : (3780904000341659208812 : Real) / 2 ^ 40 <= Chebyshev.theta (3438803634 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0379 hb28 3432215742 le_rfl (by norm_num)).2
  have hb30 : (3788143890296084306257 : Real) / 2 ^ 40 <= Chebyshev.theta (3445384968 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0380 hb29 3438803634 le_rfl (by norm_num)).2
  have hb31 : (3795384409834199480482 : Real) / 2 ^ 40 <= Chebyshev.theta (3451964358 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0381 hb30 3445384968 le_rfl (by norm_num)).2
  have hb32 : (3802625558130991282543 : Real) / 2 ^ 40 <= Chebyshev.theta (3458550548 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0382 hb31 3451964358 le_rfl (by norm_num)).2
  have hb33 : (3809867334260784947331 : Real) / 2 ^ 40 <= Chebyshev.theta (3465129000 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0383 hb32 3458550548 le_rfl (by norm_num)).2
  have hb34 : (3817109736653933777669 : Real) / 2 ^ 40 <= Chebyshev.theta (3471721910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0384 hb33 3465129000 le_rfl (by norm_num)).2
  have hb35 : (3824352765168469965359 : Real) / 2 ^ 40 <= Chebyshev.theta (3478311962 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0385 hb34 3471721910 le_rfl (by norm_num)).2
  have hb36 : (3831596417827077786016 : Real) / 2 ^ 40 <= Chebyshev.theta (3484894950 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0386 hb35 3478311962 le_rfl (by norm_num)).2
  have hb37 : (3838840693523785218774 : Real) / 2 ^ 40 <= Chebyshev.theta (3491484414 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0387 hb36 3484894950 le_rfl (by norm_num)).2
  have hb38 : (3846085591556381899106 : Real) / 2 ^ 40 <= Chebyshev.theta (3498069900 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0388 hb37 3491484414 le_rfl (by norm_num)).2
  have hb39 : (3853331110645110835169 : Real) / 2 ^ 40 <= Chebyshev.theta (3504660282 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0389 hb38 3498069900 le_rfl (by norm_num)).2
  have hb40 : (3860577249055657557498 : Real) / 2 ^ 40 <= Chebyshev.theta (3511243410 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0390 hb39 3504660282 le_rfl (by norm_num)).2
  have hb41 : (3867824005755173700039 : Real) / 2 ^ 40 <= Chebyshev.theta (3517831152 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0391 hb40 3511243410 le_rfl (by norm_num)).2
  have hb42 : (3875071380325198449379 : Real) / 2 ^ 40 <= Chebyshev.theta (3524425260 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0392 hb41 3517831152 le_rfl (by norm_num)).2
  have hb43 : (3882319371357775836154 : Real) / 2 ^ 40 <= Chebyshev.theta (3531019764 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0393 hb42 3524425260 le_rfl (by norm_num)).2
  have hb44 : (3889567977874760686459 : Real) / 2 ^ 40 <= Chebyshev.theta (3537602942 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0394 hb43 3531019764 le_rfl (by norm_num)).2
  have hb45 : (3896817198607559925216 : Real) / 2 ^ 40 <= Chebyshev.theta (3544203680 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0395 hb44 3537602942 le_rfl (by norm_num)).2
  have hb46 : (3904067032930808148298 : Real) / 2 ^ 40 <= Chebyshev.theta (3550789604 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0396 hb45 3544203680 le_rfl (by norm_num)).2
  have hb47 : (3911317479047486887076 : Real) / 2 ^ 40 <= Chebyshev.theta (3557381414 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0397 hb46 3550789604 le_rfl (by norm_num)).2
  have hb48 : (3918568536381538036470 : Real) / 2 ^ 40 <= Chebyshev.theta (3563981364 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0398 hb47 3557381414 le_rfl (by norm_num)).2
  have hb49 : (3925820203853410845290 : Real) / 2 ^ 40 <= Chebyshev.theta (3570567882 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0399 hb48 3563981364 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0400 hb49 3570567882 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 3412476462 with hc25 | hc25
  · rcases Nat.lt_or_ge n 3326940218 with hc12 | hc12
    · rcases Nat.lt_or_ge n 3287510198 with hc6 | hc6
      · rcases Nat.lt_or_ge n 3267796440 with hc3 | hc3
        · rcases Nat.lt_or_ge n 3254651360 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0351 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3261218120 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0352 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0353 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3274374114 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0354 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3280940718 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0355 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0356 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3307224998 with hc9 | hc9
        · rcases Nat.lt_or_ge n 3294081278 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0357 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3300661328 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0358 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0359 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3313803614 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0360 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3320368452 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0361 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0362 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 3366413570 with hc18 | hc18
      · rcases Nat.lt_or_ge n 3346671198 with hc15 | hc15
        · rcases Nat.lt_or_ge n 3333512598 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0363 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3340094060 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0364 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0365 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3353248950 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0366 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3359836968 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0367 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0368 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3386153228 with hc21 | hc21
        · rcases Nat.lt_or_ge n 3372987824 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0369 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3379567914 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0370 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0371 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3399310530 with hc23 | hc23
          · rcases Nat.lt_or_ge n 3392731620 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0372 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0373 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3405890168 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0374 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0375 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 3491484414 with hc37 | hc37
    · rcases Nat.lt_or_ge n 3451964358 with hc31 | hc31
      · rcases Nat.lt_or_ge n 3432215742 with hc28 | hc28
        · rcases Nat.lt_or_ge n 3419057600 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0376 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3425631198 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0377 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0378 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3438803634 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0379 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3445384968 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0380 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0381 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3471721910 with hc34 | hc34
        · rcases Nat.lt_or_ge n 3458550548 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0382 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3465129000 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0383 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0384 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3478311962 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0385 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3484894950 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0386 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0387 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 3531019764 with hc43 | hc43
      · rcases Nat.lt_or_ge n 3511243410 with hc40 | hc40
        · rcases Nat.lt_or_ge n 3498069900 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0388 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3504660282 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0389 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0390 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3517831152 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0391 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3524425260 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0392 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0393 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3550789604 with hc46 | hc46
        · rcases Nat.lt_or_ge n 3537602942 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0394 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3544203680 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0395 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0396 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3563981364 with hc48 | hc48
          · rcases Nat.lt_or_ge n 3557381414 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0397 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0398 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3570567882 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0399 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0400 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (3571226616548090907563 : Real) / 2 ^ 40 <= Chebyshev.theta (3248089460 : Real))
    (n : Nat) (h1 : 3248089460 <= n) (h2 : n <= 3577176103) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((3933072480233213816578 : Real) / 2 ^ 40 <= Chebyshev.theta (3577176104 : Real)) :=
  TFPLink.blk hbase n h1 h2
