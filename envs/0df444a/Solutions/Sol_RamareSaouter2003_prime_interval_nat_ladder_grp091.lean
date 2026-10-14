-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp091
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T11:19:38.607541+00:00
-- url     : https://prove2.me/submissions/2bfb9473-0bb4-4d69-a0a7-d3c9f8272d29

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04521
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04541
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04550

theorem solution (n : Nat)
    (hn : 757347815694311 < n) (hupper : n <= 872308179808937) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 812793980369599 n with h2 | h2
  · -- n > 812793980369599
    rcases Nat.lt_or_ge 840837020640943 n with h4 | h4
    · -- n > 840837020640943
      rcases Nat.lt_or_ge 855218662120429 n with h6 | h6
      · -- n > 855218662120429
        rcases Nat.lt_or_ge 862499969930171 n with h8 | h8
        · -- n > 862499969930171
          rcases Nat.lt_or_ge 867389956697963 n with h10 | h10
          · -- n > 867389956697963
            rcases Nat.lt_or_ge 869845649173049 n with h12 | h12
            · -- n > 869845649173049
              exact RamareSaouter2003.prime_interval_nat_ladder_c04550 n (by omega) (by omega)
            · -- n <= 869845649173049
              exact RamareSaouter2003.prime_interval_nat_ladder_c04549 n (by omega) (by omega)
          · -- n <= 867389956697963
            rcases Nat.lt_or_ge 864941854296827 n with h12 | h12
            · -- n > 864941854296827
              exact RamareSaouter2003.prime_interval_nat_ladder_c04548 n (by omega) (by omega)
            · -- n <= 864941854296827
              exact RamareSaouter2003.prime_interval_nat_ladder_c04547 n (by omega) (by omega)
        · -- n <= 862499969930171
          rcases Nat.lt_or_ge 857639328927833 n with h10 | h10
          · -- n > 857639328927833
            rcases Nat.lt_or_ge 860066055973093 n with h12 | h12
            · -- n > 860066055973093
              exact RamareSaouter2003.prime_interval_nat_ladder_c04546 n (by omega) (by omega)
            · -- n <= 860066055973093
              exact RamareSaouter2003.prime_interval_nat_ladder_c04545 n (by omega) (by omega)
          · -- n <= 857639328927833
            exact RamareSaouter2003.prime_interval_nat_ladder_c04544 n (by omega) (by omega)
      · -- n <= 855218662120429
        rcases Nat.lt_or_ge 847996113333163 n with h8 | h8
        · -- n > 847996113333163
          rcases Nat.lt_or_ge 850396746974903 n with h10 | h10
          · -- n > 850396746974903
            rcases Nat.lt_or_ge 852804451789999 n with h12 | h12
            · -- n > 852804451789999
              exact RamareSaouter2003.prime_interval_nat_ladder_c04543 n (by omega) (by omega)
            · -- n <= 852804451789999
              exact RamareSaouter2003.prime_interval_nat_ladder_c04542 n (by omega) (by omega)
          · -- n <= 850396746974903
            exact RamareSaouter2003.prime_interval_nat_ladder_c04541 n (by omega) (by omega)
        · -- n <= 847996113333163
          rcases Nat.lt_or_ge 843217399743269 n with h10 | h10
          · -- n > 843217399743269
            rcases Nat.lt_or_ge 845603760629249 n with h12 | h12
            · -- n > 845603760629249
              exact RamareSaouter2003.prime_interval_nat_ladder_c04540 n (by omega) (by omega)
            · -- n <= 845603760629249
              exact RamareSaouter2003.prime_interval_nat_ladder_c04539 n (by omega) (by omega)
          · -- n <= 843217399743269
            exact RamareSaouter2003.prime_interval_nat_ladder_c04538 n (by omega) (by omega)
    · -- n <= 840837020640943
      rcases Nat.lt_or_ge 826694864910331 n with h6 | h6
      · -- n > 826694864910331
        rcases Nat.lt_or_ge 833736166209073 n with h8 | h8
        · -- n > 833736166209073
          rcases Nat.lt_or_ge 836096706893449 n with h10 | h10
          · -- n > 836096706893449
            rcases Nat.lt_or_ge 838463422211377 n with h12 | h12
            · -- n > 838463422211377
              exact RamareSaouter2003.prime_interval_nat_ladder_c04537 n (by omega) (by omega)
            · -- n <= 838463422211377
              exact RamareSaouter2003.prime_interval_nat_ladder_c04536 n (by omega) (by omega)
          · -- n <= 836096706893449
            exact RamareSaouter2003.prime_interval_nat_ladder_c04535 n (by omega) (by omega)
        · -- n <= 833736166209073
          rcases Nat.lt_or_ge 829035172376039 n with h10 | h10
          · -- n > 829035172376039
            rcases Nat.lt_or_ge 831382364534809 n with h12 | h12
            · -- n > 831382364534809
              exact RamareSaouter2003.prime_interval_nat_ladder_c04534 n (by omega) (by omega)
            · -- n <= 831382364534809
              exact RamareSaouter2003.prime_interval_nat_ladder_c04533 n (by omega) (by omega)
          · -- n <= 829035172376039
            exact RamareSaouter2003.prime_interval_nat_ladder_c04532 n (by omega) (by omega)
      · -- n <= 826694864910331
        rcases Nat.lt_or_ge 819713770361107 n with h8 | h8
        · -- n > 819713770361107
          rcases Nat.lt_or_ge 822034090771961 n with h10 | h10
          · -- n > 822034090771961
            rcases Nat.lt_or_ge 824361079588307 n with h12 | h12
            · -- n > 824361079588307
              exact RamareSaouter2003.prime_interval_nat_ladder_c04531 n (by omega) (by omega)
            · -- n <= 824361079588307
              exact RamareSaouter2003.prime_interval_nat_ladder_c04530 n (by omega) (by omega)
          · -- n <= 822034090771961
            exact RamareSaouter2003.prime_interval_nat_ladder_c04529 n (by omega) (by omega)
        · -- n <= 819713770361107
          rcases Nat.lt_or_ge 815095187389789 n with h10 | h10
          · -- n > 815095187389789
            rcases Nat.lt_or_ge 817400216370889 n with h12 | h12
            · -- n > 817400216370889
              exact RamareSaouter2003.prime_interval_nat_ladder_c04528 n (by omega) (by omega)
            · -- n <= 817400216370889
              exact RamareSaouter2003.prime_interval_nat_ladder_c04527 n (by omega) (by omega)
          · -- n <= 815095187389789
            exact RamareSaouter2003.prime_interval_nat_ladder_c04526 n (by omega) (by omega)
  · -- n <= 812793980369599
    rcases Nat.lt_or_ge 783472959459209 n with h4 | h4
    · -- n > 783472959459209
      rcases Nat.lt_or_ge 796872261355691 n with h6 | h6
      · -- n > 796872261355691
        rcases Nat.lt_or_ge 803658314265293 n with h8 | h8
        · -- n > 803658314265293
          rcases Nat.lt_or_ge 808211500740289 n with h10 | h10
          · -- n > 808211500740289
            rcases Nat.lt_or_ge 810499330341497 n with h12 | h12
            · -- n > 810499330341497
              exact RamareSaouter2003.prime_interval_nat_ladder_c04525 n (by omega) (by omega)
            · -- n <= 810499330341497
              exact RamareSaouter2003.prime_interval_nat_ladder_c04524 n (by omega) (by omega)
          · -- n <= 808211500740289
            rcases Nat.lt_or_ge 805932705173447 n with h12 | h12
            · -- n > 805932705173447
              exact RamareSaouter2003.prime_interval_nat_ladder_c04523 n (by omega) (by omega)
            · -- n <= 805932705173447
              exact RamareSaouter2003.prime_interval_nat_ladder_c04522 n (by omega) (by omega)
        · -- n <= 803658314265293
          rcases Nat.lt_or_ge 799127991241289 n with h10 | h10
          · -- n > 799127991241289
            rcases Nat.lt_or_ge 801389683191151 n with h12 | h12
            · -- n > 801389683191151
              exact RamareSaouter2003.prime_interval_nat_ladder_c04521 n (by omega) (by omega)
            · -- n <= 801389683191151
              exact RamareSaouter2003.prime_interval_nat_ladder_c04520 n (by omega) (by omega)
          · -- n <= 799127991241289
            exact RamareSaouter2003.prime_interval_nat_ladder_c04519 n (by omega) (by omega)
      · -- n <= 796872261355691
        rcases Nat.lt_or_ge 790143088152377 n with h8 | h8
        · -- n > 790143088152377
          rcases Nat.lt_or_ge 792379316426723 n with h10 | h10
          · -- n > 792379316426723
            rcases Nat.lt_or_ge 794622481910837 n with h12 | h12
            · -- n > 794622481910837
              exact RamareSaouter2003.prime_interval_nat_ladder_c04518 n (by omega) (by omega)
            · -- n <= 794622481910837
              exact RamareSaouter2003.prime_interval_nat_ladder_c04517 n (by omega) (by omega)
          · -- n <= 792379316426723
            exact RamareSaouter2003.prime_interval_nat_ladder_c04516 n (by omega) (by omega)
        · -- n <= 790143088152377
          rcases Nat.lt_or_ge 785690709044203 n with h10 | h10
          · -- n > 785690709044203
            rcases Nat.lt_or_ge 787914119975993 n with h12 | h12
            · -- n > 787914119975993
              exact RamareSaouter2003.prime_interval_nat_ladder_c04515 n (by omega) (by omega)
            · -- n <= 787914119975993
              exact RamareSaouter2003.prime_interval_nat_ladder_c04514 n (by omega) (by omega)
          · -- n <= 785690709044203
            exact RamareSaouter2003.prime_interval_nat_ladder_c04513 n (by omega) (by omega)
    · -- n <= 783472959459209
      rcases Nat.lt_or_ge 770300281436557 n with h6 | h6
      · -- n > 770300281436557
        rcases Nat.lt_or_ge 776856800233799 n with h8 | h8
        · -- n > 776856800233799
          rcases Nat.lt_or_ge 779056298442283 n with h10 | h10
          · -- n > 779056298442283
            rcases Nat.lt_or_ge 781262033885483 n with h12 | h12
            · -- n > 781262033885483
              exact RamareSaouter2003.prime_interval_nat_ladder_c04512 n (by omega) (by omega)
            · -- n <= 781262033885483
              exact RamareSaouter2003.prime_interval_nat_ladder_c04511 n (by omega) (by omega)
          · -- n <= 779056298442283
            exact RamareSaouter2003.prime_interval_nat_ladder_c04510 n (by omega) (by omega)
        · -- n <= 776856800233799
          rcases Nat.lt_or_ge 772478753557339 n with h10 | h10
          · -- n > 772478753557339
            rcases Nat.lt_or_ge 774664756527191 n with h12 | h12
            · -- n > 774664756527191
              exact RamareSaouter2003.prime_interval_nat_ladder_c04509 n (by omega) (by omega)
            · -- n <= 774664756527191
              exact RamareSaouter2003.prime_interval_nat_ladder_c04508 n (by omega) (by omega)
          · -- n <= 772478753557339
            exact RamareSaouter2003.prime_interval_nat_ladder_c04507 n (by omega) (by omega)
      · -- n <= 770300281436557
        rcases Nat.lt_or_ge 763796530021817 n with h8 | h8
        · -- n > 763796530021817
          rcases Nat.lt_or_ge 765958542326179 n with h10 | h10
          · -- n > 765958542326179
            rcases Nat.lt_or_ge 768126490805873 n with h12 | h12
            · -- n > 768126490805873
              exact RamareSaouter2003.prime_interval_nat_ladder_c04506 n (by omega) (by omega)
            · -- n <= 768126490805873
              exact RamareSaouter2003.prime_interval_nat_ladder_c04505 n (by omega) (by omega)
          · -- n <= 765958542326179
            exact RamareSaouter2003.prime_interval_nat_ladder_c04504 n (by omega) (by omega)
        · -- n <= 763796530021817
          rcases Nat.lt_or_ge 759490932421411 n with h10 | h10
          · -- n > 759490932421411
            rcases Nat.lt_or_ge 761640278138449 n with h12 | h12
            · -- n > 761640278138449
              exact RamareSaouter2003.prime_interval_nat_ladder_c04503 n (by omega) (by omega)
            · -- n <= 761640278138449
              exact RamareSaouter2003.prime_interval_nat_ladder_c04502 n (by omega) (by omega)
          · -- n <= 759490932421411
            exact RamareSaouter2003.prime_interval_nat_ladder_c04501 n (by omega) (by omega)
