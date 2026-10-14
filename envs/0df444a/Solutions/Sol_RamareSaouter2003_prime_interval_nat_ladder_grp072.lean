-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp072
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T05:39:04.159694+00:00
-- url     : https://prove2.me/submissions/bea16dad-4760-46cf-b1a0-bcf0ea7cc0cd

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03570
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03590
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03600

theorem solution (n : Nat)
    (hn : 59087943554933 < n) (hupper : n <= 66860666865847) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 62854270418521 n with h2 | h2
  · -- n > 62854270418521
    rcases Nat.lt_or_ge 64746460011061 n with h4 | h4
    · -- n > 64746460011061
      rcases Nat.lt_or_ge 65713810028327 n with h6 | h6
      · -- n > 65713810028327
        rcases Nat.lt_or_ge 66202891406887 n with h8 | h8
        · -- n > 66202891406887
          rcases Nat.lt_or_ge 66530966233031 n with h10 | h10
          · -- n > 66530966233031
            rcases Nat.lt_or_ge 66695612820983 n with h12 | h12
            · -- n > 66695612820983
              exact RamareSaouter2003.prime_interval_nat_ladder_c03600 n (by omega) (by omega)
            · -- n <= 66695612820983
              exact RamareSaouter2003.prime_interval_nat_ladder_c03599 n (by omega) (by omega)
          · -- n <= 66530966233031
            rcases Nat.lt_or_ge 66366726096217 n with h12 | h12
            · -- n > 66366726096217
              exact RamareSaouter2003.prime_interval_nat_ladder_c03598 n (by omega) (by omega)
            · -- n <= 66366726096217
              exact RamareSaouter2003.prime_interval_nat_ladder_c03597 n (by omega) (by omega)
        · -- n <= 66202891406887
          rcases Nat.lt_or_ge 65876434370287 n with h10 | h10
          · -- n > 65876434370287
            rcases Nat.lt_or_ge 66039461164507 n with h12 | h12
            · -- n > 66039461164507
              exact RamareSaouter2003.prime_interval_nat_ladder_c03596 n (by omega) (by omega)
            · -- n <= 66039461164507
              exact RamareSaouter2003.prime_interval_nat_ladder_c03595 n (by omega) (by omega)
          · -- n <= 65876434370287
            exact RamareSaouter2003.prime_interval_nat_ladder_c03594 n (by omega) (by omega)
      · -- n <= 65713810028327
        rcases Nat.lt_or_ge 65228341793803 n with h8 | h8
        · -- n > 65228341793803
          rcases Nat.lt_or_ge 65389764729973 n with h10 | h10
          · -- n > 65389764729973
            rcases Nat.lt_or_ge 65551587145171 n with h12 | h12
            · -- n > 65551587145171
              exact RamareSaouter2003.prime_interval_nat_ladder_c03593 n (by omega) (by omega)
            · -- n <= 65551587145171
              exact RamareSaouter2003.prime_interval_nat_ladder_c03592 n (by omega) (by omega)
          · -- n <= 65389764729973
            exact RamareSaouter2003.prime_interval_nat_ladder_c03591 n (by omega) (by omega)
        · -- n <= 65228341793803
          rcases Nat.lt_or_ge 64906690416899 n with h10 | h10
          · -- n > 64906690416899
            rcases Nat.lt_or_ge 65067317350697 n with h12 | h12
            · -- n > 65067317350697
              exact RamareSaouter2003.prime_interval_nat_ladder_c03590 n (by omega) (by omega)
            · -- n <= 65067317350697
              exact RamareSaouter2003.prime_interval_nat_ladder_c03589 n (by omega) (by omega)
          · -- n <= 64906690416899
            exact RamareSaouter2003.prime_interval_nat_ladder_c03588 n (by omega) (by omega)
    · -- n <= 64746460011061
      rcases Nat.lt_or_ge 63793350015377 n with h6 | h6
      · -- n > 63793350015377
        rcases Nat.lt_or_ge 64268138184829 n with h8 | h8
        · -- n > 64268138184829
          rcases Nat.lt_or_ge 64427184870203 n with h10 | h10
          · -- n > 64427184870203
            rcases Nat.lt_or_ge 64586625154349 n with h12 | h12
            · -- n > 64586625154349
              exact RamareSaouter2003.prime_interval_nat_ladder_c03587 n (by omega) (by omega)
            · -- n <= 64586625154349
              exact RamareSaouter2003.prime_interval_nat_ladder_c03586 n (by omega) (by omega)
          · -- n <= 64427184870203
            exact RamareSaouter2003.prime_interval_nat_ladder_c03585 n (by omega) (by omega)
        · -- n <= 64268138184829
          rcases Nat.lt_or_ge 63951221725481 n with h10 | h10
          · -- n > 63951221725481
            rcases Nat.lt_or_ge 64109484126409 n with h12 | h12
            · -- n > 64109484126409
              exact RamareSaouter2003.prime_interval_nat_ladder_c03584 n (by omega) (by omega)
            · -- n <= 64109484126409
              exact RamareSaouter2003.prime_interval_nat_ladder_c03583 n (by omega) (by omega)
          · -- n <= 63951221725481
            exact RamareSaouter2003.prime_interval_nat_ladder_c03582 n (by omega) (by omega)
      · -- n <= 63793350015377
        rcases Nat.lt_or_ge 63322069397201 n with h8 | h8
        · -- n > 63322069397201
          rcases Nat.lt_or_ge 63478774812097 n with h10 | h10
          · -- n > 63478774812097
            rcases Nat.lt_or_ge 63635868031607 n with h12 | h12
            · -- n > 63635868031607
              exact RamareSaouter2003.prime_interval_nat_ladder_c03581 n (by omega) (by omega)
            · -- n <= 63635868031607
              exact RamareSaouter2003.prime_interval_nat_ladder_c03580 n (by omega) (by omega)
          · -- n <= 63478774812097
            exact RamareSaouter2003.prime_interval_nat_ladder_c03579 n (by omega) (by omega)
        · -- n <= 63322069397201
          rcases Nat.lt_or_ge 63009818154097 n with h10 | h10
          · -- n > 63009818154097
            rcases Nat.lt_or_ge 63165750829453 n with h12 | h12
            · -- n > 63165750829453
              exact RamareSaouter2003.prime_interval_nat_ladder_c03578 n (by omega) (by omega)
            · -- n <= 63165750829453
              exact RamareSaouter2003.prime_interval_nat_ladder_c03577 n (by omega) (by omega)
          · -- n <= 63009818154097
            exact RamareSaouter2003.prime_interval_nat_ladder_c03576 n (by omega) (by omega)
  · -- n <= 62854270418521
    rcases Nat.lt_or_ge 60866750167681 n with h4 | h4
    · -- n > 60866750167681
      rcases Nat.lt_or_ge 61776135048581 n with h6 | h6
      · -- n > 61776135048581
        rcases Nat.lt_or_ge 62235909901003 n with h8 | h8
        · -- n > 62235909901003
          rcases Nat.lt_or_ge 62544325966961 n with h10 | h10
          · -- n > 62544325966961
            rcases Nat.lt_or_ge 62699106672121 n with h12 | h12
            · -- n > 62699106672121
              exact RamareSaouter2003.prime_interval_nat_ladder_c03575 n (by omega) (by omega)
            · -- n <= 62699106672121
              exact RamareSaouter2003.prime_interval_nat_ladder_c03574 n (by omega) (by omega)
          · -- n <= 62544325966961
            rcases Nat.lt_or_ge 62389927357741 n with h12 | h12
            · -- n > 62389927357741
              exact RamareSaouter2003.prime_interval_nat_ladder_c03573 n (by omega) (by omega)
            · -- n <= 62389927357741
              exact RamareSaouter2003.prime_interval_nat_ladder_c03572 n (by omega) (by omega)
        · -- n <= 62235909901003
          rcases Nat.lt_or_ge 61929014683841 n with h10 | h10
          · -- n > 61929014683841
            rcases Nat.lt_or_ge 62082272655911 n with h12 | h12
            · -- n > 62082272655911
              exact RamareSaouter2003.prime_interval_nat_ladder_c03571 n (by omega) (by omega)
            · -- n <= 62082272655911
              exact RamareSaouter2003.prime_interval_nat_ladder_c03570 n (by omega) (by omega)
          · -- n <= 61929014683841
            exact RamareSaouter2003.prime_interval_nat_ladder_c03569 n (by omega) (by omega)
      · -- n <= 61776135048581
        rcases Nat.lt_or_ge 61319756835331 n with h8 | h8
        · -- n > 61319756835331
          rcases Nat.lt_or_ge 61471507054987 n with h10 | h10
          · -- n > 61471507054987
            rcases Nat.lt_or_ge 61623632816201 n with h12 | h12
            · -- n > 61623632816201
              exact RamareSaouter2003.prime_interval_nat_ladder_c03568 n (by omega) (by omega)
            · -- n <= 61623632816201
              exact RamareSaouter2003.prime_interval_nat_ladder_c03567 n (by omega) (by omega)
          · -- n <= 61471507054987
            exact RamareSaouter2003.prime_interval_nat_ladder_c03566 n (by omega) (by omega)
        · -- n <= 61319756835331
          rcases Nat.lt_or_ge 61017379315331 n with h10 | h10
          · -- n > 61017379315331
            rcases Nat.lt_or_ge 61168381230403 n with h12 | h12
            · -- n > 61168381230403
              exact RamareSaouter2003.prime_interval_nat_ladder_c03565 n (by omega) (by omega)
            · -- n <= 61168381230403
              exact RamareSaouter2003.prime_interval_nat_ladder_c03564 n (by omega) (by omega)
          · -- n <= 61017379315331
            exact RamareSaouter2003.prime_interval_nat_ladder_c03563 n (by omega) (by omega)
    · -- n <= 60866750167681
      rcases Nat.lt_or_ge 59970752023639 n with h6 | h6
      · -- n > 59970752023639
        rcases Nat.lt_or_ge 60417090138463 n with h8 | h8
        · -- n > 60417090138463
          rcases Nat.lt_or_ge 60566606495957 n with h10 | h10
          · -- n > 60566606495957
            rcases Nat.lt_or_ge 60716492867221 n with h12 | h12
            · -- n > 60716492867221
              exact RamareSaouter2003.prime_interval_nat_ladder_c03562 n (by omega) (by omega)
            · -- n <= 60716492867221
              exact RamareSaouter2003.prime_interval_nat_ladder_c03561 n (by omega) (by omega)
          · -- n <= 60566606495957
            exact RamareSaouter2003.prime_interval_nat_ladder_c03560 n (by omega) (by omega)
        · -- n <= 60417090138463
          rcases Nat.lt_or_ge 60119163812219 n with h10 | h10
          · -- n > 60119163812219
            rcases Nat.lt_or_ge 60267942880861 n with h12 | h12
            · -- n > 60267942880861
              exact RamareSaouter2003.prime_interval_nat_ladder_c03559 n (by omega) (by omega)
            · -- n <= 60267942880861
              exact RamareSaouter2003.prime_interval_nat_ladder_c03558 n (by omega) (by omega)
          · -- n <= 60119163812219
            exact RamareSaouter2003.prime_interval_nat_ladder_c03557 n (by omega) (by omega)
      · -- n <= 59970752023639
        rcases Nat.lt_or_ge 59527711282321 n with h8 | h8
        · -- n > 59527711282321
          rcases Nat.lt_or_ge 59675026662019 n with h10 | h10
          · -- n > 59675026662019
            rcases Nat.lt_or_ge 59822706608369 n with h12 | h12
            · -- n > 59822706608369
              exact RamareSaouter2003.prime_interval_nat_ladder_c03556 n (by omega) (by omega)
            · -- n <= 59822706608369
              exact RamareSaouter2003.prime_interval_nat_ladder_c03555 n (by omega) (by omega)
          · -- n <= 59675026662019
            exact RamareSaouter2003.prime_interval_nat_ladder_c03554 n (by omega) (by omega)
        · -- n <= 59527711282321
          rcases Nat.lt_or_ge 59234170625489 n with h10 | h10
          · -- n > 59234170625489
            rcases Nat.lt_or_ge 59380759569431 n with h12 | h12
            · -- n > 59380759569431
              exact RamareSaouter2003.prime_interval_nat_ladder_c03553 n (by omega) (by omega)
            · -- n <= 59380759569431
              exact RamareSaouter2003.prime_interval_nat_ladder_c03552 n (by omega) (by omega)
          · -- n <= 59234170625489
            exact RamareSaouter2003.prime_interval_nat_ladder_c03551 n (by omega) (by omega)
