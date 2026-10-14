-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp109
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T16:33:46.108632+00:00
-- url     : https://prove2.me/submissions/12ca6d45-afae-4d33-93de-6dd82055cbac

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05423
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05443
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05450

theorem solution (n : Nat)
    (hn : 9641307945289051 < n) (hupper : n <= 11105084835698311) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 10347350793805903 n with h2 | h2
  · -- n > 10347350793805903
    rcases Nat.lt_or_ge 10704399423481229 n with h4 | h4
    · -- n > 10704399423481229
      rcases Nat.lt_or_ge 10887487831103777 n with h6 | h6
      · -- n > 10887487831103777
        rcases Nat.lt_or_ge 10980215064820549 n with h8 | h8
        · -- n > 10980215064820549
          rcases Nat.lt_or_ge 11042476053183899 n with h10 | h10
          · -- n > 11042476053183899
            rcases Nat.lt_or_ge 11073732431814523 n with h12 | h12
            · -- n > 11073732431814523
              exact RamareSaouter2003.prime_interval_nat_ladder_c05450 n (by omega) (by omega)
            · -- n <= 11073732431814523
              exact RamareSaouter2003.prime_interval_nat_ladder_c05449 n (by omega) (by omega)
          · -- n <= 11042476053183899
            rcases Nat.lt_or_ge 11011302878803741 n with h12 | h12
            · -- n > 11011302878803741
              exact RamareSaouter2003.prime_interval_nat_ladder_c05448 n (by omega) (by omega)
            · -- n <= 11011302878803741
              exact RamareSaouter2003.prime_interval_nat_ladder_c05447 n (by omega) (by omega)
        · -- n <= 10980215064820549
          rcases Nat.lt_or_ge 10918306685769689 n with h10 | h10
          · -- n > 10918306685769689
            rcases Nat.lt_or_ge 10949219745900257 n with h12 | h12
            · -- n > 10949219745900257
              exact RamareSaouter2003.prime_interval_nat_ladder_c05446 n (by omega) (by omega)
            · -- n <= 10949219745900257
              exact RamareSaouter2003.prime_interval_nat_ladder_c05445 n (by omega) (by omega)
          · -- n <= 10918306685769689
            exact RamareSaouter2003.prime_interval_nat_ladder_c05444 n (by omega) (by omega)
      · -- n <= 10887487831103777
        rcases Nat.lt_or_ge 10795559207387887 n with h8 | h8
        · -- n > 10795559207387887
          rcases Nat.lt_or_ge 10826102927397341 n with h10 | h10
          · -- n > 10826102927397341
            rcases Nat.lt_or_ge 10856750036494567 n with h12 | h12
            · -- n > 10856750036494567
              exact RamareSaouter2003.prime_interval_nat_ladder_c05443 n (by omega) (by omega)
            · -- n <= 10856750036494567
              exact RamareSaouter2003.prime_interval_nat_ladder_c05442 n (by omega) (by omega)
          · -- n <= 10826102927397341
            exact RamareSaouter2003.prime_interval_nat_ladder_c05441 n (by omega) (by omega)
        · -- n <= 10795559207387887
          rcases Nat.lt_or_ge 10734703356856231 n with h10 | h10
          · -- n > 10734703356856231
            rcases Nat.lt_or_ge 10765093495620313 n with h12 | h12
            · -- n > 10765093495620313
              exact RamareSaouter2003.prime_interval_nat_ladder_c05440 n (by omega) (by omega)
            · -- n <= 10765093495620313
              exact RamareSaouter2003.prime_interval_nat_ladder_c05439 n (by omega) (by omega)
          · -- n <= 10734703356856231
            exact RamareSaouter2003.prime_interval_nat_ladder_c05438 n (by omega) (by omega)
    · -- n <= 10704399423481229
      rcases Nat.lt_or_ge 10524364562191577 n with h6 | h6
      · -- n > 10524364562191577
        rcases Nat.lt_or_ge 10614004665819209 n with h8 | h8
        · -- n > 10614004665819209
          rcases Nat.lt_or_ge 10644049848441907 n with h10 | h10
          · -- n > 10644049848441907
            rcases Nat.lt_or_ge 10674178407841303 n with h12 | h12
            · -- n > 10674178407841303
              exact RamareSaouter2003.prime_interval_nat_ladder_c05437 n (by omega) (by omega)
            · -- n <= 10674178407841303
              exact RamareSaouter2003.prime_interval_nat_ladder_c05436 n (by omega) (by omega)
          · -- n <= 10644049848441907
            exact RamareSaouter2003.prime_interval_nat_ladder_c05435 n (by omega) (by omega)
        · -- n <= 10614004665819209
          rcases Nat.lt_or_ge 10554161886140077 n with h10 | h10
          · -- n > 10554161886140077
            rcases Nat.lt_or_ge 10584039800916739 n with h12 | h12
            · -- n > 10584039800916739
              exact RamareSaouter2003.prime_interval_nat_ladder_c05434 n (by omega) (by omega)
            · -- n <= 10584039800916739
              exact RamareSaouter2003.prime_interval_nat_ladder_c05433 n (by omega) (by omega)
          · -- n <= 10554161886140077
            exact RamareSaouter2003.prime_interval_nat_ladder_c05432 n (by omega) (by omega)
      · -- n <= 10524364562191577
        rcases Nat.lt_or_ge 10435486036664461 n with h8 | h8
        · -- n > 10435486036664461
          rcases Nat.lt_or_ge 10465029688442761 n with h10 | h10
          · -- n > 10465029688442761
            rcases Nat.lt_or_ge 10494656896939669 n with h12 | h12
            · -- n > 10494656896939669
              exact RamareSaouter2003.prime_interval_nat_ladder_c05431 n (by omega) (by omega)
            · -- n <= 10494656896939669
              exact RamareSaouter2003.prime_interval_nat_ladder_c05430 n (by omega) (by omega)
          · -- n <= 10465029688442761
            exact RamareSaouter2003.prime_interval_nat_ladder_c05429 n (by omega) (by omega)
        · -- n <= 10435486036664461
          rcases Nat.lt_or_ge 10376646050502653 n with h10 | h10
          · -- n > 10376646050502653
            rcases Nat.lt_or_ge 10406024543275013 n with h12 | h12
            · -- n > 10406024543275013
              exact RamareSaouter2003.prime_interval_nat_ladder_c05428 n (by omega) (by omega)
            · -- n <= 10406024543275013
              exact RamareSaouter2003.prime_interval_nat_ladder_c05427 n (by omega) (by omega)
          · -- n <= 10376646050502653
            exact RamareSaouter2003.prime_interval_nat_ladder_c05426 n (by omega) (by omega)
  · -- n <= 10347350793805903
    rcases Nat.lt_or_ge 9973980149766761 n with h4 | h4
    · -- n > 9973980149766761
      rcases Nat.lt_or_ge 10144597341828379 n with h6 | h6
      · -- n > 10144597341828379
        rcases Nat.lt_or_ge 10231001424663769 n with h8 | h8
        · -- n > 10231001424663769
          rcases Nat.lt_or_ge 10289015367818611 n with h10 | h10
          · -- n > 10289015367818611
            rcases Nat.lt_or_ge 10318144693935623 n with h12 | h12
            · -- n > 10318144693935623
              exact RamareSaouter2003.prime_interval_nat_ladder_c05425 n (by omega) (by omega)
            · -- n <= 10318144693935623
              exact RamareSaouter2003.prime_interval_nat_ladder_c05424 n (by omega) (by omega)
          · -- n <= 10289015367818611
            rcases Nat.lt_or_ge 10259968342812151 n with h12 | h12
            · -- n > 10259968342812151
              exact RamareSaouter2003.prime_interval_nat_ladder_c05423 n (by omega) (by omega)
            · -- n <= 10259968342812151
              exact RamareSaouter2003.prime_interval_nat_ladder_c05422 n (by omega) (by omega)
        · -- n <= 10231001424663769
          rcases Nat.lt_or_ge 10173316102667869 n with h10 | h10
          · -- n > 10173316102667869
            rcases Nat.lt_or_ge 10202117460545149 n with h12 | h12
            · -- n > 10202117460545149
              exact RamareSaouter2003.prime_interval_nat_ladder_c05421 n (by omega) (by omega)
            · -- n <= 10202117460545149
              exact RamareSaouter2003.prime_interval_nat_ladder_c05420 n (by omega) (by omega)
          · -- n <= 10173316102667869
            exact RamareSaouter2003.prime_interval_nat_ladder_c05419 n (by omega) (by omega)
      · -- n <= 10144597341828379
        rcases Nat.lt_or_ge 10058930154909409 n with h8 | h8
        · -- n > 10058930154909409
          rcases Nat.lt_or_ge 10087405751218259 n with h10 | h10
          · -- n > 10087405751218259
            rcases Nat.lt_or_ge 10115964640425829 n with h12 | h12
            · -- n > 10115964640425829
              exact RamareSaouter2003.prime_interval_nat_ladder_c05418 n (by omega) (by omega)
            · -- n <= 10115964640425829
              exact RamareSaouter2003.prime_interval_nat_ladder_c05417 n (by omega) (by omega)
          · -- n <= 10087405751218259
            exact RamareSaouter2003.prime_interval_nat_ladder_c05416 n (by omega) (by omega)
        · -- n <= 10058930154909409
          rcases Nat.lt_or_ge 10002218722782101 n with h10 | h10
          · -- n > 10002218722782101
            rcases Nat.lt_or_ge 10030533063447943 n with h12 | h12
            · -- n > 10030533063447943
              exact RamareSaouter2003.prime_interval_nat_ladder_c05415 n (by omega) (by omega)
            · -- n <= 10030533063447943
              exact RamareSaouter2003.prime_interval_nat_ladder_c05414 n (by omega) (by omega)
          · -- n <= 10002218722782101
            exact RamareSaouter2003.prime_interval_nat_ladder_c05413 n (by omega) (by omega)
    · -- n <= 9973980149766761
      rcases Nat.lt_or_ge 9806223163902677 n with h6 | h6
      · -- n > 9806223163902677
        rcases Nat.lt_or_ge 9889749379991423 n with h8 | h8
        · -- n > 9889749379991423
          rcases Nat.lt_or_ge 9917747048751571 n with h10 | h10
          · -- n > 9917747048751571
            rcases Nat.lt_or_ge 9945824776067473 n with h12 | h12
            · -- n > 9945824776067473
              exact RamareSaouter2003.prime_interval_nat_ladder_c05412 n (by omega) (by omega)
            · -- n <= 9945824776067473
              exact RamareSaouter2003.prime_interval_nat_ladder_c05411 n (by omega) (by omega)
          · -- n <= 9917747048751571
            exact RamareSaouter2003.prime_interval_nat_ladder_c05410 n (by omega) (by omega)
        · -- n <= 9889749379991423
          rcases Nat.lt_or_ge 9833987009489147 n with h10 | h10
          · -- n > 9833987009489147
            rcases Nat.lt_or_ge 9861829817810701 n with h12 | h12
            · -- n > 9861829817810701
              exact RamareSaouter2003.prime_interval_nat_ladder_c05409 n (by omega) (by omega)
            · -- n <= 9861829817810701
              exact RamareSaouter2003.prime_interval_nat_ladder_c05408 n (by omega) (by omega)
          · -- n <= 9833987009489147
            exact RamareSaouter2003.prime_interval_nat_ladder_c05407 n (by omega) (by omega)
      · -- n <= 9806223163902677
        rcases Nat.lt_or_ge 9723418580349367 n with h8 | h8
        · -- n > 9723418580349367
          rcases Nat.lt_or_ge 9750940016615989 n with h10 | h10
          · -- n > 9750940016615989
            rcases Nat.lt_or_ge 9778538313209189 n with h12 | h12
            · -- n > 9778538313209189
              exact RamareSaouter2003.prime_interval_nat_ladder_c05406 n (by omega) (by omega)
            · -- n <= 9778538313209189
              exact RamareSaouter2003.prime_interval_nat_ladder_c05405 n (by omega) (by omega)
          · -- n <= 9750940016615989
            exact RamareSaouter2003.prime_interval_nat_ladder_c05404 n (by omega) (by omega)
        · -- n <= 9723418580349367
          rcases Nat.lt_or_ge 9668595030173831 n with h10 | h10
          · -- n > 9668595030173831
            rcases Nat.lt_or_ge 9695969109641201 n with h12 | h12
            · -- n > 9695969109641201
              exact RamareSaouter2003.prime_interval_nat_ladder_c05403 n (by omega) (by omega)
            · -- n <= 9695969109641201
              exact RamareSaouter2003.prime_interval_nat_ladder_c05402 n (by omega) (by omega)
          · -- n <= 9668595030173831
            exact RamareSaouter2003.prime_interval_nat_ladder_c05401 n (by omega) (by omega)
