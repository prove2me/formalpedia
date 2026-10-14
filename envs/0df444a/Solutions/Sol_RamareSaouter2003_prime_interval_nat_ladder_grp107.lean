-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp107
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T15:56:07.06246+00:00
-- url     : https://prove2.me/submissions/dfe437da-d016-437f-a52a-9846e9dfe3f1

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05325
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05345
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05350

theorem solution (n : Nat)
    (hn : 7267171176941339 < n) (hupper : n <= 8370471890560501) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 7799334766070051 n with h2 | h2
  · -- n > 7799334766070051
    rcases Nat.lt_or_ge 8068440489872759 n with h4 | h4
    · -- n > 8068440489872759
      rcases Nat.lt_or_ge 8206467868156021 n with h6 | h6
      · -- n > 8206467868156021
        rcases Nat.lt_or_ge 8276366042222857 n with h8 | h8
        · -- n > 8276366042222857
          rcases Nat.lt_or_ge 8323289153240647 n with h10 | h10
          · -- n > 8323289153240647
            rcases Nat.lt_or_ge 8346846219824267 n with h12 | h12
            · -- n > 8346846219824267
              exact RamareSaouter2003.prime_interval_nat_ladder_c05350 n (by omega) (by omega)
            · -- n <= 8346846219824267
              exact RamareSaouter2003.prime_interval_nat_ladder_c05349 n (by omega) (by omega)
          · -- n <= 8323289153240647
            rcases Nat.lt_or_ge 8299793973225493 n with h12 | h12
            · -- n > 8299793973225493
              exact RamareSaouter2003.prime_interval_nat_ladder_c05348 n (by omega) (by omega)
            · -- n <= 8299793973225493
              exact RamareSaouter2003.prime_interval_nat_ladder_c05347 n (by omega) (by omega)
        · -- n <= 8276366042222857
          rcases Nat.lt_or_ge 8229702030850693 n with h10 | h10
          · -- n > 8229702030850693
            rcases Nat.lt_or_ge 8253000279829183 n with h12 | h12
            · -- n > 8253000279829183
              exact RamareSaouter2003.prime_interval_nat_ladder_c05346 n (by omega) (by omega)
            · -- n <= 8253000279829183
              exact RamareSaouter2003.prime_interval_nat_ladder_c05345 n (by omega) (by omega)
          · -- n <= 8229702030850693
            exact RamareSaouter2003.prime_interval_nat_ladder_c05344 n (by omega) (by omega)
      · -- n <= 8206467868156021
        rcases Nat.lt_or_ge 8137164874285207 n with h8 | h8
        · -- n > 8137164874285207
          rcases Nat.lt_or_ge 8160196903006139 n with h10 | h10
          · -- n > 8160196903006139
            rcases Nat.lt_or_ge 8183300385776387 n with h12 | h12
            · -- n > 8183300385776387
              exact RamareSaouter2003.prime_interval_nat_ladder_c05343 n (by omega) (by omega)
            · -- n <= 8183300385776387
              exact RamareSaouter2003.prime_interval_nat_ladder_c05342 n (by omega) (by omega)
          · -- n <= 8160196903006139
            exact RamareSaouter2003.prime_interval_nat_ladder_c05341 n (by omega) (by omega)
        · -- n <= 8137164874285207
          rcases Nat.lt_or_ge 8091283553409571 n with h10 | h10
          · -- n > 8091283553409571
            rcases Nat.lt_or_ge 8114192051388751 n with h12 | h12
            · -- n > 8114192051388751
              exact RamareSaouter2003.prime_interval_nat_ladder_c05340 n (by omega) (by omega)
            · -- n <= 8114192051388751
              exact RamareSaouter2003.prime_interval_nat_ladder_c05339 n (by omega) (by omega)
          · -- n <= 8091283553409571
            exact RamareSaouter2003.prime_interval_nat_ladder_c05338 n (by omega) (by omega)
    · -- n <= 8068440489872759
      rcases Nat.lt_or_ge 7932733361972021 n with h6 | h6
      · -- n > 7932733361972021
        rcases Nat.lt_or_ge 8000300210739383 n with h8 | h8
        · -- n > 8000300210739383
          rcases Nat.lt_or_ge 8022949226342381 n with h10 | h10
          · -- n > 8022949226342381
            rcases Nat.lt_or_ge 8045662366754017 n with h12 | h12
            · -- n > 8045662366754017
              exact RamareSaouter2003.prime_interval_nat_ladder_c05337 n (by omega) (by omega)
            · -- n <= 8045662366754017
              exact RamareSaouter2003.prime_interval_nat_ladder_c05336 n (by omega) (by omega)
          · -- n <= 8022949226342381
            exact RamareSaouter2003.prime_interval_nat_ladder_c05335 n (by omega) (by omega)
        · -- n <= 8000300210739383
          rcases Nat.lt_or_ge 7955190628224283 n with h10 | h10
          · -- n > 7955190628224283
            rcases Nat.lt_or_ge 7977713044187401 n with h12 | h12
            · -- n > 7977713044187401
              exact RamareSaouter2003.prime_interval_nat_ladder_c05334 n (by omega) (by omega)
            · -- n <= 7977713044187401
              exact RamareSaouter2003.prime_interval_nat_ladder_c05333 n (by omega) (by omega)
          · -- n <= 7955190628224283
            exact RamareSaouter2003.prime_interval_nat_ladder_c05332 n (by omega) (by omega)
      · -- n <= 7932733361972021
        rcases Nat.lt_or_ge 7865752269378967 n with h8 | h8
        · -- n > 7865752269378967
          rcases Nat.lt_or_ge 7888015478825441 n with h10 | h10
          · -- n > 7888015478825441
            rcases Nat.lt_or_ge 7910338962213917 n with h12 | h12
            · -- n > 7910338962213917
              exact RamareSaouter2003.prime_interval_nat_ladder_c05331 n (by omega) (by omega)
            · -- n <= 7910338962213917
              exact RamareSaouter2003.prime_interval_nat_ladder_c05330 n (by omega) (by omega)
          · -- n <= 7888015478825441
            exact RamareSaouter2003.prime_interval_nat_ladder_c05329 n (by omega) (by omega)
        · -- n <= 7865752269378967
          rcases Nat.lt_or_ge 7821415228585603 n with h10 | h10
          · -- n > 7821415228585603
            rcases Nat.lt_or_ge 7843557547534957 n with h12 | h12
            · -- n > 7843557547534957
              exact RamareSaouter2003.prime_interval_nat_ladder_c05328 n (by omega) (by omega)
            · -- n <= 7843557547534957
              exact RamareSaouter2003.prime_interval_nat_ladder_c05327 n (by omega) (by omega)
          · -- n <= 7821415228585603
            exact RamareSaouter2003.prime_interval_nat_ladder_c05326 n (by omega) (by omega)
  · -- n <= 7799334766070051
    rcases Nat.lt_or_ge 7517917543688711 n with h4 | h4
    · -- n > 7517917543688711
      rcases Nat.lt_or_ge 7646522661708023 n with h6 | h6
      · -- n > 7646522661708023
        rcases Nat.lt_or_ge 7711639930109831 n with h8 | h8
        · -- n > 7711639930109831
          rcases Nat.lt_or_ge 7755364699570591 n with h10 | h10
          · -- n > 7755364699570591
            rcases Nat.lt_or_ge 7777319911512449 n with h12 | h12
            · -- n > 7777319911512449
              exact RamareSaouter2003.prime_interval_nat_ladder_c05325 n (by omega) (by omega)
            · -- n <= 7777319911512449
              exact RamareSaouter2003.prime_interval_nat_ladder_c05324 n (by omega) (by omega)
          · -- n <= 7755364699570591
            rcases Nat.lt_or_ge 7733472710677261 n with h12 | h12
            · -- n > 7733472710677261
              exact RamareSaouter2003.prime_interval_nat_ladder_c05323 n (by omega) (by omega)
            · -- n <= 7733472710677261
              exact RamareSaouter2003.prime_interval_nat_ladder_c05322 n (by omega) (by omega)
        · -- n <= 7711639930109831
          rcases Nat.lt_or_ge 7668170305292429 n with h10 | h10
          · -- n > 7668170305292429
            rcases Nat.lt_or_ge 7689880288456147 n with h12 | h12
            · -- n > 7689880288456147
              exact RamareSaouter2003.prime_interval_nat_ladder_c05321 n (by omega) (by omega)
            · -- n <= 7689880288456147
              exact RamareSaouter2003.prime_interval_nat_ladder_c05320 n (by omega) (by omega)
          · -- n <= 7668170305292429
            exact RamareSaouter2003.prime_interval_nat_ladder_c05319 n (by omega) (by omega)
      · -- n <= 7646522661708023
        rcases Nat.lt_or_ge 7581953853657853 n with h8 | h8
        · -- n > 7581953853657853
          rcases Nat.lt_or_ge 7603418235571447 n with h10 | h10
          · -- n > 7603418235571447
            rcases Nat.lt_or_ge 7624943171875753 n with h12 | h12
            · -- n > 7624943171875753
              exact RamareSaouter2003.prime_interval_nat_ladder_c05318 n (by omega) (by omega)
            · -- n <= 7624943171875753
              exact RamareSaouter2003.prime_interval_nat_ladder_c05317 n (by omega) (by omega)
          · -- n <= 7603418235571447
            exact RamareSaouter2003.prime_interval_nat_ladder_c05316 n (by omega) (by omega)
        · -- n <= 7581953853657853
          rcases Nat.lt_or_ge 7539202938721189 n with h10 | h10
          · -- n > 7539202938721189
            rcases Nat.lt_or_ge 7560548156991811 n with h12 | h12
            · -- n > 7560548156991811
              exact RamareSaouter2003.prime_interval_nat_ladder_c05315 n (by omega) (by omega)
            · -- n <= 7560548156991811
              exact RamareSaouter2003.prime_interval_nat_ladder_c05314 n (by omega) (by omega)
          · -- n <= 7539202938721189
            exact RamareSaouter2003.prime_interval_nat_ladder_c05313 n (by omega) (by omega)
    · -- n <= 7517917543688711
      rcases Nat.lt_or_ge 7391488225971191 n with h6 | h6
      · -- n > 7391488225971191
        rcases Nat.lt_or_ge 7454428044719801 n with h8 | h8
        · -- n > 7454428044719801
          rcases Nat.lt_or_ge 7475533518386873 n with h10 | h10
          · -- n > 7475533518386873
            rcases Nat.lt_or_ge 7496694101823187 n with h12 | h12
            · -- n > 7496694101823187
              exact RamareSaouter2003.prime_interval_nat_ladder_c05312 n (by omega) (by omega)
            · -- n <= 7496694101823187
              exact RamareSaouter2003.prime_interval_nat_ladder_c05311 n (by omega) (by omega)
          · -- n <= 7475533518386873
            exact RamareSaouter2003.prime_interval_nat_ladder_c05310 n (by omega) (by omega)
        · -- n <= 7454428044719801
          rcases Nat.lt_or_ge 7412415789183833 n with h10 | h10
          · -- n > 7412415789183833
            rcases Nat.lt_or_ge 7433397590900669 n with h12 | h12
            · -- n > 7433397590900669
              exact RamareSaouter2003.prime_interval_nat_ladder_c05309 n (by omega) (by omega)
            · -- n <= 7433397590900669
              exact RamareSaouter2003.prime_interval_nat_ladder_c05308 n (by omega) (by omega)
          · -- n <= 7412415789183833
            exact RamareSaouter2003.prime_interval_nat_ladder_c05307 n (by omega) (by omega)
      · -- n <= 7391488225971191
        rcases Nat.lt_or_ge 7329065731044697 n with h8 | h8
        · -- n > 7329065731044697
          rcases Nat.lt_or_ge 7349814436045349 n with h10 | h10
          · -- n > 7349814436045349
            rcases Nat.lt_or_ge 7370620122091313 n with h12 | h12
            · -- n > 7370620122091313
              exact RamareSaouter2003.prime_interval_nat_ladder_c05306 n (by omega) (by omega)
            · -- n <= 7370620122091313
              exact RamareSaouter2003.prime_interval_nat_ladder_c05305 n (by omega) (by omega)
          · -- n <= 7349814436045349
            exact RamareSaouter2003.prime_interval_nat_ladder_c05304 n (by omega) (by omega)
        · -- n <= 7329065731044697
          rcases Nat.lt_or_ge 7287746446201561 n with h10 | h10
          · -- n > 7287746446201561
            rcases Nat.lt_or_ge 7308375243531893 n with h12 | h12
            · -- n > 7308375243531893
              exact RamareSaouter2003.prime_interval_nat_ladder_c05303 n (by omega) (by omega)
            · -- n <= 7308375243531893
              exact RamareSaouter2003.prime_interval_nat_ladder_c05302 n (by omega) (by omega)
          · -- n <= 7287746446201561
            exact RamareSaouter2003.prime_interval_nat_ladder_c05301 n (by omega) (by omega)
