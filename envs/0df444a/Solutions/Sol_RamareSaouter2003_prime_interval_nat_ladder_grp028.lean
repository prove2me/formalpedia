-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp028
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T06:53:24.069496+00:00
-- url     : https://prove2.me/submissions/0e42bd71-0e85-404a-81fd-5be5360ee7b9

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01374
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01394
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01400

theorem solution (n : Nat)
    (hn : 242864356649 < n) (hupper : n <= 275326001903) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 258581578919 n with h2 | h2
  · -- n > 258581578919
    rcases Nat.lt_or_ge 266486636137 n with h4 | h4
    · -- n > 266486636137
      rcases Nat.lt_or_ge 270530185279 n with h6 | h6
      · -- n > 270530185279
        rcases Nat.lt_or_ge 272575124999 n with h8 | h8
        · -- n > 272575124999
          rcases Nat.lt_or_ge 273947078569 n with h10 | h10
          · -- n > 273947078569
            rcases Nat.lt_or_ge 274635666797 n with h12 | h12
            · -- n > 274635666797
              exact RamareSaouter2003.prime_interval_nat_ladder_c01400 n (by omega) (by omega)
            · -- n <= 274635666797
              exact RamareSaouter2003.prime_interval_nat_ladder_c01399 n (by omega) (by omega)
          · -- n <= 273947078569
            rcases Nat.lt_or_ge 273260232811 n with h12 | h12
            · -- n > 273260232811
              exact RamareSaouter2003.prime_interval_nat_ladder_c01398 n (by omega) (by omega)
            · -- n <= 273260232811
              exact RamareSaouter2003.prime_interval_nat_ladder_c01397 n (by omega) (by omega)
        · -- n <= 272575124999
          rcases Nat.lt_or_ge 271210105667 n with h10 | h10
          · -- n > 271210105667
            rcases Nat.lt_or_ge 271891750769 n with h12 | h12
            · -- n > 271891750769
              exact RamareSaouter2003.prime_interval_nat_ladder_c01396 n (by omega) (by omega)
            · -- n <= 271891750769
              exact RamareSaouter2003.prime_interval_nat_ladder_c01395 n (by omega) (by omega)
          · -- n <= 271210105667
            exact RamareSaouter2003.prime_interval_nat_ladder_c01394 n (by omega) (by omega)
      · -- n <= 270530185279
        rcases Nat.lt_or_ge 268500728437 n with h8 | h8
        · -- n > 268500728437
          rcases Nat.lt_or_ge 269175501053 n with h10 | h10
          · -- n > 269175501053
            rcases Nat.lt_or_ge 269851985243 n with h12 | h12
            · -- n > 269851985243
              exact RamareSaouter2003.prime_interval_nat_ladder_c01393 n (by omega) (by omega)
            · -- n <= 269851985243
              exact RamareSaouter2003.prime_interval_nat_ladder_c01392 n (by omega) (by omega)
          · -- n <= 269175501053
            exact RamareSaouter2003.prime_interval_nat_ladder_c01391 n (by omega) (by omega)
        · -- n <= 268500728437
          rcases Nat.lt_or_ge 267156300319 n with h10 | h10
          · -- n > 267156300319
            rcases Nat.lt_or_ge 267827662957 n with h12 | h12
            · -- n > 267827662957
              exact RamareSaouter2003.prime_interval_nat_ladder_c01390 n (by omega) (by omega)
            · -- n <= 267827662957
              exact RamareSaouter2003.prime_interval_nat_ladder_c01389 n (by omega) (by omega)
          · -- n <= 267156300319
            exact RamareSaouter2003.prime_interval_nat_ladder_c01388 n (by omega) (by omega)
    · -- n <= 266486636137
      rcases Nat.lt_or_ge 262504076717 n with h6 | h6
      · -- n > 262504076717
        rcases Nat.lt_or_ge 264487790981 n with h8 | h8
        · -- n > 264487790981
          rcases Nat.lt_or_ge 265152385787 n with h10 | h10
          · -- n > 265152385787
            rcases Nat.lt_or_ge 265818666077 n with h12 | h12
            · -- n > 265818666077
              exact RamareSaouter2003.prime_interval_nat_ladder_c01387 n (by omega) (by omega)
            · -- n <= 265818666077
              exact RamareSaouter2003.prime_interval_nat_ladder_c01386 n (by omega) (by omega)
          · -- n <= 265152385787
            exact RamareSaouter2003.prime_interval_nat_ladder_c01385 n (by omega) (by omega)
        · -- n <= 264487790981
          rcases Nat.lt_or_ge 263163640783 n with h10 | h10
          · -- n > 263163640783
            rcases Nat.lt_or_ge 263824877413 n with h12 | h12
            · -- n > 263824877413
              exact RamareSaouter2003.prime_interval_nat_ladder_c01384 n (by omega) (by omega)
            · -- n <= 263824877413
              exact RamareSaouter2003.prime_interval_nat_ladder_c01383 n (by omega) (by omega)
          · -- n <= 263163640783
            exact RamareSaouter2003.prime_interval_nat_ladder_c01382 n (by omega) (by omega)
      · -- n <= 262504076717
        rcases Nat.lt_or_ge 260535377549 n with h8 | h8
        · -- n > 260535377549
          rcases Nat.lt_or_ge 261189949357 n with h10 | h10
          · -- n > 261189949357
            rcases Nat.lt_or_ge 261846180977 n with h12 | h12
            · -- n > 261846180977
              exact RamareSaouter2003.prime_interval_nat_ladder_c01381 n (by omega) (by omega)
            · -- n <= 261846180977
              exact RamareSaouter2003.prime_interval_nat_ladder_c01380 n (by omega) (by omega)
          · -- n <= 261189949357
            exact RamareSaouter2003.prime_interval_nat_ladder_c01379 n (by omega) (by omega)
        · -- n <= 260535377549
          rcases Nat.lt_or_ge 259231196617 n with h10 | h10
          · -- n > 259231196617
            rcases Nat.lt_or_ge 259882461343 n with h12 | h12
            · -- n > 259882461343
              exact RamareSaouter2003.prime_interval_nat_ladder_c01378 n (by omega) (by omega)
            · -- n <= 259882461343
              exact RamareSaouter2003.prime_interval_nat_ladder_c01377 n (by omega) (by omega)
          · -- n <= 259231196617
            exact RamareSaouter2003.prime_interval_nat_ladder_c01376 n (by omega) (by omega)
  · -- n <= 258581578919
    rcases Nat.lt_or_ge 250284542887 n with h4 | h4
    · -- n > 250284542887
      rcases Nat.lt_or_ge 254080023919 n with h6 | h6
      · -- n > 254080023919
        rcases Nat.lt_or_ge 255999495889 n with h8 | h8
        · -- n > 255999495889
          rcases Nat.lt_or_ge 257287268197 n with h10 | h10
          · -- n > 257287268197
            rcases Nat.lt_or_ge 257933604179 n with h12 | h12
            · -- n > 257933604179
              exact RamareSaouter2003.prime_interval_nat_ladder_c01375 n (by omega) (by omega)
            · -- n <= 257933604179
              exact RamareSaouter2003.prime_interval_nat_ladder_c01374 n (by omega) (by omega)
          · -- n <= 257287268197
            rcases Nat.lt_or_ge 256642566827 n with h12 | h12
            · -- n > 256642566827
              exact RamareSaouter2003.prime_interval_nat_ladder_c01373 n (by omega) (by omega)
            · -- n <= 256642566827
              exact RamareSaouter2003.prime_interval_nat_ladder_c01372 n (by omega) (by omega)
        · -- n <= 255999495889
          rcases Nat.lt_or_ge 254718228577 n with h10 | h10
          · -- n > 254718228577
            rcases Nat.lt_or_ge 255358051177 n with h12 | h12
            · -- n > 255358051177
              exact RamareSaouter2003.prime_interval_nat_ladder_c01371 n (by omega) (by omega)
            · -- n <= 255358051177
              exact RamareSaouter2003.prime_interval_nat_ladder_c01370 n (by omega) (by omega)
          · -- n <= 254718228577
            exact RamareSaouter2003.prime_interval_nat_ladder_c01369 n (by omega) (by omega)
      · -- n <= 254080023919
        rcases Nat.lt_or_ge 252175076513 n with h8 | h8
        · -- n > 252175076513
          rcases Nat.lt_or_ge 252808451957 n with h10 | h10
          · -- n > 252808451957
            rcases Nat.lt_or_ge 253443433073 n with h12 | h12
            · -- n > 253443433073
              exact RamareSaouter2003.prime_interval_nat_ladder_c01368 n (by omega) (by omega)
            · -- n <= 253443433073
              exact RamareSaouter2003.prime_interval_nat_ladder_c01367 n (by omega) (by omega)
          · -- n <= 252808451957
            exact RamareSaouter2003.prime_interval_nat_ladder_c01366 n (by omega) (by omega)
        · -- n <= 252175076513
          rcases Nat.lt_or_ge 250913126089 n with h10 | h10
          · -- n > 250913126089
            rcases Nat.lt_or_ge 251543302499 n with h12 | h12
            · -- n > 251543302499
              exact RamareSaouter2003.prime_interval_nat_ladder_c01365 n (by omega) (by omega)
            · -- n <= 251543302499
              exact RamareSaouter2003.prime_interval_nat_ladder_c01364 n (by omega) (by omega)
          · -- n <= 250913126089
            exact RamareSaouter2003.prime_interval_nat_ladder_c01363 n (by omega) (by omega)
    · -- n <= 250284542887
      rcases Nat.lt_or_ge 246546277157 n with h6 | h6
      · -- n > 246546277157
        rcases Nat.lt_or_ge 248408312857 n with h8 | h8
        · -- n > 248408312857
          rcases Nat.lt_or_ge 249032140321 n with h10 | h10
          · -- n > 249032140321
            rcases Nat.lt_or_ge 249657548977 n with h12 | h12
            · -- n > 249657548977
              exact RamareSaouter2003.prime_interval_nat_ladder_c01362 n (by omega) (by omega)
            · -- n <= 249657548977
              exact RamareSaouter2003.prime_interval_nat_ladder_c01361 n (by omega) (by omega)
          · -- n <= 249032140321
            exact RamareSaouter2003.prime_interval_nat_ladder_c01360 n (by omega) (by omega)
        · -- n <= 248408312857
          rcases Nat.lt_or_ge 247165385303 n with h10 | h10
          · -- n > 247165385303
            rcases Nat.lt_or_ge 247786062463 n with h12 | h12
            · -- n > 247786062463
              exact RamareSaouter2003.prime_interval_nat_ladder_c01359 n (by omega) (by omega)
            · -- n <= 247786062463
              exact RamareSaouter2003.prime_interval_nat_ladder_c01358 n (by omega) (by omega)
          · -- n <= 247165385303
            exact RamareSaouter2003.prime_interval_nat_ladder_c01357 n (by omega) (by omega)
      · -- n <= 246546277157
        rcases Nat.lt_or_ge 244698327571 n with h8 | h8
        · -- n > 244698327571
          rcases Nat.lt_or_ge 245312752337 n with h10 | h10
          · -- n > 245312752337
            rcases Nat.lt_or_ge 245928734243 n with h12 | h12
            · -- n > 245928734243
              exact RamareSaouter2003.prime_interval_nat_ladder_c01356 n (by omega) (by omega)
            · -- n <= 245928734243
              exact RamareSaouter2003.prime_interval_nat_ladder_c01355 n (by omega) (by omega)
          · -- n <= 245312752337
            exact RamareSaouter2003.prime_interval_nat_ladder_c01354 n (by omega) (by omega)
        · -- n <= 244698327571
          rcases Nat.lt_or_ge 243474133571 n with h10 | h10
          · -- n > 243474133571
            rcases Nat.lt_or_ge 244085455973 n with h12 | h12
            · -- n > 244085455973
              exact RamareSaouter2003.prime_interval_nat_ladder_c01353 n (by omega) (by omega)
            · -- n <= 244085455973
              exact RamareSaouter2003.prime_interval_nat_ladder_c01352 n (by omega) (by omega)
          · -- n <= 243474133571
            exact RamareSaouter2003.prime_interval_nat_ladder_c01351 n (by omega) (by omega)
