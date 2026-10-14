-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp088
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T10:30:55.122517+00:00
-- url     : https://prove2.me/submissions/6906bbd2-abfc-49f9-9016-99d9660a3946

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04374
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04394
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04400

theorem solution (n : Nat)
    (hn : 495672413417261 < n) (hupper : n <= 570899461905341) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 531953658135623 n with h2 | h2
  · -- n > 531953658135623
    rcases Nat.lt_or_ge 550303031679131 n with h4 | h4
    · -- n > 550303031679131
      rcases Nat.lt_or_ge 559715704451741 n with h6 | h6
      · -- n > 559715704451741
        rcases Nat.lt_or_ge 564482407585933 n with h8 | h8
        · -- n > 564482407585933
          rcases Nat.lt_or_ge 567680968745881 n with h10 | h10
          · -- n > 567680968745881
            rcases Nat.lt_or_ge 569288075855077 n with h12 | h12
            · -- n > 569288075855077
              exact RamareSaouter2003.prime_interval_nat_ladder_c04400 n (by omega) (by omega)
            · -- n <= 569288075855077
              exact RamareSaouter2003.prime_interval_nat_ladder_c04399 n (by omega) (by omega)
          · -- n <= 567680968745881
            rcases Nat.lt_or_ge 566079701595977 n with h12 | h12
            · -- n > 566079701595977
              exact RamareSaouter2003.prime_interval_nat_ladder_c04398 n (by omega) (by omega)
            · -- n <= 566079701595977
              exact RamareSaouter2003.prime_interval_nat_ladder_c04397 n (by omega) (by omega)
        · -- n <= 564482407585933
          rcases Nat.lt_or_ge 561300322398889 n with h10 | h10
          · -- n > 561300322398889
            rcases Nat.lt_or_ge 562888839941273 n with h12 | h12
            · -- n > 562888839941273
              exact RamareSaouter2003.prime_interval_nat_ladder_c04396 n (by omega) (by omega)
            · -- n <= 562888839941273
              exact RamareSaouter2003.prime_interval_nat_ladder_c04395 n (by omega) (by omega)
          · -- n <= 561300322398889
            exact RamareSaouter2003.prime_interval_nat_ladder_c04394 n (by omega) (by omega)
      · -- n <= 559715704451741
        rcases Nat.lt_or_ge 554989472879297 n with h8 | h8
        · -- n > 554989472879297
          rcases Nat.lt_or_ge 556560266116147 n with h10 | h10
          · -- n > 556560266116147
            rcases Nat.lt_or_ge 558135831231397 n with h12 | h12
            · -- n > 558135831231397
              exact RamareSaouter2003.prime_interval_nat_ladder_c04393 n (by omega) (by omega)
            · -- n <= 558135831231397
              exact RamareSaouter2003.prime_interval_nat_ladder_c04392 n (by omega) (by omega)
          · -- n <= 556560266116147
            exact RamareSaouter2003.prime_interval_nat_ladder_c04391 n (by omega) (by omega)
        · -- n <= 554989472879297
          rcases Nat.lt_or_ge 551861027927879 n with h10 | h10
          · -- n > 551861027927879
            rcases Nat.lt_or_ge 553422874570669 n with h12 | h12
            · -- n > 553422874570669
              exact RamareSaouter2003.prime_interval_nat_ladder_c04390 n (by omega) (by omega)
            · -- n <= 553422874570669
              exact RamareSaouter2003.prime_interval_nat_ladder_c04389 n (by omega) (by omega)
          · -- n <= 551861027927879
            exact RamareSaouter2003.prime_interval_nat_ladder_c04388 n (by omega) (by omega)
    · -- n <= 550303031679131
      rcases Nat.lt_or_ge 541050562157983 n with h6 | h6
      · -- n > 541050562157983
        rcases Nat.lt_or_ge 545656455753587 n with h8 | h8
        · -- n > 545656455753587
          rcases Nat.lt_or_ge 547201316367227 n with h10 | h10
          · -- n > 547201316367227
            rcases Nat.lt_or_ge 548749578490307 n with h12 | h12
            · -- n > 548749578490307
              exact RamareSaouter2003.prime_interval_nat_ladder_c04387 n (by omega) (by omega)
            · -- n <= 548749578490307
              exact RamareSaouter2003.prime_interval_nat_ladder_c04386 n (by omega) (by omega)
          · -- n <= 547201316367227
            exact RamareSaouter2003.prime_interval_nat_ladder_c04385 n (by omega) (by omega)
        · -- n <= 545656455753587
          rcases Nat.lt_or_ge 542581298806597 n with h10 | h10
          · -- n > 542581298806597
            rcases Nat.lt_or_ge 544116345099181 n with h12 | h12
            · -- n > 544116345099181
              exact RamareSaouter2003.prime_interval_nat_ladder_c04384 n (by omega) (by omega)
            · -- n <= 544116345099181
              exact RamareSaouter2003.prime_interval_nat_ladder_c04383 n (by omega) (by omega)
          · -- n <= 542581298806597
            exact RamareSaouter2003.prime_interval_nat_ladder_c04382 n (by omega) (by omega)
      · -- n <= 541050562157983
        rcases Nat.lt_or_ge 536482068625421 n with h8 | h8
        · -- n > 536482068625421
          rcases Nat.lt_or_ge 538000537383191 n with h10 | h10
          · -- n > 538000537383191
            rcases Nat.lt_or_ge 539523194500273 n with h12 | h12
            · -- n > 539523194500273
              exact RamareSaouter2003.prime_interval_nat_ladder_c04381 n (by omega) (by omega)
            · -- n <= 539523194500273
              exact RamareSaouter2003.prime_interval_nat_ladder_c04380 n (by omega) (by omega)
          · -- n <= 538000537383191
            exact RamareSaouter2003.prime_interval_nat_ladder_c04379 n (by omega) (by omega)
        · -- n <= 536482068625421
          rcases Nat.lt_or_ge 533459240936059 n with h10 | h10
          · -- n > 533459240936059
            rcases Nat.lt_or_ge 534969310238533 n with h12 | h12
            · -- n > 534969310238533
              exact RamareSaouter2003.prime_interval_nat_ladder_c04378 n (by omega) (by omega)
            · -- n <= 534969310238533
              exact RamareSaouter2003.prime_interval_nat_ladder_c04377 n (by omega) (by omega)
          · -- n <= 533459240936059
            exact RamareSaouter2003.prime_interval_nat_ladder_c04376 n (by omega) (by omega)
  · -- n <= 531953658135623
    rcases Nat.lt_or_ge 512768019458039 n with h4 | h4
    · -- n > 512768019458039
      rcases Nat.lt_or_ge 521537046598901 n with h6 | h6
      · -- n > 521537046598901
        rcases Nat.lt_or_ge 525975126250339 n with h8 | h8
        · -- n > 525975126250339
          rcases Nat.lt_or_ge 528956144651059 n with h10 | h10
          · -- n > 528956144651059
            rcases Nat.lt_or_ge 530453475433657 n with h12 | h12
            · -- n > 530453475433657
              exact RamareSaouter2003.prime_interval_nat_ladder_c04375 n (by omega) (by omega)
            · -- n <= 530453475433657
              exact RamareSaouter2003.prime_interval_nat_ladder_c04374 n (by omega) (by omega)
          · -- n <= 528956144651059
            rcases Nat.lt_or_ge 527464008465787 n with h12 | h12
            · -- n > 527464008465787
              exact RamareSaouter2003.prime_interval_nat_ladder_c04373 n (by omega) (by omega)
            · -- n <= 527464008465787
              exact RamareSaouter2003.prime_interval_nat_ladder_c04372 n (by omega) (by omega)
        · -- n <= 525975126250339
          rcases Nat.lt_or_ge 523013556459767 n with h10 | h10
          · -- n > 523013556459767
            rcases Nat.lt_or_ge 524491325464507 n with h12 | h12
            · -- n > 524491325464507
              exact RamareSaouter2003.prime_interval_nat_ladder_c04371 n (by omega) (by omega)
            · -- n <= 524491325464507
              exact RamareSaouter2003.prime_interval_nat_ladder_c04370 n (by omega) (by omega)
          · -- n <= 523013556459767
            exact RamareSaouter2003.prime_interval_nat_ladder_c04369 n (by omega) (by omega)
      · -- n <= 521537046598901
        rcases Nat.lt_or_ge 517134872683757 n with h8 | h8
        · -- n > 517134872683757
          rcases Nat.lt_or_ge 518597944044743 n with h10 | h10
          · -- n > 518597944044743
            rcases Nat.lt_or_ge 520065226139231 n with h12 | h12
            · -- n > 520065226139231
              exact RamareSaouter2003.prime_interval_nat_ladder_c04368 n (by omega) (by omega)
            · -- n <= 520065226139231
              exact RamareSaouter2003.prime_interval_nat_ladder_c04367 n (by omega) (by omega)
          · -- n <= 518597944044743
            exact RamareSaouter2003.prime_interval_nat_ladder_c04366 n (by omega) (by omega)
        · -- n <= 517134872683757
          rcases Nat.lt_or_ge 514219690754051 n with h10 | h10
          · -- n > 514219690754051
            rcases Nat.lt_or_ge 515675001904787 n with h12 | h12
            · -- n > 515675001904787
              exact RamareSaouter2003.prime_interval_nat_ladder_c04365 n (by omega) (by omega)
            · -- n <= 515675001904787
              exact RamareSaouter2003.prime_interval_nat_ladder_c04364 n (by omega) (by omega)
          · -- n <= 514219690754051
            exact RamareSaouter2003.prime_interval_nat_ladder_c04363 n (by omega) (by omega)
    · -- n <= 512768019458039
      rcases Nat.lt_or_ge 504146758701121 n with h6 | h6
      · -- n > 504146758701121
        rcases Nat.lt_or_ge 508439659978511 n with h8 | h8
        · -- n > 508439659978511
          rcases Nat.lt_or_ge 509878016686037 n with h10 | h10
          · -- n > 509878016686037
            rcases Nat.lt_or_ge 511320437088953 n with h12 | h12
            · -- n > 511320437088953
              exact RamareSaouter2003.prime_interval_nat_ladder_c04362 n (by omega) (by omega)
            · -- n <= 511320437088953
              exact RamareSaouter2003.prime_interval_nat_ladder_c04361 n (by omega) (by omega)
          · -- n <= 509878016686037
            exact RamareSaouter2003.prime_interval_nat_ladder_c04360 n (by omega) (by omega)
        · -- n <= 508439659978511
          rcases Nat.lt_or_ge 505573725917959 n with h10 | h10
          · -- n > 505573725917959
            rcases Nat.lt_or_ge 507004826093569 n with h12 | h12
            · -- n > 507004826093569
              exact RamareSaouter2003.prime_interval_nat_ladder_c04359 n (by omega) (by omega)
            · -- n <= 507004826093569
              exact RamareSaouter2003.prime_interval_nat_ladder_c04358 n (by omega) (by omega)
          · -- n <= 505573725917959
            exact RamareSaouter2003.prime_interval_nat_ladder_c04357 n (by omega) (by omega)
      · -- n <= 504146758701121
        rcases Nat.lt_or_ge 499892580792551 n with h8 | h8
        · -- n > 499892580792551
          rcases Nat.lt_or_ge 501306980378663 n with h10 | h10
          · -- n > 501306980378663
            rcases Nat.lt_or_ge 502723601202247 n with h12 | h12
            · -- n > 502723601202247
              exact RamareSaouter2003.prime_interval_nat_ladder_c04356 n (by omega) (by omega)
            · -- n <= 502723601202247
              exact RamareSaouter2003.prime_interval_nat_ladder_c04355 n (by omega) (by omega)
          · -- n <= 501306980378663
            exact RamareSaouter2003.prime_interval_nat_ladder_c04354 n (by omega) (by omega)
        · -- n <= 499892580792551
          rcases Nat.lt_or_ge 497075795897699 n with h10 | h10
          · -- n > 497075795897699
            rcases Nat.lt_or_ge 498481473318853 n with h12 | h12
            · -- n > 498481473318853
              exact RamareSaouter2003.prime_interval_nat_ladder_c04353 n (by omega) (by omega)
            · -- n <= 498481473318853
              exact RamareSaouter2003.prime_interval_nat_ladder_c04352 n (by omega) (by omega)
          · -- n <= 497075795897699
            exact RamareSaouter2003.prime_interval_nat_ladder_c04351 n (by omega) (by omega)
