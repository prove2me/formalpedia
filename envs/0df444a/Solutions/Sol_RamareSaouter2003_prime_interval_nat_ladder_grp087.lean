-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp087
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T10:14:46.240986+00:00
-- url     : https://prove2.me/submissions/a26746d8-652a-4460-9219-ea505cbd5e06

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04325
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04345
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04350

theorem solution (n : Nat)
    (hn : 430355186223233 < n) (hupper : n <= 495672413417261) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 461860020970853 n with h2 | h2
  · -- n > 461860020970853
    rcases Nat.lt_or_ge 477792481425577 n with h4 | h4
    · -- n > 477792481425577
      rcases Nat.lt_or_ge 485961335494501 n with h6 | h6
      · -- n > 485961335494501
        rcases Nat.lt_or_ge 490099887064867 n with h8 | h8
        · -- n > 490099887064867
          rcases Nat.lt_or_ge 492878616095737 n with h10 | h10
          · -- n > 492878616095737
            rcases Nat.lt_or_ge 494273905866779 n with h12 | h12
            · -- n > 494273905866779
              exact RamareSaouter2003.prime_interval_nat_ladder_c04350 n (by omega) (by omega)
            · -- n <= 494273905866779
              exact RamareSaouter2003.prime_interval_nat_ladder_c04349 n (by omega) (by omega)
          · -- n <= 492878616095737
            rcases Nat.lt_or_ge 491487204559927 n with h12 | h12
            · -- n > 491487204559927
              exact RamareSaouter2003.prime_interval_nat_ladder_c04348 n (by omega) (by omega)
            · -- n <= 491487204559927
              exact RamareSaouter2003.prime_interval_nat_ladder_c04347 n (by omega) (by omega)
        · -- n <= 490099887064867
          rcases Nat.lt_or_ge 487337225310263 n with h10 | h10
          · -- n > 487337225310263
            rcases Nat.lt_or_ge 488716695714571 n with h12 | h12
            · -- n > 488716695714571
              exact RamareSaouter2003.prime_interval_nat_ladder_c04346 n (by omega) (by omega)
            · -- n <= 488716695714571
              exact RamareSaouter2003.prime_interval_nat_ladder_c04345 n (by omega) (by omega)
          · -- n <= 487337225310263
            exact RamareSaouter2003.prime_interval_nat_ladder_c04344 n (by omega) (by omega)
      · -- n <= 485961335494501
        rcases Nat.lt_or_ge 481857627310663 n with h8 | h8
        · -- n > 481857627310663
          rcases Nat.lt_or_ge 483221633798149 n with h10 | h10
          · -- n > 483221633798149
            rcases Nat.lt_or_ge 484589415784819 n with h12 | h12
            · -- n > 484589415784819
              exact RamareSaouter2003.prime_interval_nat_ladder_c04343 n (by omega) (by omega)
            · -- n <= 484589415784819
              exact RamareSaouter2003.prime_interval_nat_ladder_c04342 n (by omega) (by omega)
          · -- n <= 483221633798149
            exact RamareSaouter2003.prime_interval_nat_ladder_c04341 n (by omega) (by omega)
        · -- n <= 481857627310663
          rcases Nat.lt_or_ge 479144989943267 n with h10 | h10
          · -- n > 479144989943267
            rcases Nat.lt_or_ge 480500505262289 n with h12 | h12
            · -- n > 480500505262289
              exact RamareSaouter2003.prime_interval_nat_ladder_c04340 n (by omega) (by omega)
            · -- n <= 480500505262289
              exact RamareSaouter2003.prime_interval_nat_ladder_c04339 n (by omega) (by omega)
          · -- n <= 479144989943267
            exact RamareSaouter2003.prime_interval_nat_ladder_c04338 n (by omega) (by omega)
    · -- n <= 477792481425577
      rcases Nat.lt_or_ge 469759752368911 n with h6 | h6
      · -- n > 469759752368911
        rcases Nat.lt_or_ge 473758309508987 n with h8 | h8
        · -- n > 473758309508987
          rcases Nat.lt_or_ge 475099565003237 n with h10 | h10
          · -- n > 475099565003237
            rcases Nat.lt_or_ge 476444154486407 n with h12 | h12
            · -- n > 476444154486407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04337 n (by omega) (by omega)
            · -- n <= 476444154486407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04336 n (by omega) (by omega)
          · -- n <= 475099565003237
            exact RamareSaouter2003.prime_interval_nat_ladder_c04335 n (by omega) (by omega)
        · -- n <= 473758309508987
          rcases Nat.lt_or_ge 471089564696831 n with h10 | h10
          · -- n > 471089564696831
            rcases Nat.lt_or_ge 472422212695261 n with h12 | h12
            · -- n > 472422212695261
              exact RamareSaouter2003.prime_interval_nat_ladder_c04334 n (by omega) (by omega)
            · -- n <= 472422212695261
              exact RamareSaouter2003.prime_interval_nat_ladder_c04333 n (by omega) (by omega)
          · -- n <= 471089564696831
            exact RamareSaouter2003.prime_interval_nat_ladder_c04332 n (by omega) (by omega)
      · -- n <= 469759752368911
        rcases Nat.lt_or_ge 465794023908019 n with h8 | h8
        · -- n > 465794023908019
          rcases Nat.lt_or_ge 467112293642833 n with h10 | h10
          · -- n > 467112293642833
            rcases Nat.lt_or_ge 468434113660753 n with h12 | h12
            · -- n > 468434113660753
              exact RamareSaouter2003.prime_interval_nat_ladder_c04331 n (by omega) (by omega)
            · -- n <= 468434113660753
              exact RamareSaouter2003.prime_interval_nat_ladder_c04330 n (by omega) (by omega)
          · -- n <= 467112293642833
            exact RamareSaouter2003.prime_interval_nat_ladder_c04329 n (by omega) (by omega)
        · -- n <= 465794023908019
          rcases Nat.lt_or_ge 463167678036731 n with h10 | h10
          · -- n > 463167678036731
            rcases Nat.lt_or_ge 464479040293883 n with h12 | h12
            · -- n > 464479040293883
              exact RamareSaouter2003.prime_interval_nat_ladder_c04328 n (by omega) (by omega)
            · -- n <= 464479040293883
              exact RamareSaouter2003.prime_interval_nat_ladder_c04327 n (by omega) (by omega)
          · -- n <= 463167678036731
            exact RamareSaouter2003.prime_interval_nat_ladder_c04326 n (by omega) (by omega)
  · -- n <= 461860020970853
    rcases Nat.lt_or_ge 445199611861451 n with h4 | h4
    · -- n > 445199611861451
      rcases Nat.lt_or_ge 452813579306419 n with h6 | h6
      · -- n > 452813579306419
        rcases Nat.lt_or_ge 456668386763807 n with h8 | h8
        · -- n > 456668386763807
          rcases Nat.lt_or_ge 459256462124527 n with h10 | h10
          · -- n > 459256462124527
            rcases Nat.lt_or_ge 460556700293407 n with h12 | h12
            · -- n > 460556700293407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04325 n (by omega) (by omega)
            · -- n <= 460556700293407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04324 n (by omega) (by omega)
          · -- n <= 459256462124527
            rcases Nat.lt_or_ge 457961147178079 n with h12 | h12
            · -- n > 457961147178079
              exact RamareSaouter2003.prime_interval_nat_ladder_c04323 n (by omega) (by omega)
            · -- n <= 457961147178079
              exact RamareSaouter2003.prime_interval_nat_ladder_c04322 n (by omega) (by omega)
        · -- n <= 456668386763807
          rcases Nat.lt_or_ge 454093716715277 n with h10 | h10
          · -- n > 454093716715277
            rcases Nat.lt_or_ge 455379331925033 n with h12 | h12
            · -- n > 455379331925033
              exact RamareSaouter2003.prime_interval_nat_ladder_c04321 n (by omega) (by omega)
            · -- n <= 455379331925033
              exact RamareSaouter2003.prime_interval_nat_ladder_c04320 n (by omega) (by omega)
          · -- n <= 454093716715277
            exact RamareSaouter2003.prime_interval_nat_ladder_c04319 n (by omega) (by omega)
      · -- n <= 452813579306419
        rcases Nat.lt_or_ge 448990284421213 n with h8 | h8
        · -- n > 448990284421213
          rcases Nat.lt_or_ge 450261401228173 n with h10 | h10
          · -- n > 450261401228173
            rcases Nat.lt_or_ge 451535846026141 n with h12 | h12
            · -- n > 451535846026141
              exact RamareSaouter2003.prime_interval_nat_ladder_c04318 n (by omega) (by omega)
            · -- n <= 451535846026141
              exact RamareSaouter2003.prime_interval_nat_ladder_c04317 n (by omega) (by omega)
          · -- n <= 450261401228173
            exact RamareSaouter2003.prime_interval_nat_ladder_c04316 n (by omega) (by omega)
        · -- n <= 448990284421213
          rcases Nat.lt_or_ge 446459736517343 n with h10 | h10
          · -- n > 446459736517343
            rcases Nat.lt_or_ge 447722867641759 n with h12 | h12
            · -- n > 447722867641759
              exact RamareSaouter2003.prime_interval_nat_ladder_c04315 n (by omega) (by omega)
            · -- n <= 447722867641759
              exact RamareSaouter2003.prime_interval_nat_ladder_c04314 n (by omega) (by omega)
          · -- n <= 446459736517343
            exact RamareSaouter2003.prime_interval_nat_ladder_c04313 n (by omega) (by omega)
    · -- n <= 445199611861451
      rcases Nat.lt_or_ge 437714889883129 n with h6 | h6
      · -- n > 437714889883129
        rcases Nat.lt_or_ge 441442155252517 n with h8 | h8
        · -- n > 441442155252517
          rcases Nat.lt_or_ge 442690261522417 n with h10 | h10
          · -- n > 442690261522417
            rcases Nat.lt_or_ge 443943503649871 n with h12 | h12
            · -- n > 443943503649871
              exact RamareSaouter2003.prime_interval_nat_ladder_c04312 n (by omega) (by omega)
            · -- n <= 443943503649871
              exact RamareSaouter2003.prime_interval_nat_ladder_c04311 n (by omega) (by omega)
          · -- n <= 442690261522417
            exact RamareSaouter2003.prime_interval_nat_ladder_c04310 n (by omega) (by omega)
        · -- n <= 441442155252517
          rcases Nat.lt_or_ge 438953739418169 n with h10 | h10
          · -- n > 438953739418169
            rcases Nat.lt_or_ge 440196270227737 n with h12 | h12
            · -- n > 440196270227737
              exact RamareSaouter2003.prime_interval_nat_ladder_c04309 n (by omega) (by omega)
            · -- n <= 440196270227737
              exact RamareSaouter2003.prime_interval_nat_ladder_c04308 n (by omega) (by omega)
          · -- n <= 438953739418169
            exact RamareSaouter2003.prime_interval_nat_ladder_c04307 n (by omega) (by omega)
      · -- n <= 437714889883129
        rcases Nat.lt_or_ge 434018842325293 n with h8 | h8
        · -- n > 434018842325293
          rcases Nat.lt_or_ge 435247614694733 n with h10 | h10
          · -- n > 435247614694733
            rcases Nat.lt_or_ge 436479210161947 n with h12 | h12
            · -- n > 436479210161947
              exact RamareSaouter2003.prime_interval_nat_ladder_c04306 n (by omega) (by omega)
            · -- n <= 436479210161947
              exact RamareSaouter2003.prime_interval_nat_ladder_c04305 n (by omega) (by omega)
          · -- n <= 435247614694733
            exact RamareSaouter2003.prime_interval_nat_ladder_c04304 n (by omega) (by omega)
        · -- n <= 434018842325293
          rcases Nat.lt_or_ge 431572989789437 n with h10 | h10
          · -- n > 431572989789437
            rcases Nat.lt_or_ge 432794719975133 n with h12 | h12
            · -- n > 432794719975133
              exact RamareSaouter2003.prime_interval_nat_ladder_c04303 n (by omega) (by omega)
            · -- n <= 432794719975133
              exact RamareSaouter2003.prime_interval_nat_ladder_c04302 n (by omega) (by omega)
          · -- n <= 431572989789437
            exact RamareSaouter2003.prime_interval_nat_ladder_c04301 n (by omega) (by omega)
