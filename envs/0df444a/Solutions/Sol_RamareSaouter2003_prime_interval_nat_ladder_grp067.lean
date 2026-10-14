-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp067
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T03:39:54.041528+00:00
-- url     : https://prove2.me/submissions/78d6055a-6641-4e47-b928-f5e446681824

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03325
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03345
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03350

theorem solution (n : Nat)
    (hn : 31852221937607 < n) (hupper : n <= 36042222348907) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 33882515628859 n with h2 | h2
  · -- n > 33882515628859
    rcases Nat.lt_or_ge 34902528159511 n with h4 | h4
    · -- n > 34902528159511
      rcases Nat.lt_or_ge 35423992363099 n with h6 | h6
      · -- n > 35423992363099
        rcases Nat.lt_or_ge 35687638847999 n with h8 | h8
        · -- n > 35687638847999
          rcases Nat.lt_or_ge 35864492390999 n with h10 | h10
          · -- n > 35864492390999
            rcases Nat.lt_or_ge 35953247547121 n with h12 | h12
            · -- n > 35953247547121
              exact RamareSaouter2003.prime_interval_nat_ladder_c03350 n (by omega) (by omega)
            · -- n <= 35953247547121
              exact RamareSaouter2003.prime_interval_nat_ladder_c03349 n (by omega) (by omega)
          · -- n <= 35864492390999
            rcases Nat.lt_or_ge 35775956338169 n with h12 | h12
            · -- n > 35775956338169
              exact RamareSaouter2003.prime_interval_nat_ladder_c03348 n (by omega) (by omega)
            · -- n <= 35775956338169
              exact RamareSaouter2003.prime_interval_nat_ladder_c03347 n (by omega) (by omega)
        · -- n <= 35687638847999
          rcases Nat.lt_or_ge 35511657397901 n with h10 | h10
          · -- n > 35511657397901
            rcases Nat.lt_or_ge 35599539380599 n with h12 | h12
            · -- n > 35599539380599
              exact RamareSaouter2003.prime_interval_nat_ladder_c03346 n (by omega) (by omega)
            · -- n <= 35599539380599
              exact RamareSaouter2003.prime_interval_nat_ladder_c03345 n (by omega) (by omega)
          · -- n <= 35511657397901
            exact RamareSaouter2003.prime_interval_nat_ladder_c03344 n (by omega) (by omega)
      · -- n <= 35423992363099
        rcases Nat.lt_or_ge 35162293596751 n with h8 | h8
        · -- n > 35162293596751
          rcases Nat.lt_or_ge 35249310996049 n with h10 | h10
          · -- n > 35249310996049
            rcases Nat.lt_or_ge 35336543740523 n with h12 | h12
            · -- n > 35336543740523
              exact RamareSaouter2003.prime_interval_nat_ladder_c03343 n (by omega) (by omega)
            · -- n <= 35336543740523
              exact RamareSaouter2003.prime_interval_nat_ladder_c03342 n (by omega) (by omega)
          · -- n <= 35249310996049
            exact RamareSaouter2003.prime_interval_nat_ladder_c03341 n (by omega) (by omega)
        · -- n <= 35162293596751
          rcases Nat.lt_or_ge 34988902708037 n with h10 | h10
          · -- n > 34988902708037
            rcases Nat.lt_or_ge 35075491010773 n with h12 | h12
            · -- n > 35075491010773
              exact RamareSaouter2003.prime_interval_nat_ladder_c03340 n (by omega) (by omega)
            · -- n <= 35075491010773
              exact RamareSaouter2003.prime_interval_nat_ladder_c03339 n (by omega) (by omega)
          · -- n <= 34988902708037
            exact RamareSaouter2003.prime_interval_nat_ladder_c03338 n (by omega) (by omega)
    · -- n <= 34902528159511
      rcases Nat.lt_or_ge 34388740247969 n with h6 | h6
      · -- n > 34388740247969
        rcases Nat.lt_or_ge 34644681769039 n with h8 | h8
        · -- n > 34644681769039
          rcases Nat.lt_or_ge 34730418215653 n with h10 | h10
          · -- n > 34730418215653
            rcases Nat.lt_or_ge 34816366837489 n with h12 | h12
            · -- n > 34816366837489
              exact RamareSaouter2003.prime_interval_nat_ladder_c03337 n (by omega) (by omega)
            · -- n <= 34816366837489
              exact RamareSaouter2003.prime_interval_nat_ladder_c03336 n (by omega) (by omega)
          · -- n <= 34730418215653
            exact RamareSaouter2003.prime_interval_nat_ladder_c03335 n (by omega) (by omega)
        · -- n <= 34644681769039
          rcases Nat.lt_or_ge 34473843306997 n with h10 | h10
          · -- n > 34473843306997
            rcases Nat.lt_or_ge 34559156973619 n with h12 | h12
            · -- n > 34559156973619
              exact RamareSaouter2003.prime_interval_nat_ladder_c03334 n (by omega) (by omega)
            · -- n <= 34559156973619
              exact RamareSaouter2003.prime_interval_nat_ladder_c03333 n (by omega) (by omega)
          · -- n <= 34473843306997
            exact RamareSaouter2003.prime_interval_nat_ladder_c03332 n (by omega) (by omega)
      · -- n <= 34388740247969
        rcases Nat.lt_or_ge 34134689524307 n with h8 | h8
        · -- n > 34134689524307
          rcases Nat.lt_or_ge 34219163874713 n with h10 | h10
          · -- n > 34219163874713
            rcases Nat.lt_or_ge 34303847276707 n with h12 | h12
            · -- n > 34303847276707
              exact RamareSaouter2003.prime_interval_nat_ladder_c03331 n (by omega) (by omega)
            · -- n <= 34303847276707
              exact RamareSaouter2003.prime_interval_nat_ladder_c03330 n (by omega) (by omega)
          · -- n <= 34219163874713
            exact RamareSaouter2003.prime_interval_nat_ladder_c03329 n (by omega) (by omega)
        · -- n <= 34134689524307
          rcases Nat.lt_or_ge 33966365915473 n with h10 | h10
          · -- n > 33966365915473
            rcases Nat.lt_or_ge 34050423709459 n with h12 | h12
            · -- n > 34050423709459
              exact RamareSaouter2003.prime_interval_nat_ladder_c03328 n (by omega) (by omega)
            · -- n <= 34050423709459
              exact RamareSaouter2003.prime_interval_nat_ladder_c03327 n (by omega) (by omega)
          · -- n <= 33966365915473
            exact RamareSaouter2003.prime_interval_nat_ladder_c03326 n (by omega) (by omega)
  · -- n <= 33882515628859
    rcases Nat.lt_or_ge 32811113710663 n with h4 | h4
    · -- n > 32811113710663
      rcases Nat.lt_or_ge 33301330957549 n with h6 | h6
      · -- n > 33301330957549
        rcases Nat.lt_or_ge 33549179329763 n with h8 | h8
        · -- n > 33549179329763
          rcases Nat.lt_or_ge 33715435530079 n with h10 | h10
          · -- n > 33715435530079
            rcases Nat.lt_or_ge 33798872337577 n with h12 | h12
            · -- n > 33798872337577
              exact RamareSaouter2003.prime_interval_nat_ladder_c03325 n (by omega) (by omega)
            · -- n <= 33798872337577
              exact RamareSaouter2003.prime_interval_nat_ladder_c03324 n (by omega) (by omega)
          · -- n <= 33715435530079
            rcases Nat.lt_or_ge 33632204697001 n with h12 | h12
            · -- n > 33632204697001
              exact RamareSaouter2003.prime_interval_nat_ladder_c03323 n (by omega) (by omega)
            · -- n <= 33632204697001
              exact RamareSaouter2003.prime_interval_nat_ladder_c03322 n (by omega) (by omega)
        · -- n <= 33549179329763
          rcases Nat.lt_or_ge 33383742965477 n with h10 | h10
          · -- n > 33383742965477
            rcases Nat.lt_or_ge 33466358921227 n with h12 | h12
            · -- n > 33466358921227
              exact RamareSaouter2003.prime_interval_nat_ladder_c03321 n (by omega) (by omega)
            · -- n <= 33466358921227
              exact RamareSaouter2003.prime_interval_nat_ladder_c03320 n (by omega) (by omega)
          · -- n <= 33383742965477
            exact RamareSaouter2003.prime_interval_nat_ladder_c03319 n (by omega) (by omega)
      · -- n <= 33301330957549
        rcases Nat.lt_or_ge 33055313593559 n with h8 | h8
        · -- n > 33055313593559
          rcases Nat.lt_or_ge 33137116773359 n with h10 | h10
          · -- n > 33137116773359
            rcases Nat.lt_or_ge 33219122394421 n with h12 | h12
            · -- n > 33219122394421
              exact RamareSaouter2003.prime_interval_nat_ladder_c03318 n (by omega) (by omega)
            · -- n <= 33219122394421
              exact RamareSaouter2003.prime_interval_nat_ladder_c03317 n (by omega) (by omega)
          · -- n <= 33137116773359
            exact RamareSaouter2003.prime_interval_nat_ladder_c03316 n (by omega) (by omega)
        · -- n <= 33055313593559
          rcases Nat.lt_or_ge 32892312560203 n with h10 | h10
          · -- n > 32892312560203
            rcases Nat.lt_or_ge 32973712355489 n with h12 | h12
            · -- n > 32973712355489
              exact RamareSaouter2003.prime_interval_nat_ladder_c03315 n (by omega) (by omega)
            · -- n <= 32973712355489
              exact RamareSaouter2003.prime_interval_nat_ladder_c03314 n (by omega) (by omega)
          · -- n <= 32892312560203
            exact RamareSaouter2003.prime_interval_nat_ladder_c03313 n (by omega) (by omega)
    · -- n <= 32811113710663
      rcases Nat.lt_or_ge 32328112780441 n with h6 | h6
      · -- n > 32328112780441
        rcases Nat.lt_or_ge 32568717882353 n with h8 | h8
        · -- n > 32568717882353
          rcases Nat.lt_or_ge 32649316865741 n with h10 | h10
          · -- n > 32649316865741
            rcases Nat.lt_or_ge 32730115310743 n with h12 | h12
            · -- n > 32730115310743
              exact RamareSaouter2003.prime_interval_nat_ladder_c03312 n (by omega) (by omega)
            · -- n <= 32730115310743
              exact RamareSaouter2003.prime_interval_nat_ladder_c03311 n (by omega) (by omega)
          · -- n <= 32649316865741
            exact RamareSaouter2003.prime_interval_nat_ladder_c03310 n (by omega) (by omega)
        · -- n <= 32568717882353
          rcases Nat.lt_or_ge 32408116330103 n with h10 | h10
          · -- n > 32408116330103
            rcases Nat.lt_or_ge 32488317867427 n with h12 | h12
            · -- n > 32488317867427
              exact RamareSaouter2003.prime_interval_nat_ladder_c03309 n (by omega) (by omega)
            · -- n <= 32488317867427
              exact RamareSaouter2003.prime_interval_nat_ladder_c03308 n (by omega) (by omega)
          · -- n <= 32408116330103
            exact RamareSaouter2003.prime_interval_nat_ladder_c03307 n (by omega) (by omega)
      · -- n <= 32328112780441
        rcases Nat.lt_or_ge 32089285176031 n with h8 | h8
        · -- n > 32089285176031
          rcases Nat.lt_or_ge 32168697690379 n with h10 | h10
          · -- n > 32168697690379
            rcases Nat.lt_or_ge 32248306729711 n with h12 | h12
            · -- n > 32248306729711
              exact RamareSaouter2003.prime_interval_nat_ladder_c03306 n (by omega) (by omega)
            · -- n <= 32248306729711
              exact RamareSaouter2003.prime_interval_nat_ladder_c03305 n (by omega) (by omega)
          · -- n <= 32168697690379
            exact RamareSaouter2003.prime_interval_nat_ladder_c03304 n (by omega) (by omega)
        · -- n <= 32089285176031
          rcases Nat.lt_or_ge 31931047782943 n with h10 | h10
          · -- n > 31931047782943
            rcases Nat.lt_or_ge 32010068701517 n with h12 | h12
            · -- n > 32010068701517
              exact RamareSaouter2003.prime_interval_nat_ladder_c03303 n (by omega) (by omega)
            · -- n <= 32010068701517
              exact RamareSaouter2003.prime_interval_nat_ladder_c03302 n (by omega) (by omega)
          · -- n <= 31931047782943
            exact RamareSaouter2003.prime_interval_nat_ladder_c03301 n (by omega) (by omega)
