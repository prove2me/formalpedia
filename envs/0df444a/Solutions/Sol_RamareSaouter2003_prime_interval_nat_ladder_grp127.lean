-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp127
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T22:33:45.937785+00:00
-- url     : https://prove2.me/submissions/a4d1aa93-b70c-464e-beb7-5a479f933622

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06325
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06345
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06350

theorem solution (n : Nat)
    (hn : 122786617740997081 < n) (hupper : n <= 141430315807842023) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 131779110575926831 n with h2 | h2
  · -- n > 131779110575926831
    rcases Nat.lt_or_ge 136326579555081781 n with h4 | h4
    · -- n > 136326579555081781
      rcases Nat.lt_or_ge 138658791999341567 n with h6 | h6
      · -- n > 138658791999341567
        rcases Nat.lt_or_ge 139839882751950203 n with h8 | h8
        · -- n > 139839882751950203
          rcases Nat.lt_or_ge 140632846331991017 n with h10 | h10
          · -- n > 140632846331991017
            rcases Nat.lt_or_ge 141031015339637321 n with h12 | h12
            · -- n > 141031015339637321
              exact RamareSaouter2003.prime_interval_nat_ladder_c06350 n (by omega) (by omega)
            · -- n <= 141031015339637321
              exact RamareSaouter2003.prime_interval_nat_ladder_c06349 n (by omega) (by omega)
          · -- n <= 140632846331991017
            rcases Nat.lt_or_ge 140235811700376781 n with h12 | h12
            · -- n > 140235811700376781
              exact RamareSaouter2003.prime_interval_nat_ladder_c06348 n (by omega) (by omega)
            · -- n <= 140235811700376781
              exact RamareSaouter2003.prime_interval_nat_ladder_c06347 n (by omega) (by omega)
        · -- n <= 139839882751950203
          rcases Nat.lt_or_ge 139051376788455349 n with h10 | h10
          · -- n > 139051376788455349
            rcases Nat.lt_or_ge 139445071414394519 n with h12 | h12
            · -- n > 139445071414394519
              exact RamareSaouter2003.prime_interval_nat_ladder_c06346 n (by omega) (by omega)
            · -- n <= 139445071414394519
              exact RamareSaouter2003.prime_interval_nat_ladder_c06345 n (by omega) (by omega)
          · -- n <= 139051376788455349
            exact RamareSaouter2003.prime_interval_nat_ladder_c06344 n (by omega) (by omega)
      · -- n <= 138658791999341567
        rcases Nat.lt_or_ge 137487735963384421 n with h8 | h8
        · -- n > 137487735963384421
          rcases Nat.lt_or_ge 137876985165543289 n with h10 | h10
          · -- n > 137876985165543289
            rcases Nat.lt_or_ge 138267357253018739 n with h12 | h12
            · -- n > 138267357253018739
              exact RamareSaouter2003.prime_interval_nat_ladder_c06343 n (by omega) (by omega)
            · -- n <= 138267357253018739
              exact RamareSaouter2003.prime_interval_nat_ladder_c06342 n (by omega) (by omega)
          · -- n <= 137876985165543289
            exact RamareSaouter2003.prime_interval_nat_ladder_c06341 n (by omega) (by omega)
        · -- n <= 137487735963384421
          rcases Nat.lt_or_ge 136712552146085633 n with h10 | h10
          · -- n > 136712552146085633
            rcases Nat.lt_or_ge 137099588689378027 n with h12 | h12
            · -- n > 137099588689378027
              exact RamareSaouter2003.prime_interval_nat_ladder_c06340 n (by omega) (by omega)
            · -- n <= 137099588689378027
              exact RamareSaouter2003.prime_interval_nat_ladder_c06339 n (by omega) (by omega)
          · -- n <= 136712552146085633
            exact RamareSaouter2003.prime_interval_nat_ladder_c06338 n (by omega) (by omega)
    · -- n <= 136326579555081781
      rcases Nat.lt_or_ge 134033555476734919 n with h6 | h6
      · -- n > 134033555476734919
        rcases Nat.lt_or_ge 135175228264953281 n with h8 | h8
        · -- n > 135175228264953281
          rcases Nat.lt_or_ge 135557921419678811 n with h10 | h10
          · -- n > 135557921419678811
            rcases Nat.lt_or_ge 135941701933728991 n with h12 | h12
            · -- n > 135941701933728991
              exact RamareSaouter2003.prime_interval_nat_ladder_c06337 n (by omega) (by omega)
            · -- n <= 135941701933728991
              exact RamareSaouter2003.prime_interval_nat_ladder_c06336 n (by omega) (by omega)
          · -- n <= 135557921419678811
            exact RamareSaouter2003.prime_interval_nat_ladder_c06335 n (by omega) (by omega)
        · -- n <= 135175228264953281
          rcases Nat.lt_or_ge 134413042011721427 n with h10 | h10
          · -- n > 134413042011721427
            rcases Nat.lt_or_ge 134793593736305941 n with h12 | h12
            · -- n > 134793593736305941
              exact RamareSaouter2003.prime_interval_nat_ladder_c06334 n (by omega) (by omega)
            · -- n <= 134793593736305941
              exact RamareSaouter2003.prime_interval_nat_ladder_c06333 n (by omega) (by omega)
          · -- n <= 134413042011721427
            exact RamareSaouter2003.prime_interval_nat_ladder_c06332 n (by omega) (by omega)
      · -- n <= 134033555476734919
        rcases Nat.lt_or_ge 132901578741345793 n with h8 | h8
        · -- n > 132901578741345793
          rcases Nat.lt_or_ge 133277827946378749 n with h10 | h10
          · -- n > 133277827946378749
            rcases Nat.lt_or_ge 133655144965059661 n with h12 | h12
            · -- n > 133655144965059661
              exact RamareSaouter2003.prime_interval_nat_ladder_c06331 n (by omega) (by omega)
            · -- n <= 133655144965059661
              exact RamareSaouter2003.prime_interval_nat_ladder_c06330 n (by omega) (by omega)
          · -- n <= 133277827946378749
            exact RamareSaouter2003.prime_interval_nat_ladder_c06329 n (by omega) (by omega)
        · -- n <= 132901578741345793
          rcases Nat.lt_or_ge 132152211316859681 n with h10 | h10
          · -- n > 132152211316859681
            rcases Nat.lt_or_ge 132526358630435389 n with h12 | h12
            · -- n > 132526358630435389
              exact RamareSaouter2003.prime_interval_nat_ladder_c06328 n (by omega) (by omega)
            · -- n <= 132526358630435389
              exact RamareSaouter2003.prime_interval_nat_ladder_c06327 n (by omega) (by omega)
          · -- n <= 132152211316859681
            exact RamareSaouter2003.prime_interval_nat_ladder_c06326 n (by omega) (by omega)
  · -- n <= 131779110575926831
    rcases Nat.lt_or_ge 127023665747056619 n with h4 | h4
    · -- n > 127023665747056619
      rcases Nat.lt_or_ge 129196778303581873 n with h6 | h6
      · -- n > 129196778303581873
        rcases Nat.lt_or_ge 130297234564195157 n with h8 | h8
        · -- n > 130297234564195157
          rcases Nat.lt_or_ge 131036061662494699 n with h10 | h10
          · -- n > 131036061662494699
            rcases Nat.lt_or_ge 131407058538922609 n with h12 | h12
            · -- n > 131407058538922609
              exact RamareSaouter2003.prime_interval_nat_ladder_c06325 n (by omega) (by omega)
            · -- n <= 131407058538922609
              exact RamareSaouter2003.prime_interval_nat_ladder_c06324 n (by omega) (by omega)
          · -- n <= 131036061662494699
            rcases Nat.lt_or_ge 130666128529513373 n with h12 | h12
            · -- n > 130666128529513373
              exact RamareSaouter2003.prime_interval_nat_ladder_c06323 n (by omega) (by omega)
            · -- n <= 130666128529513373
              exact RamareSaouter2003.prime_interval_nat_ladder_c06322 n (by omega) (by omega)
        · -- n <= 130297234564195157
          rcases Nat.lt_or_ge 129562569561190939 n with h10 | h10
          · -- n > 129562569561190939
            rcases Nat.lt_or_ge 129929396980213991 n with h12 | h12
            · -- n > 129929396980213991
              exact RamareSaouter2003.prime_interval_nat_ladder_c06321 n (by omega) (by omega)
            · -- n <= 129929396980213991
              exact RamareSaouter2003.prime_interval_nat_ladder_c06320 n (by omega) (by omega)
          · -- n <= 129562569561190939
            exact RamareSaouter2003.prime_interval_nat_ladder_c06319 n (by omega) (by omega)
      · -- n <= 129196778303581873
        rcases Nat.lt_or_ge 128105621713836731 n with h8 | h8
        · -- n > 128105621713836731
          rcases Nat.lt_or_ge 128468312688492449 n with h10 | h10
          · -- n > 128468312688492449
            rcases Nat.lt_or_ge 128832030341889011 n with h12 | h12
            · -- n > 128832030341889011
              exact RamareSaouter2003.prime_interval_nat_ladder_c06318 n (by omega) (by omega)
            · -- n <= 128832030341889011
              exact RamareSaouter2003.prime_interval_nat_ladder_c06317 n (by omega) (by omega)
          · -- n <= 128468312688492449
            exact RamareSaouter2003.prime_interval_nat_ladder_c06316 n (by omega) (by omega)
        · -- n <= 128105621713836731
          rcases Nat.lt_or_ge 127383288261440339 n with h10 | h10
          · -- n > 127383288261440339
            rcases Nat.lt_or_ge 127743945941186011 n with h12 | h12
            · -- n > 127743945941186011
              exact RamareSaouter2003.prime_interval_nat_ladder_c06315 n (by omega) (by omega)
            · -- n <= 127743945941186011
              exact RamareSaouter2003.prime_interval_nat_ladder_c06314 n (by omega) (by omega)
          · -- n <= 127383288261440339
            exact RamareSaouter2003.prime_interval_nat_ladder_c06313 n (by omega) (by omega)
    · -- n <= 127023665747056619
      rcases Nat.lt_or_ge 124887154801451683 n with h6 | h6
      · -- n > 124887154801451683
        rcases Nat.lt_or_ge 125950886997100229 n with h8 | h8
        · -- n > 125950886997100229
          rcases Nat.lt_or_ge 126307474752100303 n with h10 | h10
          · -- n > 126307474752100303
            rcases Nat.lt_or_ge 126665078364258971 n with h12 | h12
            · -- n > 126665078364258971
              exact RamareSaouter2003.prime_interval_nat_ladder_c06312 n (by omega) (by omega)
            · -- n <= 126665078364258971
              exact RamareSaouter2003.prime_interval_nat_ladder_c06311 n (by omega) (by omega)
          · -- n <= 126307474752100303
            exact RamareSaouter2003.prime_interval_nat_ladder_c06310 n (by omega) (by omega)
        · -- n <= 125950886997100229
          rcases Nat.lt_or_ge 125240745408294343 n with h10 | h10
          · -- n > 125240745408294343
            rcases Nat.lt_or_ge 125595339168226061 n with h12 | h12
            · -- n > 125595339168226061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06309 n (by omega) (by omega)
            · -- n <= 125595339168226061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06308 n (by omega) (by omega)
          · -- n <= 125240745408294343
            exact RamareSaouter2003.prime_interval_nat_ladder_c06307 n (by omega) (by omega)
      · -- n <= 124887154801451683
        rcases Nat.lt_or_ge 123832444894946653 n with h8 | h8
        · -- n > 123832444894946653
          rcases Nat.lt_or_ge 124182985529249117 n with h10 | h10
          · -- n > 124182985529249117
            rcases Nat.lt_or_ge 124534579945098887 n with h12 | h12
            · -- n > 124534579945098887
              exact RamareSaouter2003.prime_interval_nat_ladder_c06306 n (by omega) (by omega)
            · -- n <= 124534579945098887
              exact RamareSaouter2003.prime_interval_nat_ladder_c06305 n (by omega) (by omega)
          · -- n <= 124182985529249117
            exact RamareSaouter2003.prime_interval_nat_ladder_c06304 n (by omega) (by omega)
        · -- n <= 123832444894946653
          rcases Nat.lt_or_ge 123134209264292777 n with h10 | h10
          · -- n > 123134209264292777
            rcases Nat.lt_or_ge 123482828387110799 n with h12 | h12
            · -- n > 123482828387110799
              exact RamareSaouter2003.prime_interval_nat_ladder_c06303 n (by omega) (by omega)
            · -- n <= 123482828387110799
              exact RamareSaouter2003.prime_interval_nat_ladder_c06302 n (by omega) (by omega)
          · -- n <= 123134209264292777
            exact RamareSaouter2003.prime_interval_nat_ladder_c06301 n (by omega) (by omega)
