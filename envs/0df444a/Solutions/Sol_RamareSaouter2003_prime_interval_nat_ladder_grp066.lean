-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp066
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T03:24:01.605793+00:00
-- url     : https://prove2.me/submissions/e680a83e-9a20-40b7-9231-ef07b2b1e1a5

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03276
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03296
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03300

theorem solution (n : Nat)
    (hn : 28149319776593 < n) (hupper : n <= 31852221937607) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 29943586640533 n with h2 | h2
  · -- n > 29943586640533
    rcases Nat.lt_or_ge 30845020108933 n with h4 | h4
    · -- n > 30845020108933
      rcases Nat.lt_or_ge 31305862766911 n with h6 | h6
      · -- n > 31305862766911
        rcases Nat.lt_or_ge 31538859674263 n with h8 | h8
        · -- n > 31538859674263
          rcases Nat.lt_or_ge 31695153541201 n with h10 | h10
          · -- n > 31695153541201
            rcases Nat.lt_or_ge 31773590683763 n with h12 | h12
            · -- n > 31773590683763
              exact RamareSaouter2003.prime_interval_nat_ladder_c03300 n (by omega) (by omega)
            · -- n <= 31773590683763
              exact RamareSaouter2003.prime_interval_nat_ladder_c03299 n (by omega) (by omega)
          · -- n <= 31695153541201
            rcases Nat.lt_or_ge 31616910030647 n with h12 | h12
            · -- n > 31616910030647
              exact RamareSaouter2003.prime_interval_nat_ladder_c03298 n (by omega) (by omega)
            · -- n <= 31616910030647
              exact RamareSaouter2003.prime_interval_nat_ladder_c03297 n (by omega) (by omega)
        · -- n <= 31538859674263
          rcases Nat.lt_or_ge 31383336517451 n with h10 | h10
          · -- n > 31383336517451
            rcases Nat.lt_or_ge 31461001995047 n with h12 | h12
            · -- n > 31461001995047
              exact RamareSaouter2003.prime_interval_nat_ladder_c03296 n (by omega) (by omega)
            · -- n <= 31461001995047
              exact RamareSaouter2003.prime_interval_nat_ladder_c03295 n (by omega) (by omega)
          · -- n <= 31383336517451
            exact RamareSaouter2003.prime_interval_nat_ladder_c03294 n (by omega) (by omega)
      · -- n <= 31305862766911
        rcases Nat.lt_or_ge 31074587150573 n with h8 | h8
        · -- n > 31074587150573
          rcases Nat.lt_or_ge 31151488554931 n with h10 | h10
          · -- n > 31151488554931
            rcases Nat.lt_or_ge 31228580270057 n with h12 | h12
            · -- n > 31228580270057
              exact RamareSaouter2003.prime_interval_nat_ladder_c03293 n (by omega) (by omega)
            · -- n <= 31228580270057
              exact RamareSaouter2003.prime_interval_nat_ladder_c03292 n (by omega) (by omega)
          · -- n <= 31151488554931
            exact RamareSaouter2003.prime_interval_nat_ladder_c03291 n (by omega) (by omega)
        · -- n <= 31074587150573
          rcases Nat.lt_or_ge 30921353395531 n with h10 | h10
          · -- n > 30921353395531
            rcases Nat.lt_or_ge 30997875586927 n with h12 | h12
            · -- n > 30997875586927
              exact RamareSaouter2003.prime_interval_nat_ladder_c03290 n (by omega) (by omega)
            · -- n <= 30997875586927
              exact RamareSaouter2003.prime_interval_nat_ladder_c03289 n (by omega) (by omega)
          · -- n <= 30921353395531
            exact RamareSaouter2003.prime_interval_nat_ladder_c03288 n (by omega) (by omega)
    · -- n <= 30845020108933
      rcases Nat.lt_or_ge 30390961354591 n with h6 | h6
      · -- n > 30390961354591
        rcases Nat.lt_or_ge 30617149019971 n with h8 | h8
        · -- n > 30617149019971
          rcases Nat.lt_or_ge 30692918385799 n with h10 | h10
          · -- n > 30692918385799
            rcases Nat.lt_or_ge 30768875260829 n with h12 | h12
            · -- n > 30768875260829
              exact RamareSaouter2003.prime_interval_nat_ladder_c03287 n (by omega) (by omega)
            · -- n <= 30768875260829
              exact RamareSaouter2003.prime_interval_nat_ladder_c03286 n (by omega) (by omega)
          · -- n <= 30692918385799
            exact RamareSaouter2003.prime_interval_nat_ladder_c03285 n (by omega) (by omega)
        · -- n <= 30617149019971
          rcases Nat.lt_or_ge 30466170965599 n with h10 | h10
          · -- n > 30466170965599
            rcases Nat.lt_or_ge 30541566700511 n with h12 | h12
            · -- n > 30541566700511
              exact RamareSaouter2003.prime_interval_nat_ladder_c03284 n (by omega) (by omega)
            · -- n <= 30541566700511
              exact RamareSaouter2003.prime_interval_nat_ladder_c03283 n (by omega) (by omega)
          · -- n <= 30466170965599
            exact RamareSaouter2003.prime_interval_nat_ladder_c03282 n (by omega) (by omega)
      · -- n <= 30390961354591
        rcases Nat.lt_or_ge 30166444676369 n with h8 | h8
        · -- n > 30166444676369
          rcases Nat.lt_or_ge 30241098667817 n with h10 | h10
          · -- n > 30241098667817
            rcases Nat.lt_or_ge 30315937408021 n with h12 | h12
            · -- n > 30315937408021
              exact RamareSaouter2003.prime_interval_nat_ladder_c03281 n (by omega) (by omega)
            · -- n <= 30315937408021
              exact RamareSaouter2003.prime_interval_nat_ladder_c03280 n (by omega) (by omega)
          · -- n <= 30241098667817
            exact RamareSaouter2003.prime_interval_nat_ladder_c03279 n (by omega) (by omega)
        · -- n <= 30166444676369
          rcases Nat.lt_or_ge 30017689117127 n with h10 | h10
          · -- n > 30017689117127
            rcases Nat.lt_or_ge 30091974977789 n with h12 | h12
            · -- n > 30091974977789
              exact RamareSaouter2003.prime_interval_nat_ladder_c03278 n (by omega) (by omega)
            · -- n <= 30091974977789
              exact RamareSaouter2003.prime_interval_nat_ladder_c03277 n (by omega) (by omega)
          · -- n <= 30017689117127
            exact RamareSaouter2003.prime_interval_nat_ladder_c03276 n (by omega) (by omega)
  · -- n <= 29943586640533
    rcases Nat.lt_or_ge 28996737931717 n with h4 | h4
    · -- n > 28996737931717
      rcases Nat.lt_or_ge 29429966171701 n with h6 | h6
      · -- n > 29429966171701
        rcases Nat.lt_or_ge 29649001537559 n with h8 | h8
        · -- n > 29649001537559
          rcases Nat.lt_or_ge 29795930029849 n with h10 | h10
          · -- n > 29795930029849
            rcases Nat.lt_or_ge 29869667095253 n with h12 | h12
            · -- n > 29869667095253
              exact RamareSaouter2003.prime_interval_nat_ladder_c03275 n (by omega) (by omega)
            · -- n <= 29869667095253
              exact RamareSaouter2003.prime_interval_nat_ladder_c03274 n (by omega) (by omega)
          · -- n <= 29795930029849
            rcases Nat.lt_or_ge 29722374993679 n with h12 | h12
            · -- n > 29722374993679
              exact RamareSaouter2003.prime_interval_nat_ladder_c03273 n (by omega) (by omega)
            · -- n <= 29722374993679
              exact RamareSaouter2003.prime_interval_nat_ladder_c03272 n (by omega) (by omega)
        · -- n <= 29649001537559
          rcases Nat.lt_or_ge 29502797573177 n with h10 | h10
          · -- n > 29502797573177
            rcases Nat.lt_or_ge 29575809213133 n with h12 | h12
            · -- n > 29575809213133
              exact RamareSaouter2003.prime_interval_nat_ladder_c03271 n (by omega) (by omega)
            · -- n <= 29575809213133
              exact RamareSaouter2003.prime_interval_nat_ladder_c03270 n (by omega) (by omega)
          · -- n <= 29502797573177
            exact RamareSaouter2003.prime_interval_nat_ladder_c03269 n (by omega) (by omega)
      · -- n <= 29429966171701
        rcases Nat.lt_or_ge 29212548954649 n with h8 | h8
        · -- n > 29212548954649
          rcases Nat.lt_or_ge 29284842305899 n with h10 | h10
          · -- n > 29284842305899
            rcases Nat.lt_or_ge 29357314563949 n with h12 | h12
            · -- n > 29357314563949
              exact RamareSaouter2003.prime_interval_nat_ladder_c03268 n (by omega) (by omega)
            · -- n <= 29357314563949
              exact RamareSaouter2003.prime_interval_nat_ladder_c03267 n (by omega) (by omega)
          · -- n <= 29284842305899
            exact RamareSaouter2003.prime_interval_nat_ladder_c03266 n (by omega) (by omega)
        · -- n <= 29212548954649
          rcases Nat.lt_or_ge 29068497207623 n with h10 | h10
          · -- n > 29068497207623
            rcases Nat.lt_or_ge 29140434068771 n with h12 | h12
            · -- n > 29140434068771
              exact RamareSaouter2003.prime_interval_nat_ladder_c03265 n (by omega) (by omega)
            · -- n <= 29140434068771
              exact RamareSaouter2003.prime_interval_nat_ladder_c03264 n (by omega) (by omega)
          · -- n <= 29068497207623
            exact RamareSaouter2003.prime_interval_nat_ladder_c03263 n (by omega) (by omega)
    · -- n <= 28996737931717
      rcases Nat.lt_or_ge 28569887093177 n with h6 | h6
      · -- n > 28569887093177
        rcases Nat.lt_or_ge 28782521237329 n with h8 | h8
        · -- n > 28782521237329
          rcases Nat.lt_or_ge 28853750383343 n with h10 | h10
          · -- n > 28853750383343
            rcases Nat.lt_or_ge 28925155802797 n with h12 | h12
            · -- n > 28925155802797
              exact RamareSaouter2003.prime_interval_nat_ladder_c03262 n (by omega) (by omega)
            · -- n <= 28925155802797
              exact RamareSaouter2003.prime_interval_nat_ladder_c03261 n (by omega) (by omega)
          · -- n <= 28853750383343
            exact RamareSaouter2003.prime_interval_nat_ladder_c03260 n (by omega) (by omega)
        · -- n <= 28782521237329
          rcases Nat.lt_or_ge 28640590025833 n with h10 | h10
          · -- n > 28640590025833
            rcases Nat.lt_or_ge 28711467929393 n with h12 | h12
            · -- n > 28711467929393
              exact RamareSaouter2003.prime_interval_nat_ladder_c03259 n (by omega) (by omega)
            · -- n <= 28711467929393
              exact RamareSaouter2003.prime_interval_nat_ladder_c03258 n (by omega) (by omega)
          · -- n <= 28640590025833
            exact RamareSaouter2003.prime_interval_nat_ladder_c03257 n (by omega) (by omega)
      · -- n <= 28569887093177
        rcases Nat.lt_or_ge 28358823807827 n with h8 | h8
        · -- n > 28358823807827
          rcases Nat.lt_or_ge 28429004414507 n with h10 | h10
          · -- n > 28429004414507
            rcases Nat.lt_or_ge 28499358699743 n with h12 | h12
            · -- n > 28499358699743
              exact RamareSaouter2003.prime_interval_nat_ladder_c03256 n (by omega) (by omega)
            · -- n <= 28499358699743
              exact RamareSaouter2003.prime_interval_nat_ladder_c03255 n (by omega) (by omega)
          · -- n <= 28429004414507
            exact RamareSaouter2003.prime_interval_nat_ladder_c03254 n (by omega) (by omega)
        · -- n <= 28358823807827
          rcases Nat.lt_or_ge 28218981916061 n with h10 | h10
          · -- n > 28218981916061
            rcases Nat.lt_or_ge 28288816450919 n with h12 | h12
            · -- n > 28288816450919
              exact RamareSaouter2003.prime_interval_nat_ladder_c03253 n (by omega) (by omega)
            · -- n <= 28288816450919
              exact RamareSaouter2003.prime_interval_nat_ladder_c03252 n (by omega) (by omega)
          · -- n <= 28218981916061
            exact RamareSaouter2003.prime_interval_nat_ladder_c03251 n (by omega) (by omega)
