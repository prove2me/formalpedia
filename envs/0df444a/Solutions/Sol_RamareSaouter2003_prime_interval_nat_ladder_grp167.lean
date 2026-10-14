-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp167
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T14:23:28.959744+00:00
-- url     : https://prove2.me/submissions/ef4337f1-6f12-4106-b4ca-97e8045f2b72

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08296
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08300
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08325

theorem solution (n : Nat)
    (hn : 30299003920194604927 < n) (hupper : n <= 34149953953884191081) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 32127652585792731307 n with h2 | h2
  · -- n > 32127652585792731307
    rcases Nat.lt_or_ge 33082958423379635027 n with h4 | h4
    · -- n > 33082958423379635027
      rcases Nat.lt_or_ge 33571211078879503109 n with h6 | h6
      · -- n > 33571211078879503109
        rcases Nat.lt_or_ge 33818033086347811421 n with h8 | h8
        · -- n > 33818033086347811421
          rcases Nat.lt_or_ge 33983588243979899633 n with h10 | h10
          · -- n > 33983588243979899633
            rcases Nat.lt_or_ge 34066669675384458641 n with h12 | h12
            · -- n > 34066669675384458641
              exact RamareSaouter2003.prime_interval_nat_ladder_c08325 n (by omega) (by omega)
            · -- n <= 34066669675384458641
              exact RamareSaouter2003.prime_interval_nat_ladder_c08324 n (by omega) (by omega)
          · -- n <= 33983588243979899633
            rcases Nat.lt_or_ge 33900709810578038083 n with h12 | h12
            · -- n > 33900709810578038083
              exact RamareSaouter2003.prime_interval_nat_ladder_c08323 n (by omega) (by omega)
            · -- n <= 33900709810578038083
              exact RamareSaouter2003.prime_interval_nat_ladder_c08322 n (by omega) (by omega)
        · -- n <= 33818033086347811421
          rcases Nat.lt_or_ge 33653284297756459849 n with h10 | h10
          · -- n > 33653284297756459849
            rcases Nat.lt_or_ge 33735558270940069171 n with h12 | h12
            · -- n > 33735558270940069171
              exact RamareSaouter2003.prime_interval_nat_ladder_c08321 n (by omega) (by omega)
            · -- n <= 33735558270940069171
              exact RamareSaouter2003.prime_interval_nat_ladder_c08320 n (by omega) (by omega)
          · -- n <= 33653284297756459849
            exact RamareSaouter2003.prime_interval_nat_ladder_c08319 n (by omega) (by omega)
      · -- n <= 33571211078879503109
        rcases Nat.lt_or_ge 33326190307827549751 n with h8 | h8
        · -- n > 33326190307827549751
          rcases Nat.lt_or_ge 33407664611279167421 n with h10 | h10
          · -- n > 33407664611279167421
            rcases Nat.lt_or_ge 33489337956297305009 n with h12 | h12
            · -- n > 33489337956297305009
              exact RamareSaouter2003.prime_interval_nat_ladder_c08318 n (by omega) (by omega)
            · -- n <= 33489337956297305009
              exact RamareSaouter2003.prime_interval_nat_ladder_c08317 n (by omega) (by omega)
          · -- n <= 33407664611279167421
            exact RamareSaouter2003.prime_interval_nat_ladder_c08316 n (by omega) (by omega)
        · -- n <= 33326190307827549751
          rcases Nat.lt_or_ge 33163837611745025123 n with h10 | h10
          · -- n > 33163837611745025123
            rcases Nat.lt_or_ge 33244914900862204283 n with h12 | h12
            · -- n > 33244914900862204283
              exact RamareSaouter2003.prime_interval_nat_ladder_c08315 n (by omega) (by omega)
            · -- n <= 33244914900862204283
              exact RamareSaouter2003.prime_interval_nat_ladder_c08314 n (by omega) (by omega)
          · -- n <= 33163837611745025123
            exact RamareSaouter2003.prime_interval_nat_ladder_c08313 n (by omega) (by omega)
    · -- n <= 33082958423379635027
      rcases Nat.lt_or_ge 32601806304409403689 n with h6 | h6
      · -- n > 32601806304409403689
        rcases Nat.lt_or_ge 32841501256956795737 n with h8 | h8
        · -- n > 32841501256956795737
          rcases Nat.lt_or_ge 32921790576741628841 n with h10 | h10
          · -- n > 32921790576741628841
            rcases Nat.lt_or_ge 33002276041096179599 n with h12 | h12
            · -- n > 33002276041096179599
              exact RamareSaouter2003.prime_interval_nat_ladder_c08312 n (by omega) (by omega)
            · -- n <= 33002276041096179599
              exact RamareSaouter2003.prime_interval_nat_ladder_c08311 n (by omega) (by omega)
          · -- n <= 32921790576741628841
            exact RamareSaouter2003.prime_interval_nat_ladder_c08310 n (by omega) (by omega)
        · -- n <= 32841501256956795737
          rcases Nat.lt_or_ge 32681509684494377983 n with h10 | h10
          · -- n > 32681509684494377983
            rcases Nat.lt_or_ge 32761407757022199139 n with h12 | h12
            · -- n > 32761407757022199139
              exact RamareSaouter2003.prime_interval_nat_ladder_c08309 n (by omega) (by omega)
            · -- n <= 32761407757022199139
              exact RamareSaouter2003.prime_interval_nat_ladder_c08308 n (by omega) (by omega)
          · -- n <= 32681509684494377983
            exact RamareSaouter2003.prime_interval_nat_ladder_c08307 n (by omega) (by omega)
      · -- n <= 32601806304409403689
        rcases Nat.lt_or_ge 32363861091034795643 n with h8 | h8
        · -- n > 32363861091034795643
          rcases Nat.lt_or_ge 32442982676741922193 n with h10 | h10
          · -- n > 32442982676741922193
            rcases Nat.lt_or_ge 32522297454592780883 n with h12 | h12
            · -- n > 32522297454592780883
              exact RamareSaouter2003.prime_interval_nat_ladder_c08306 n (by omega) (by omega)
            · -- n <= 32522297454592780883
              exact RamareSaouter2003.prime_interval_nat_ladder_c08305 n (by omega) (by omega)
          · -- n <= 32442982676741922193
            exact RamareSaouter2003.prime_interval_nat_ladder_c08304 n (by omega) (by omega)
        · -- n <= 32363861091034795643
          rcases Nat.lt_or_ge 32206196778644086879 n with h10 | h10
          · -- n > 32206196778644086879
            rcases Nat.lt_or_ge 32284932765857502037 n with h12 | h12
            · -- n > 32284932765857502037
              exact RamareSaouter2003.prime_interval_nat_ladder_c08303 n (by omega) (by omega)
            · -- n <= 32284932765857502037
              exact RamareSaouter2003.prime_interval_nat_ladder_c08302 n (by omega) (by omega)
          · -- n <= 32206196778644086879
            exact RamareSaouter2003.prime_interval_nat_ladder_c08301 n (by omega) (by omega)
  · -- n <= 32127652585792731307
    rcases Nat.lt_or_ge 31199934719042324693 n with h4 | h4
    · -- n > 31199934719042324693
      rcases Nat.lt_or_ge 31660395966971661017 n with h6 | h6
      · -- n > 31660395966971661017
        rcases Nat.lt_or_ge 31893168722975438299 n with h8 | h8
        · -- n > 31893168722975438299
          rcases Nat.lt_or_ge 31971139355643410651 n with h10 | h10
          · -- n > 31971139355643410651
            rcases Nat.lt_or_ge 32049300685020909161 n with h12 | h12
            · -- n > 32049300685020909161
              exact RamareSaouter2003.prime_interval_nat_ladder_c08300 n (by omega) (by omega)
            · -- n <= 32049300685020909161
              exact RamareSaouter2003.prime_interval_nat_ladder_c08299 n (by omega) (by omega)
          · -- n <= 31971139355643410651
            exact RamareSaouter2003.prime_interval_nat_ladder_c08298 n (by omega) (by omega)
        · -- n <= 31893168722975438299
          rcases Nat.lt_or_ge 31737797826849859417 n with h10 | h10
          · -- n > 31737797826849859417
            rcases Nat.lt_or_ge 31815388596414731881 n with h12 | h12
            · -- n > 31815388596414731881
              exact RamareSaouter2003.prime_interval_nat_ladder_c08297 n (by omega) (by omega)
            · -- n <= 31815388596414731881
              exact RamareSaouter2003.prime_interval_nat_ladder_c08296 n (by omega) (by omega)
          · -- n <= 31737797826849859417
            exact RamareSaouter2003.prime_interval_nat_ladder_c08295 n (by omega) (by omega)
      · -- n <= 31660395966971661017
        rcases Nat.lt_or_ge 31429322065329816007 n with h8 | h8
        · -- n > 31429322065329816007
          rcases Nat.lt_or_ge 31506158672604782317 n with h10 | h10
          · -- n > 31506158672604782317
            rcases Nat.lt_or_ge 31583183221024798607 n with h12 | h12
            · -- n > 31583183221024798607
              exact RamareSaouter2003.prime_interval_nat_ladder_c08294 n (by omega) (by omega)
            · -- n <= 31583183221024798607
              exact RamareSaouter2003.prime_interval_nat_ladder_c08293 n (by omega) (by omega)
          · -- n <= 31506158672604782317
            exact RamareSaouter2003.prime_interval_nat_ladder_c08292 n (by omega) (by omega)
        · -- n <= 31429322065329816007
          rcases Nat.lt_or_ge 31276210828332175073 n with h10 | h10
          · -- n > 31276210828332175073
            rcases Nat.lt_or_ge 31352672875641457103 n with h12 | h12
            · -- n > 31352672875641457103
              exact RamareSaouter2003.prime_interval_nat_ladder_c08291 n (by omega) (by omega)
            · -- n <= 31352672875641457103
              exact RamareSaouter2003.prime_interval_nat_ladder_c08290 n (by omega) (by omega)
          · -- n <= 31276210828332175073
            exact RamareSaouter2003.prime_interval_nat_ladder_c08289 n (by omega) (by omega)
    · -- n <= 31199934719042324693
      rcases Nat.lt_or_ge 30746169800901746707 n with h6 | h6
      · -- n > 30746169800901746707
        rcases Nat.lt_or_ge 30972220839801428287 n with h8 | h8
        · -- n > 30972220839801428287
          rcases Nat.lt_or_ge 31047940199258264467 n with h10 | h10
          · -- n > 31047940199258264467
            rcases Nat.lt_or_ge 31123844623510846919 n with h12 | h12
            · -- n > 31123844623510846919
              exact RamareSaouter2003.prime_interval_nat_ladder_c08288 n (by omega) (by omega)
            · -- n <= 31123844623510846919
              exact RamareSaouter2003.prime_interval_nat_ladder_c08287 n (by omega) (by omega)
          · -- n <= 31047940199258264467
            exact RamareSaouter2003.prime_interval_nat_ladder_c08286 n (by omega) (by omega)
        · -- n <= 30972220839801428287
          rcases Nat.lt_or_ge 30821336362258852103 n with h10 | h10
          · -- n > 30821336362258852103
            rcases Nat.lt_or_ge 30896686896620939497 n with h12 | h12
            · -- n > 30896686896620939497
              exact RamareSaouter2003.prime_interval_nat_ladder_c08285 n (by omega) (by omega)
            · -- n <= 30896686896620939497
              exact RamareSaouter2003.prime_interval_nat_ladder_c08284 n (by omega) (by omega)
          · -- n <= 30821336362258852103
            exact RamareSaouter2003.prime_interval_nat_ladder_c08283 n (by omega) (by omega)
      · -- n <= 30746169800901746707
        rcases Nat.lt_or_ge 30521768037615163987 n with h8 | h8
        · -- n > 30521768037615163987
          rcases Nat.lt_or_ge 30596386222715308841 n with h10 | h10
          · -- n > 30596386222715308841
            rcases Nat.lt_or_ge 30671186776884201901 n with h12 | h12
            · -- n > 30671186776884201901
              exact RamareSaouter2003.prime_interval_nat_ladder_c08282 n (by omega) (by omega)
            · -- n <= 30671186776884201901
              exact RamareSaouter2003.prime_interval_nat_ladder_c08281 n (by omega) (by omega)
          · -- n <= 30596386222715308841
            exact RamareSaouter2003.prime_interval_nat_ladder_c08280 n (by omega) (by omega)
        · -- n <= 30521768037615163987
          rcases Nat.lt_or_ge 30373077274018249097 n with h10 | h10
          · -- n > 30373077274018249097
            rcases Nat.lt_or_ge 30447331898486849693 n with h12 | h12
            · -- n > 30447331898486849693
              exact RamareSaouter2003.prime_interval_nat_ladder_c08279 n (by omega) (by omega)
            · -- n <= 30447331898486849693
              exact RamareSaouter2003.prime_interval_nat_ladder_c08278 n (by omega) (by omega)
          · -- n <= 30373077274018249097
            exact RamareSaouter2003.prime_interval_nat_ladder_c08277 n (by omega) (by omega)
