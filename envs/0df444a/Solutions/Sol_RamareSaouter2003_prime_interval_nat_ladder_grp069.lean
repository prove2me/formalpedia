-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp069
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T04:54:05.746021+00:00
-- url     : https://prove2.me/submissions/43c7a860-9a04-448a-a29c-f3853b94a303

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03423
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03443
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03450

theorem solution (n : Nat)
    (hn : 40783396349303 < n) (hupper : n <= 46148248066457) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 43382972370511 n with h2 | h2
  · -- n > 43382972370511
    rcases Nat.lt_or_ge 44688990375149 n with h4 | h4
    · -- n > 44688990375149
      rcases Nat.lt_or_ge 45356670053537 n with h6 | h6
      · -- n > 45356670053537
        rcases Nat.lt_or_ge 45694241451647 n with h8 | h8
        · -- n > 45694241451647
          rcases Nat.lt_or_ge 45920683681003 n with h10 | h10
          · -- n > 45920683681003
            rcases Nat.lt_or_ge 46034325257233 n with h12 | h12
            · -- n > 46034325257233
              exact RamareSaouter2003.prime_interval_nat_ladder_c03450 n (by omega) (by omega)
            · -- n <= 46034325257233
              exact RamareSaouter2003.prime_interval_nat_ladder_c03449 n (by omega) (by omega)
          · -- n <= 45920683681003
            rcases Nat.lt_or_ge 45807322643323 n with h12 | h12
            · -- n > 45807322643323
              exact RamareSaouter2003.prime_interval_nat_ladder_c03448 n (by omega) (by omega)
            · -- n <= 45807322643323
              exact RamareSaouter2003.prime_interval_nat_ladder_c03447 n (by omega) (by omega)
        · -- n <= 45694241451647
          rcases Nat.lt_or_ge 45468915845053 n with h10 | h10
          · -- n > 45468915845053
            rcases Nat.lt_or_ge 45581439415247 n with h12 | h12
            · -- n > 45581439415247
              exact RamareSaouter2003.prime_interval_nat_ladder_c03446 n (by omega) (by omega)
            · -- n <= 45581439415247
              exact RamareSaouter2003.prime_interval_nat_ladder_c03445 n (by omega) (by omega)
          · -- n <= 45468915845053
            exact RamareSaouter2003.prime_interval_nat_ladder_c03444 n (by omega) (by omega)
      · -- n <= 45356670053537
        rcases Nat.lt_or_ge 45021592502741 n with h8 | h8
        · -- n > 45021592502741
          rcases Nat.lt_or_ge 45133009065637 n with h10 | h10
          · -- n > 45133009065637
            rcases Nat.lt_or_ge 45244701355241 n with h12 | h12
            · -- n > 45244701355241
              exact RamareSaouter2003.prime_interval_nat_ladder_c03443 n (by omega) (by omega)
            · -- n <= 45244701355241
              exact RamareSaouter2003.prime_interval_nat_ladder_c03442 n (by omega) (by omega)
          · -- n <= 45133009065637
            exact RamareSaouter2003.prime_interval_nat_ladder_c03441 n (by omega) (by omega)
        · -- n <= 45021592502741
          rcases Nat.lt_or_ge 44799583835597 n with h10 | h10
          · -- n > 44799583835597
            rcases Nat.lt_or_ge 44910450985661 n with h12 | h12
            · -- n > 44910450985661
              exact RamareSaouter2003.prime_interval_nat_ladder_c03440 n (by omega) (by omega)
            · -- n <= 44910450985661
              exact RamareSaouter2003.prime_interval_nat_ladder_c03439 n (by omega) (by omega)
          · -- n <= 44799583835597
            exact RamareSaouter2003.prime_interval_nat_ladder_c03438 n (by omega) (by omega)
    · -- n <= 44688990375149
      rcases Nat.lt_or_ge 44031139375471 n with h6 | h6
      · -- n > 44031139375471
        rcases Nat.lt_or_ge 44358845383499 n with h8 | h8
        · -- n > 44358845383499
          rcases Nat.lt_or_ge 44468621822227 n with h10 | h10
          · -- n > 44468621822227
            rcases Nat.lt_or_ge 44578669928659 n with h12 | h12
            · -- n > 44578669928659
              exact RamareSaouter2003.prime_interval_nat_ladder_c03437 n (by omega) (by omega)
            · -- n <= 44578669928659
              exact RamareSaouter2003.prime_interval_nat_ladder_c03436 n (by omega) (by omega)
          · -- n <= 44468621822227
            exact RamareSaouter2003.prime_interval_nat_ladder_c03435 n (by omega) (by omega)
        · -- n <= 44358845383499
          rcases Nat.lt_or_ge 44140104828301 n with h10 | h10
          · -- n > 44140104828301
            rcases Nat.lt_or_ge 44249339941847 n with h12 | h12
            · -- n > 44249339941847
              exact RamareSaouter2003.prime_interval_nat_ladder_c03434 n (by omega) (by omega)
            · -- n <= 44249339941847
              exact RamareSaouter2003.prime_interval_nat_ladder_c03433 n (by omega) (by omega)
          · -- n <= 44140104828301
            exact RamareSaouter2003.prime_interval_nat_ladder_c03432 n (by omega) (by omega)
      · -- n <= 44031139375471
        rcases Nat.lt_or_ge 43705854332843 n with h8 | h8
        · -- n > 43705854332843
          rcases Nat.lt_or_ge 43814014791031 n with h10 | h10
          · -- n > 43814014791031
            rcases Nat.lt_or_ge 43922442917737 n with h12 | h12
            · -- n > 43922442917737
              exact RamareSaouter2003.prime_interval_nat_ladder_c03431 n (by omega) (by omega)
            · -- n <= 43922442917737
              exact RamareSaouter2003.prime_interval_nat_ladder_c03430 n (by omega) (by omega)
          · -- n <= 43814014791031
            exact RamareSaouter2003.prime_interval_nat_ladder_c03429 n (by omega) (by omega)
        · -- n <= 43705854332843
          rcases Nat.lt_or_ge 43490333780969 n with h10 | h10
          · -- n > 43490333780969
            rcases Nat.lt_or_ge 43597960882529 n with h12 | h12
            · -- n > 43597960882529
              exact RamareSaouter2003.prime_interval_nat_ladder_c03428 n (by omega) (by omega)
            · -- n <= 43597960882529
              exact RamareSaouter2003.prime_interval_nat_ladder_c03427 n (by omega) (by omega)
          · -- n <= 43490333780969
            exact RamareSaouter2003.prime_interval_nat_ladder_c03426 n (by omega) (by omega)
  · -- n <= 43382972370511
    rcases Nat.lt_or_ge 42011155698049 n with h4 | h4
    · -- n > 42011155698049
      rcases Nat.lt_or_ge 42638826958667 n with h6 | h6
      · -- n > 42638826958667
        rcases Nat.lt_or_ge 42956170546969 n with h8 | h8
        · -- n > 42956170546969
          rcases Nat.lt_or_ge 43169044001089 n with h10 | h10
          · -- n > 43169044001089
            rcases Nat.lt_or_ge 43275875995321 n with h12 | h12
            · -- n > 43275875995321
              exact RamareSaouter2003.prime_interval_nat_ladder_c03425 n (by omega) (by omega)
            · -- n <= 43275875995321
              exact RamareSaouter2003.prime_interval_nat_ladder_c03424 n (by omega) (by omega)
          · -- n <= 43169044001089
            rcases Nat.lt_or_ge 43062475735229 n with h12 | h12
            · -- n > 43062475735229
              exact RamareSaouter2003.prime_interval_nat_ladder_c03423 n (by omega) (by omega)
            · -- n <= 43062475735229
              exact RamareSaouter2003.prime_interval_nat_ladder_c03422 n (by omega) (by omega)
        · -- n <= 42956170546969
          rcases Nat.lt_or_ge 42744346805627 n with h10 | h10
          · -- n > 42744346805627
            rcases Nat.lt_or_ge 42850127786317 n with h12 | h12
            · -- n > 42850127786317
              exact RamareSaouter2003.prime_interval_nat_ladder_c03421 n (by omega) (by omega)
            · -- n <= 42850127786317
              exact RamareSaouter2003.prime_interval_nat_ladder_c03420 n (by omega) (by omega)
          · -- n <= 42744346805627
            exact RamareSaouter2003.prime_interval_nat_ladder_c03419 n (by omega) (by omega)
      · -- n <= 42638826958667
        rcases Nat.lt_or_ge 42323827782361 n with h8 | h8
        · -- n > 42323827782361
          rcases Nat.lt_or_ge 42428568089429 n with h10 | h10
          · -- n > 42428568089429
            rcases Nat.lt_or_ge 42533567601067 n with h12 | h12
            · -- n > 42533567601067
              exact RamareSaouter2003.prime_interval_nat_ladder_c03418 n (by omega) (by omega)
            · -- n <= 42533567601067
              exact RamareSaouter2003.prime_interval_nat_ladder_c03417 n (by omega) (by omega)
          · -- n <= 42428568089429
            exact RamareSaouter2003.prime_interval_nat_ladder_c03416 n (by omega) (by omega)
        · -- n <= 42323827782361
          rcases Nat.lt_or_ge 42115122224183 n with h10 | h10
          · -- n > 42115122224183
            rcases Nat.lt_or_ge 42219346040041 n with h12 | h12
            · -- n > 42219346040041
              exact RamareSaouter2003.prime_interval_nat_ladder_c03415 n (by omega) (by omega)
            · -- n <= 42219346040041
              exact RamareSaouter2003.prime_interval_nat_ladder_c03414 n (by omega) (by omega)
          · -- n <= 42115122224183
            exact RamareSaouter2003.prime_interval_nat_ladder_c03413 n (by omega) (by omega)
    · -- n <= 42011155698049
      rcases Nat.lt_or_ge 41392724166617 n with h6 | h6
      · -- n > 41392724166617
        rcases Nat.lt_or_ge 41700793514591 n with h8 | h8
        · -- n > 41700793514591
          rcases Nat.lt_or_ge 41803991976119 n with h10 | h10
          · -- n > 41803991976119
            rcases Nat.lt_or_ge 41907445826689 n with h12 | h12
            · -- n > 41907445826689
              exact RamareSaouter2003.prime_interval_nat_ladder_c03412 n (by omega) (by omega)
            · -- n <= 41907445826689
              exact RamareSaouter2003.prime_interval_nat_ladder_c03411 n (by omega) (by omega)
          · -- n <= 41803991976119
            exact RamareSaouter2003.prime_interval_nat_ladder_c03410 n (by omega) (by omega)
        · -- n <= 41700793514591
          rcases Nat.lt_or_ge 41495160237877 n with h10 | h10
          · -- n > 41495160237877
            rcases Nat.lt_or_ge 41597849811431 n with h12 | h12
            · -- n > 41597849811431
              exact RamareSaouter2003.prime_interval_nat_ladder_c03409 n (by omega) (by omega)
            · -- n <= 41597849811431
              exact RamareSaouter2003.prime_interval_nat_ladder_c03408 n (by omega) (by omega)
          · -- n <= 41495160237877
            exact RamareSaouter2003.prime_interval_nat_ladder_c03407 n (by omega) (by omega)
      · -- n <= 41392724166617
        rcases Nat.lt_or_ge 41086930716071 n with h8 | h8
        · -- n > 41086930716071
          rcases Nat.lt_or_ge 41188610029267 n with h10 | h10
          · -- n > 41188610029267
            rcases Nat.lt_or_ge 41290540971943 n with h12 | h12
            · -- n > 41290540971943
              exact RamareSaouter2003.prime_interval_nat_ladder_c03406 n (by omega) (by omega)
            · -- n <= 41290540971943
              exact RamareSaouter2003.prime_interval_nat_ladder_c03405 n (by omega) (by omega)
          · -- n <= 41188610029267
            exact RamareSaouter2003.prime_interval_nat_ladder_c03404 n (by omega) (by omega)
        · -- n <= 41086930716071
          rcases Nat.lt_or_ge 40884324495037 n with h10 | h10
          · -- n > 40884324495037
            rcases Nat.lt_or_ge 40985502411233 n with h12 | h12
            · -- n > 40985502411233
              exact RamareSaouter2003.prime_interval_nat_ladder_c03403 n (by omega) (by omega)
            · -- n <= 40985502411233
              exact RamareSaouter2003.prime_interval_nat_ladder_c03402 n (by omega) (by omega)
          · -- n <= 40884324495037
            exact RamareSaouter2003.prime_interval_nat_ladder_c03401 n (by omega) (by omega)
