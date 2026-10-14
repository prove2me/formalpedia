-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp147
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T05:52:09.164049+00:00
-- url     : https://prove2.me/submissions/a5572bd6-2bbc-4b65-ad14-f191246af634

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07300
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07325
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07345

theorem solution (n : Nat)
    (hn : 2051624730942508333 < n) (hupper : n <= 2356479914408562661) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2195669145254760517 n with h2 | h2
  · -- n > 2195669145254760517
    rcases Nat.lt_or_ge 2271440741335785203 n with h4 | h4
    · -- n > 2271440741335785203
      rcases Nat.lt_or_ge 2310301342825695313 n with h6 | h6
      · -- n > 2310301342825695313
        rcases Nat.lt_or_ge 2329980286465050781 n with h8 | h8
        · -- n > 2329980286465050781
          rcases Nat.lt_or_ge 2343192609143381663 n with h10 | h10
          · -- n > 2343192609143381663
            rcases Nat.lt_or_ge 2349826901328692593 n with h12 | h12
            · -- n > 2349826901328692593
              exact RamareSaouter2003.prime_interval_nat_ladder_c07345 n (by omega) (by omega)
            · -- n <= 2349826901328692593
              exact RamareSaouter2003.prime_interval_nat_ladder_c07344 n (by omega) (by omega)
          · -- n <= 2343192609143381663
            rcases Nat.lt_or_ge 2336577071880840673 n with h12 | h12
            · -- n > 2336577071880840673
              exact RamareSaouter2003.prime_interval_nat_ladder_c07343 n (by omega) (by omega)
            · -- n <= 2336577071880840673
              exact RamareSaouter2003.prime_interval_nat_ladder_c07342 n (by omega) (by omega)
        · -- n <= 2329980286465050781
          rcases Nat.lt_or_ge 2316842482590597977 n with h10 | h10
          · -- n > 2316842482590597977
            rcases Nat.lt_or_ge 2323402148940595717 n with h12 | h12
            · -- n > 2323402148940595717
              exact RamareSaouter2003.prime_interval_nat_ladder_c07341 n (by omega) (by omega)
            · -- n <= 2323402148940595717
              exact RamareSaouter2003.prime_interval_nat_ladder_c07340 n (by omega) (by omega)
          · -- n <= 2316842482590597977
            exact RamareSaouter2003.prime_interval_nat_ladder_c07339 n (by omega) (by omega)
      · -- n <= 2310301342825695313
        rcases Nat.lt_or_ge 2290788697137365059 n with h8 | h8
        · -- n > 2290788697137365059
          rcases Nat.lt_or_ge 2297274613713572707 n with h10 | h10
          · -- n > 2297274613713572707
            rcases Nat.lt_or_ge 2303778672309292313 n with h12 | h12
            · -- n > 2303778672309292313
              exact RamareSaouter2003.prime_interval_nat_ladder_c07338 n (by omega) (by omega)
            · -- n <= 2303778672309292313
              exact RamareSaouter2003.prime_interval_nat_ladder_c07337 n (by omega) (by omega)
          · -- n <= 2297274613713572707
            exact RamareSaouter2003.prime_interval_nat_ladder_c07336 n (by omega) (by omega)
        · -- n <= 2290788697137365059
          rcases Nat.lt_or_ge 2277871772550226129 n with h10 | h10
          · -- n > 2277871772550226129
            rcases Nat.lt_or_ge 2284321090328566979 n with h12 | h12
            · -- n > 2284321090328566979
              exact RamareSaouter2003.prime_interval_nat_ladder_c07335 n (by omega) (by omega)
            · -- n <= 2284321090328566979
              exact RamareSaouter2003.prime_interval_nat_ladder_c07334 n (by omega) (by omega)
          · -- n <= 2277871772550226129
            exact RamareSaouter2003.prime_interval_nat_ladder_c07333 n (by omega) (by omega)
    · -- n <= 2271440741335785203
      rcases Nat.lt_or_ge 2233233667003948333 n with h6 | h6
      · -- n > 2233233667003948333
        rcases Nat.lt_or_ge 2252256169564224841 n with h8 | h8
        · -- n > 2252256169564224841
          rcases Nat.lt_or_ge 2258632898333143859 n with h10 | h10
          · -- n > 2258632898333143859
            rcases Nat.lt_or_ge 2265027752765754437 n with h12 | h12
            · -- n > 2265027752765754437
              exact RamareSaouter2003.prime_interval_nat_ladder_c07332 n (by omega) (by omega)
            · -- n <= 2265027752765754437
              exact RamareSaouter2003.prime_interval_nat_ladder_c07331 n (by omega) (by omega)
          · -- n <= 2258632898333143859
            exact RamareSaouter2003.prime_interval_nat_ladder_c07330 n (by omega) (by omega)
        · -- n <= 2252256169564224841
          rcases Nat.lt_or_ge 2239556500522117121 n with h10 | h10
          · -- n > 2239556500522117121
            rcases Nat.lt_or_ge 2245897353951485141 n with h12 | h12
            · -- n > 2245897353951485141
              exact RamareSaouter2003.prime_interval_nat_ladder_c07329 n (by omega) (by omega)
            · -- n <= 2245897353951485141
              exact RamareSaouter2003.prime_interval_nat_ladder_c07328 n (by omega) (by omega)
          · -- n <= 2239556500522117121
            exact RamareSaouter2003.prime_interval_nat_ladder_c07327 n (by omega) (by omega)
      · -- n <= 2233233667003948333
        rcases Nat.lt_or_ge 2214371761048414883 n with h8 | h8
        · -- n > 2214371761048414883
          rcases Nat.lt_or_ge 2220641261776254181 n with h10 | h10
          · -- n > 2220641261776254181
            rcases Nat.lt_or_ge 2226928549024396627 n with h12 | h12
            · -- n > 2226928549024396627
              exact RamareSaouter2003.prime_interval_nat_ladder_c07326 n (by omega) (by omega)
            · -- n <= 2226928549024396627
              exact RamareSaouter2003.prime_interval_nat_ladder_c07325 n (by omega) (by omega)
          · -- n <= 2220641261776254181
            exact RamareSaouter2003.prime_interval_nat_ladder_c07324 n (by omega) (by omega)
        · -- n <= 2214371761048414883
          rcases Nat.lt_or_ge 2201885731428918923 n with h10 | h10
          · -- n > 2201885731428918923
            rcases Nat.lt_or_ge 2208119946877753679 n with h12 | h12
            · -- n > 2208119946877753679
              exact RamareSaouter2003.prime_interval_nat_ladder_c07323 n (by omega) (by omega)
            · -- n <= 2208119946877753679
              exact RamareSaouter2003.prime_interval_nat_ladder_c07322 n (by omega) (by omega)
          · -- n <= 2201885731428918923
            exact RamareSaouter2003.prime_interval_nat_ladder_c07321 n (by omega) (by omega)
  · -- n <= 2195669145254760517
    rcases Nat.lt_or_ge 2122425292087592519 n with h4 | h4
    · -- n > 2122425292087592519
      rcases Nat.lt_or_ge 2158736695869543701 n with h6 | h6
      · -- n > 2158736695869543701
        rcases Nat.lt_or_ge 2177124596465099509 n with h8 | h8
        · -- n > 2177124596465099509
          rcases Nat.lt_or_ge 2183288703869581573 n with h10 | h10
          · -- n > 2183288703869581573
            rcases Nat.lt_or_ge 2189470204944876437 n with h12 | h12
            · -- n > 2189470204944876437
              exact RamareSaouter2003.prime_interval_nat_ladder_c07320 n (by omega) (by omega)
            · -- n <= 2189470204944876437
              exact RamareSaouter2003.prime_interval_nat_ladder_c07319 n (by omega) (by omega)
          · -- n <= 2183288703869581573
            exact RamareSaouter2003.prime_interval_nat_ladder_c07318 n (by omega) (by omega)
        · -- n <= 2177124596465099509
          rcases Nat.lt_or_ge 2164848716123149157 n with h10 | h10
          · -- n > 2164848716123149157
            rcases Nat.lt_or_ge 2170978028756443847 n with h12 | h12
            · -- n > 2170978028756443847
              exact RamareSaouter2003.prime_interval_nat_ladder_c07317 n (by omega) (by omega)
            · -- n <= 2170978028756443847
              exact RamareSaouter2003.prime_interval_nat_ladder_c07316 n (by omega) (by omega)
          · -- n <= 2164848716123149157
            exact RamareSaouter2003.prime_interval_nat_ladder_c07315 n (by omega) (by omega)
      · -- n <= 2158736695869543701
        rcases Nat.lt_or_ge 2140503933931876837 n with h8 | h8
        · -- n > 2140503933931876837
          rcases Nat.lt_or_ge 2146564358674668769 n with h10 | h10
          · -- n > 2146564358674668769
            rcases Nat.lt_or_ge 2152641904552713737 n with h12 | h12
            · -- n > 2152641904552713737
              exact RamareSaouter2003.prime_interval_nat_ladder_c07314 n (by omega) (by omega)
            · -- n <= 2152641904552713737
              exact RamareSaouter2003.prime_interval_nat_ladder_c07313 n (by omega) (by omega)
          · -- n <= 2146564358674668769
            exact RamareSaouter2003.prime_interval_nat_ladder_c07312 n (by omega) (by omega)
        · -- n <= 2140503933931876837
          rcases Nat.lt_or_ge 2128434512847605323 n with h10 | h10
          · -- n > 2128434512847605323
            rcases Nat.lt_or_ge 2134460708009669983 n with h12 | h12
            · -- n > 2134460708009669983
              exact RamareSaouter2003.prime_interval_nat_ladder_c07311 n (by omega) (by omega)
            · -- n <= 2134460708009669983
              exact RamareSaouter2003.prime_interval_nat_ladder_c07310 n (by omega) (by omega)
          · -- n <= 2128434512847605323
            exact RamareSaouter2003.prime_interval_nat_ladder_c07309 n (by omega) (by omega)
    · -- n <= 2122425292087592519
      rcases Nat.lt_or_ge 2086724809523816857 n with h6 | h6
      · -- n > 2086724809523816857
        rcases Nat.lt_or_ge 2104499460421590593 n with h8 | h8
        · -- n > 2104499460421590593
          rcases Nat.lt_or_ge 2110457935800542491 n with h10 | h10
          · -- n > 2110457935800542491
            rcases Nat.lt_or_ge 2116433231154202139 n with h12 | h12
            · -- n > 2116433231154202139
              exact RamareSaouter2003.prime_interval_nat_ladder_c07308 n (by omega) (by omega)
            · -- n <= 2116433231154202139
              exact RamareSaouter2003.prime_interval_nat_ladder_c07307 n (by omega) (by omega)
          · -- n <= 2110457935800542491
            exact RamareSaouter2003.prime_interval_nat_ladder_c07306 n (by omega) (by omega)
        · -- n <= 2104499460421590593
          rcases Nat.lt_or_ge 2092632950512937383 n with h10 | h10
          · -- n > 2092632950512937383
            rcases Nat.lt_or_ge 2098557822293793323 n with h12 | h12
            · -- n > 2098557822293793323
              exact RamareSaouter2003.prime_interval_nat_ladder_c07305 n (by omega) (by omega)
            · -- n <= 2098557822293793323
              exact RamareSaouter2003.prime_interval_nat_ladder_c07304 n (by omega) (by omega)
          · -- n <= 2092632950512937383
            exact RamareSaouter2003.prime_interval_nat_ladder_c07303 n (by omega) (by omega)
      · -- n <= 2086724809523816857
        rcases Nat.lt_or_ge 2069100372471414731 n with h8 | h8
        · -- n > 2069100372471414731
          rcases Nat.lt_or_ge 2074958596237106387 n with h10 | h10
          · -- n > 2074958596237106387
            rcases Nat.lt_or_ge 2080833407372352587 n with h12 | h12
            · -- n > 2080833407372352587
              exact RamareSaouter2003.prime_interval_nat_ladder_c07302 n (by omega) (by omega)
            · -- n <= 2080833407372352587
              exact RamareSaouter2003.prime_interval_nat_ladder_c07301 n (by omega) (by omega)
          · -- n <= 2074958596237106387
            exact RamareSaouter2003.prime_interval_nat_ladder_c07300 n (by omega) (by omega)
        · -- n <= 2069100372471414731
          rcases Nat.lt_or_ge 2057433494882661361 n with h10 | h10
          · -- n > 2057433494882661361
            rcases Nat.lt_or_ge 2063258654945668357 n with h12 | h12
            · -- n > 2063258654945668357
              exact RamareSaouter2003.prime_interval_nat_ladder_c07299 n (by omega) (by omega)
            · -- n <= 2063258654945668357
              exact RamareSaouter2003.prime_interval_nat_ladder_c07298 n (by omega) (by omega)
          · -- n <= 2057433494882661361
            exact RamareSaouter2003.prime_interval_nat_ladder_c07297 n (by omega) (by omega)
