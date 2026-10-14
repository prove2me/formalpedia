-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp168
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T14:34:36.627986+00:00
-- url     : https://prove2.me/submissions/a92b0770-925d-451b-8a6c-338f4eed7abb

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08345
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08350
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08374

theorem solution (n : Nat)
    (hn : 34149953953884191081 < n) (hupper : n <= 38490349635789503129) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 36211019110965740051 n with h2 | h2
  · -- n > 36211019110965740051
    rcases Nat.lt_or_ge 37287742229152126651 n with h4 | h4
    · -- n > 37287742229152126651
      rcases Nat.lt_or_ge 37838050265856722197 n with h6 | h6
      · -- n > 37838050265856722197
        rcases Nat.lt_or_ge 38116242021498197597 n with h8 | h8
        · -- n > 38116242021498197597
          rcases Nat.lt_or_ge 38302839043089010909 n with h10 | h10
          · -- n > 38302839043089010909
            rcases Nat.lt_or_ge 38396480037726709361 n with h12 | h12
            · -- n > 38396480037726709361
              exact RamareSaouter2003.prime_interval_nat_ladder_c08374 n (by omega) (by omega)
            · -- n <= 38396480037726709361
              exact RamareSaouter2003.prime_interval_nat_ladder_c08373 n (by omega) (by omega)
          · -- n <= 38302839043089010909
            rcases Nat.lt_or_ge 38209426530389696509 n with h12 | h12
            · -- n > 38209426530389696509
              exact RamareSaouter2003.prime_interval_nat_ladder_c08372 n (by omega) (by omega)
            · -- n <= 38209426530389696509
              exact RamareSaouter2003.prime_interval_nat_ladder_c08371 n (by omega) (by omega)
        · -- n <= 38116242021498197597
          rcases Nat.lt_or_ge 37930553687926540051 n with h10 | h10
          · -- n > 37930553687926540051
            rcases Nat.lt_or_ge 38023284504698725963 n with h12 | h12
            · -- n > 38023284504698725963
              exact RamareSaouter2003.prime_interval_nat_ladder_c08370 n (by omega) (by omega)
            · -- n <= 38023284504698725963
              exact RamareSaouter2003.prime_interval_nat_ladder_c08369 n (by omega) (by omega)
          · -- n <= 37930553687926540051
            exact RamareSaouter2003.prime_interval_nat_ladder_c08368 n (by omega) (by omega)
      · -- n <= 37838050265856722197
        rcases Nat.lt_or_ge 37561888812432904529 n with h8 | h8
        · -- n > 37561888812432904529
          rcases Nat.lt_or_ge 37653718318372828769 n with h10 | h10
          · -- n > 37653718318372828769
            rcases Nat.lt_or_ge 37745771653462941643 n with h12 | h12
            · -- n > 37745771653462941643
              exact RamareSaouter2003.prime_interval_nat_ladder_c08367 n (by omega) (by omega)
            · -- n <= 37745771653462941643
              exact RamareSaouter2003.prime_interval_nat_ladder_c08366 n (by omega) (by omega)
          · -- n <= 37653718318372828769
            exact RamareSaouter2003.prime_interval_nat_ladder_c08365 n (by omega) (by omega)
        · -- n <= 37561888812432904529
          rcases Nat.lt_or_ge 37378901531905840661 n with h10 | h10
          · -- n > 37378901531905840661
            rcases Nat.lt_or_ge 37470283415137392217 n with h12 | h12
            · -- n > 37470283415137392217
              exact RamareSaouter2003.prime_interval_nat_ladder_c08364 n (by omega) (by omega)
            · -- n <= 37470283415137392217
              exact RamareSaouter2003.prime_interval_nat_ladder_c08363 n (by omega) (by omega)
          · -- n <= 37378901531905840661
            exact RamareSaouter2003.prime_interval_nat_ladder_c08362 n (by omega) (by omega)
    · -- n <= 37287742229152126651
      rcases Nat.lt_or_ge 36745437079804527307 n with h6 | h6
      · -- n > 36745437079804527307
        rcases Nat.lt_or_ge 37015596550183691117 n with h8 | h8
        · -- n > 37015596550183691117
          rcases Nat.lt_or_ge 37106090467451529893 n with h10 | h10
          · -- n > 37106090467451529893
            rcases Nat.lt_or_ge 37196805440914715749 n with h12 | h12
            · -- n > 37196805440914715749
              exact RamareSaouter2003.prime_interval_nat_ladder_c08361 n (by omega) (by omega)
            · -- n <= 37196805440914715749
              exact RamareSaouter2003.prime_interval_nat_ladder_c08360 n (by omega) (by omega)
          · -- n <= 37106090467451529893
            exact RamareSaouter2003.prime_interval_nat_ladder_c08359 n (by omega) (by omega)
        · -- n <= 37015596550183691117
          rcases Nat.lt_or_ge 36835270556978257081 n with h10 | h10
          · -- n > 36835270556978257081
            rcases Nat.lt_or_ge 36925323271132796009 n with h12 | h12
            · -- n > 36925323271132796009
              exact RamareSaouter2003.prime_interval_nat_ladder_c08358 n (by omega) (by omega)
            · -- n <= 36925323271132796009
              exact RamareSaouter2003.prime_interval_nat_ladder_c08357 n (by omega) (by omega)
          · -- n <= 36835270556978257081
            exact RamareSaouter2003.prime_interval_nat_ladder_c08356 n (by omega) (by omega)
      · -- n <= 36745437079804527307
        rcases Nat.lt_or_ge 36477249448742504291 n with h8 | h8
        · -- n > 36477249448742504291
          rcases Nat.lt_or_ge 36566427289380794879 n with h10 | h10
          · -- n > 36566427289380794879
            rcases Nat.lt_or_ge 36655822669571819299 n with h12 | h12
            · -- n > 36655822669571819299
              exact RamareSaouter2003.prime_interval_nat_ladder_c08355 n (by omega) (by omega)
            · -- n <= 36655822669571819299
              exact RamareSaouter2003.prime_interval_nat_ladder_c08354 n (by omega) (by omega)
          · -- n <= 36566427289380794879
            exact RamareSaouter2003.prime_interval_nat_ladder_c08353 n (by omega) (by omega)
        · -- n <= 36477249448742504291
          rcases Nat.lt_or_ge 36299545678845736943 n with h10 | h10
          · -- n > 36299545678845736943
            rcases Nat.lt_or_ge 36388289064595958797 n with h12 | h12
            · -- n > 36388289064595958797
              exact RamareSaouter2003.prime_interval_nat_ladder_c08352 n (by omega) (by omega)
            · -- n <= 36388289064595958797
              exact RamareSaouter2003.prime_interval_nat_ladder_c08351 n (by omega) (by omega)
          · -- n <= 36299545678845736943
            exact RamareSaouter2003.prime_interval_nat_ladder_c08350 n (by omega) (by omega)
  · -- n <= 36211019110965740051
    rcases Nat.lt_or_ge 35165390163046719899 n with h4 | h4
    · -- n > 35165390163046719899
      rcases Nat.lt_or_ge 35684375775850238191 n with h6 | h6
      · -- n > 35684375775850238191
        rcases Nat.lt_or_ge 35946732600096872629 n with h8 | h8
        · -- n > 35946732600096872629
          rcases Nat.lt_or_ge 36034613362207440863 n with h10 | h10
          · -- n > 36034613362207440863
            rcases Nat.lt_or_ge 36122708133412986289 n with h12 | h12
            · -- n > 36122708133412986289
              exact RamareSaouter2003.prime_interval_nat_ladder_c08349 n (by omega) (by omega)
            · -- n <= 36122708133412986289
              exact RamareSaouter2003.prime_interval_nat_ladder_c08348 n (by omega) (by omega)
          · -- n <= 36034613362207440863
            exact RamareSaouter2003.prime_interval_nat_ladder_c08347 n (by omega) (by omega)
        · -- n <= 35946732600096872629
          rcases Nat.lt_or_ge 35771615168030104901 n with h10 | h10
          · -- n > 35771615168030104901
            rcases Nat.lt_or_ge 35859066606265250687 n with h12 | h12
            · -- n > 35859066606265250687
              exact RamareSaouter2003.prime_interval_nat_ladder_c08346 n (by omega) (by omega)
            · -- n <= 35859066606265250687
              exact RamareSaouter2003.prime_interval_nat_ladder_c08345 n (by omega) (by omega)
          · -- n <= 35771615168030104901
            exact RamareSaouter2003.prime_interval_nat_ladder_c08344 n (by omega) (by omega)
      · -- n <= 35684375775850238191
        rcases Nat.lt_or_ge 35423932099221691177 n with h8 | h8
        · -- n > 35423932099221691177
          rcases Nat.lt_or_ge 35510534695243968161 n with h10 | h10
          · -- n > 35510534695243968161
            rcases Nat.lt_or_ge 35597349152943368239 n with h12 | h12
            · -- n > 35597349152943368239
              exact RamareSaouter2003.prime_interval_nat_ladder_c08343 n (by omega) (by omega)
            · -- n <= 35597349152943368239
              exact RamareSaouter2003.prime_interval_nat_ladder_c08342 n (by omega) (by omega)
          · -- n <= 35510534695243968161
            exact RamareSaouter2003.prime_interval_nat_ladder_c08341 n (by omega) (by omega)
        · -- n <= 35423932099221691177
          rcases Nat.lt_or_ge 35251359821101357001 n with h10 | h10
          · -- n > 35251359821101357001
            rcases Nat.lt_or_ge 35337540689963803051 n with h12 | h12
            · -- n > 35337540689963803051
              exact RamareSaouter2003.prime_interval_nat_ladder_c08340 n (by omega) (by omega)
            · -- n <= 35337540689963803051
              exact RamareSaouter2003.prime_interval_nat_ladder_c08339 n (by omega) (by omega)
          · -- n <= 35251359821101357001
            exact RamareSaouter2003.prime_interval_nat_ladder_c08338 n (by omega) (by omega)
    · -- n <= 35165390163046719899
      rcases Nat.lt_or_ge 34653953957107184411 n with h6 | h6
      · -- n > 34653953957107184411
        rcases Nat.lt_or_ge 34908734994686732761 n with h8 | h8
        · -- n > 34908734994686732761
          rcases Nat.lt_or_ge 34994077895241494023 n with h10 | h10
          · -- n > 34994077895241494023
            rcases Nat.lt_or_ge 35079629443167444139 n with h12 | h12
            · -- n > 35079629443167444139
              exact RamareSaouter2003.prime_interval_nat_ladder_c08337 n (by omega) (by omega)
            · -- n <= 35079629443167444139
              exact RamareSaouter2003.prime_interval_nat_ladder_c08336 n (by omega) (by omega)
          · -- n <= 34994077895241494023
            exact RamareSaouter2003.prime_interval_nat_ladder_c08335 n (by omega) (by omega)
        · -- n <= 34908734994686732761
          rcases Nat.lt_or_ge 34738673743481076883 n with h10 | h10
          · -- n > 34738673743481076883
            rcases Nat.lt_or_ge 34823600291702163941 n with h12 | h12
            · -- n > 34823600291702163941
              exact RamareSaouter2003.prime_interval_nat_ladder_c08334 n (by omega) (by omega)
            · -- n <= 34823600291702163941
              exact RamareSaouter2003.prime_interval_nat_ladder_c08333 n (by omega) (by omega)
          · -- n <= 34738673743481076883
            exact RamareSaouter2003.prime_interval_nat_ladder_c08332 n (by omega) (by omega)
      · -- n <= 34653953957107184411
        rcases Nat.lt_or_ge 34401031284487516147 n with h8 | h8
        · -- n > 34401031284487516147
          rcases Nat.lt_or_ge 34485132604587298157 n with h10 | h10
          · -- n > 34485132604587298157
            rcases Nat.lt_or_ge 34569440201229348797 n with h12 | h12
            · -- n > 34569440201229348797
              exact RamareSaouter2003.prime_interval_nat_ladder_c08331 n (by omega) (by omega)
            · -- n <= 34569440201229348797
              exact RamareSaouter2003.prime_interval_nat_ladder_c08330 n (by omega) (by omega)
          · -- n <= 34485132604587298157
            exact RamareSaouter2003.prime_interval_nat_ladder_c08329 n (by omega) (by omega)
        · -- n <= 34401031284487516147
          rcases Nat.lt_or_ge 34233442162317985823 n with h10 | h10
          · -- n > 34233442162317985823
            rcases Nat.lt_or_ge 34317134348948354963 n with h12 | h12
            · -- n > 34317134348948354963
              exact RamareSaouter2003.prime_interval_nat_ladder_c08328 n (by omega) (by omega)
            · -- n <= 34317134348948354963
              exact RamareSaouter2003.prime_interval_nat_ladder_c08327 n (by omega) (by omega)
          · -- n <= 34233442162317985823
            exact RamareSaouter2003.prime_interval_nat_ladder_c08326 n (by omega) (by omega)
