-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp106
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T15:34:26.288707+00:00
-- url     : https://prove2.me/submissions/00da8e45-fd51-422a-ae02-4fe5aa2c7dfe

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05276
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05296
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05300

theorem solution (n : Nat)
    (hn : 6309300846480967 < n) (hupper : n <= 7267171176941339) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 6771332751424651 n with h2 | h2
  · -- n > 6771332751424651
    rcases Nat.lt_or_ge 7004959990161509 n with h4 | h4
    · -- n > 7004959990161509
      rcases Nat.lt_or_ge 7124779669747349 n with h6 | h6
      · -- n > 7124779669747349
        rcases Nat.lt_or_ge 7185456816488521 n with h8 | h8
        · -- n > 7185456816488521
          rcases Nat.lt_or_ge 7226195975540449 n with h10 | h10
          · -- n > 7226195975540449
            rcases Nat.lt_or_ge 7246654628343959 n with h12 | h12
            · -- n > 7246654628343959
              exact RamareSaouter2003.prime_interval_nat_ladder_c05300 n (by omega) (by omega)
            · -- n <= 7246654628343959
              exact RamareSaouter2003.prime_interval_nat_ladder_c05299 n (by omega) (by omega)
          · -- n <= 7226195975540449
            rcases Nat.lt_or_ge 7205798164920133 n with h12 | h12
            · -- n > 7205798164920133
              exact RamareSaouter2003.prime_interval_nat_ladder_c05298 n (by omega) (by omega)
            · -- n <= 7205798164920133
              exact RamareSaouter2003.prime_interval_nat_ladder_c05297 n (by omega) (by omega)
        · -- n <= 7185456816488521
          rcases Nat.lt_or_ge 7144948114751459 n with h10 | h10
          · -- n > 7144948114751459
            rcases Nat.lt_or_ge 7165170460496879 n with h12 | h12
            · -- n > 7165170460496879
              exact RamareSaouter2003.prime_interval_nat_ladder_c05296 n (by omega) (by omega)
            · -- n <= 7165170460496879
              exact RamareSaouter2003.prime_interval_nat_ladder_c05295 n (by omega) (by omega)
          · -- n <= 7144948114751459
            exact RamareSaouter2003.prime_interval_nat_ladder_c05294 n (by omega) (by omega)
      · -- n <= 7124779669747349
        rcases Nat.lt_or_ge 7064619181159831 n with h8 | h8
        · -- n > 7064619181159831
          rcases Nat.lt_or_ge 7084621050034597 n with h10 | h10
          · -- n > 7084621050034597
            rcases Nat.lt_or_ge 7104667031356547 n with h12 | h12
            · -- n > 7104667031356547
              exact RamareSaouter2003.prime_interval_nat_ladder_c05293 n (by omega) (by omega)
            · -- n <= 7104667031356547
              exact RamareSaouter2003.prime_interval_nat_ladder_c05292 n (by omega) (by omega)
          · -- n <= 7084621050034597
            exact RamareSaouter2003.prime_interval_nat_ladder_c05291 n (by omega) (by omega)
        · -- n <= 7064619181159831
          rcases Nat.lt_or_ge 7024786430383121 n with h10 | h10
          · -- n > 7024786430383121
            rcases Nat.lt_or_ge 7044674454543679 n with h12 | h12
            · -- n > 7044674454543679
              exact RamareSaouter2003.prime_interval_nat_ladder_c05290 n (by omega) (by omega)
            · -- n <= 7044674454543679
              exact RamareSaouter2003.prime_interval_nat_ladder_c05289 n (by omega) (by omega)
          · -- n <= 7024786430383121
            exact RamareSaouter2003.prime_interval_nat_ladder_c05288 n (by omega) (by omega)
    · -- n <= 7004959990161509
      rcases Nat.lt_or_ge 6887151395445193 n with h6 | h6
      · -- n > 6887151395445193
        rcases Nat.lt_or_ge 6945803303095607 n with h8 | h8
        · -- n > 6945803303095607
          rcases Nat.lt_or_ge 6965467620857807 n with h10 | h10
          · -- n > 6965467620857807
            rcases Nat.lt_or_ge 6985188986346463 n with h12 | h12
            · -- n > 6985188986346463
              exact RamareSaouter2003.prime_interval_nat_ladder_c05287 n (by omega) (by omega)
            · -- n <= 6985188986346463
              exact RamareSaouter2003.prime_interval_nat_ladder_c05286 n (by omega) (by omega)
          · -- n <= 6965467620857807
            exact RamareSaouter2003.prime_interval_nat_ladder_c05285 n (by omega) (by omega)
        · -- n <= 6945803303095607
          rcases Nat.lt_or_ge 6906645482103649 n with h10 | h10
          · -- n > 6906645482103649
            rcases Nat.lt_or_ge 6926194407003631 n with h12 | h12
            · -- n > 6926194407003631
              exact RamareSaouter2003.prime_interval_nat_ladder_c05284 n (by omega) (by omega)
            · -- n <= 6926194407003631
              exact RamareSaouter2003.prime_interval_nat_ladder_c05283 n (by omega) (by omega)
          · -- n <= 6906645482103649
            exact RamareSaouter2003.prime_interval_nat_ladder_c05282 n (by omega) (by omega)
      · -- n <= 6887151395445193
        rcases Nat.lt_or_ge 6829006013873819 n with h8 | h8
        · -- n > 6829006013873819
          rcases Nat.lt_or_ge 6848340231338681 n with h10 | h10
          · -- n > 6848340231338681
            rcases Nat.lt_or_ge 6867723322707623 n with h12 | h12
            · -- n > 6867723322707623
              exact RamareSaouter2003.prime_interval_nat_ladder_c05281 n (by omega) (by omega)
            · -- n <= 6867723322707623
              exact RamareSaouter2003.prime_interval_nat_ladder_c05280 n (by omega) (by omega)
          · -- n <= 6848340231338681
            exact RamareSaouter2003.prime_interval_nat_ladder_c05279 n (by omega) (by omega)
        · -- n <= 6829006013873819
          rcases Nat.lt_or_ge 6790503458655991 n with h10 | h10
          · -- n > 6790503458655991
            rcases Nat.lt_or_ge 6809726196523559 n with h12 | h12
            · -- n > 6809726196523559
              exact RamareSaouter2003.prime_interval_nat_ladder_c05278 n (by omega) (by omega)
            · -- n <= 6809726196523559
              exact RamareSaouter2003.prime_interval_nat_ladder_c05277 n (by omega) (by omega)
          · -- n <= 6790503458655991
            exact RamareSaouter2003.prime_interval_nat_ladder_c05276 n (by omega) (by omega)
  · -- n <= 6771332751424651
    rcases Nat.lt_or_ge 6527009459080501 n with h4 | h4
    · -- n > 6527009459080501
      rcases Nat.lt_or_ge 6638667628724569 n with h6 | h6
      · -- n > 6638667628724569
        rcases Nat.lt_or_ge 6695206295563109 n with h8 | h8
        · -- n > 6695206295563109
          rcases Nat.lt_or_ge 6733156811289751 n with h10 | h10
          · -- n > 6733156811289751
            rcases Nat.lt_or_ge 6752220202535429 n with h12 | h12
            · -- n > 6752220202535429
              exact RamareSaouter2003.prime_interval_nat_ladder_c05275 n (by omega) (by omega)
            · -- n <= 6752220202535429
              exact RamareSaouter2003.prime_interval_nat_ladder_c05274 n (by omega) (by omega)
          · -- n <= 6733156811289751
            rcases Nat.lt_or_ge 6714148065771851 n with h12 | h12
            · -- n > 6714148065771851
              exact RamareSaouter2003.prime_interval_nat_ladder_c05273 n (by omega) (by omega)
            · -- n <= 6714148065771851
              exact RamareSaouter2003.prime_interval_nat_ladder_c05272 n (by omega) (by omega)
        · -- n <= 6695206295563109
          rcases Nat.lt_or_ge 6657461591536999 n with h10 | h10
          · -- n > 6657461591536999
            rcases Nat.lt_or_ge 6676307286206861 n with h12 | h12
            · -- n > 6676307286206861
              exact RamareSaouter2003.prime_interval_nat_ladder_c05271 n (by omega) (by omega)
            · -- n <= 6676307286206861
              exact RamareSaouter2003.prime_interval_nat_ladder_c05270 n (by omega) (by omega)
          · -- n <= 6657461591536999
            exact RamareSaouter2003.prime_interval_nat_ladder_c05269 n (by omega) (by omega)
      · -- n <= 6638667628724569
        rcases Nat.lt_or_ge 6582603661406951 n with h8 | h8
        · -- n > 6582603661406951
          rcases Nat.lt_or_ge 6601239995104199 n with h10 | h10
          · -- n > 6601239995104199
            rcases Nat.lt_or_ge 6619925941691177 n with h12 | h12
            · -- n > 6619925941691177
              exact RamareSaouter2003.prime_interval_nat_ladder_c05268 n (by omega) (by omega)
            · -- n <= 6619925941691177
              exact RamareSaouter2003.prime_interval_nat_ladder_c05267 n (by omega) (by omega)
          · -- n <= 6601239995104199
            exact RamareSaouter2003.prime_interval_nat_ladder_c05266 n (by omega) (by omega)
        · -- n <= 6582603661406951
          rcases Nat.lt_or_ge 6545488991371387 n with h10 | h10
          · -- n > 6545488991371387
            rcases Nat.lt_or_ge 6564020087902579 n with h12 | h12
            · -- n > 6564020087902579
              exact RamareSaouter2003.prime_interval_nat_ladder_c05265 n (by omega) (by omega)
            · -- n <= 6564020087902579
              exact RamareSaouter2003.prime_interval_nat_ladder_c05264 n (by omega) (by omega)
          · -- n <= 6545488991371387
            exact RamareSaouter2003.prime_interval_nat_ladder_c05263 n (by omega) (by omega)
    · -- n <= 6527009459080501
      rcases Nat.lt_or_ge 6417231177506867 n with h6 | h6
      · -- n > 6417231177506867
        rcases Nat.lt_or_ge 6471886402170829 n with h8 | h8
        · -- n > 6471886402170829
          rcases Nat.lt_or_ge 6490208521584209 n with h10 | h10
          · -- n > 6490208521584209
            rcases Nat.lt_or_ge 6508583963861699 n with h12 | h12
            · -- n > 6508583963861699
              exact RamareSaouter2003.prime_interval_nat_ladder_c05262 n (by omega) (by omega)
            · -- n <= 6508583963861699
              exact RamareSaouter2003.prime_interval_nat_ladder_c05261 n (by omega) (by omega)
          · -- n <= 6490208521584209
            exact RamareSaouter2003.prime_interval_nat_ladder_c05260 n (by omega) (by omega)
        · -- n <= 6471886402170829
          rcases Nat.lt_or_ge 6435399290592109 n with h10 | h10
          · -- n > 6435399290592109
            rcases Nat.lt_or_ge 6453617820719887 n with h12 | h12
            · -- n > 6453617820719887
              exact RamareSaouter2003.prime_interval_nat_ladder_c05259 n (by omega) (by omega)
            · -- n <= 6453617820719887
              exact RamareSaouter2003.prime_interval_nat_ladder_c05258 n (by omega) (by omega)
          · -- n <= 6435399290592109
            exact RamareSaouter2003.prime_interval_nat_ladder_c05257 n (by omega) (by omega)
      · -- n <= 6417231177506867
        rcases Nat.lt_or_ge 6363036011658269 n with h8 | h8
        · -- n > 6363036011658269
          rcases Nat.lt_or_ge 6381051247185997 n with h10 | h10
          · -- n > 6381051247185997
            rcases Nat.lt_or_ge 6399116429627567 n with h12 | h12
            · -- n > 6399116429627567
              exact RamareSaouter2003.prime_interval_nat_ladder_c05256 n (by omega) (by omega)
            · -- n <= 6399116429627567
              exact RamareSaouter2003.prime_interval_nat_ladder_c05255 n (by omega) (by omega)
          · -- n <= 6381051247185997
            exact RamareSaouter2003.prime_interval_nat_ladder_c05254 n (by omega) (by omega)
        · -- n <= 6363036011658269
          rcases Nat.lt_or_ge 6327160523598389 n with h10 | h10
          · -- n > 6327160523598389
            rcases Nat.lt_or_ge 6345071410667953 n with h12 | h12
            · -- n > 6345071410667953
              exact RamareSaouter2003.prime_interval_nat_ladder_c05253 n (by omega) (by omega)
            · -- n <= 6345071410667953
              exact RamareSaouter2003.prime_interval_nat_ladder_c05252 n (by omega) (by omega)
          · -- n <= 6327160523598389
            exact RamareSaouter2003.prime_interval_nat_ladder_c05251 n (by omega) (by omega)
