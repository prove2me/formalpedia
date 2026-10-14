-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp132
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T00:08:42.482977+00:00
-- url     : https://prove2.me/submissions/e0e45664-ef44-4f7c-9935-cc41c3bfd321

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06570
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06590
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06600

theorem solution (n : Nat)
    (hn : 248949425222306737 < n) (hupper : n <= 286750217619026779) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 267182183919043499 n with h2 | h2
  · -- n > 267182183919043499
    rcases Nat.lt_or_ge 276402330827677979 n with h4 | h4
    · -- n > 276402330827677979
      rcases Nat.lt_or_ge 281130967633057709 n with h6 | h6
      · -- n > 281130967633057709
        rcases Nat.lt_or_ge 283525613971630421 n with h8 | h8
        · -- n > 283525613971630421
          rcases Nat.lt_or_ge 285133363989083483 n with h10 | h10
          · -- n > 285133363989083483
            rcases Nat.lt_or_ge 285940637601732833 n with h12 | h12
            · -- n > 285940637601732833
              exact RamareSaouter2003.prime_interval_nat_ladder_c06600 n (by omega) (by omega)
            · -- n <= 285940637601732833
              exact RamareSaouter2003.prime_interval_nat_ladder_c06599 n (by omega) (by omega)
          · -- n <= 285133363989083483
            rcases Nat.lt_or_ge 284328354505602839 n with h12 | h12
            · -- n > 284328354505602839
              exact RamareSaouter2003.prime_interval_nat_ladder_c06598 n (by omega) (by omega)
            · -- n <= 284328354505602839
              exact RamareSaouter2003.prime_interval_nat_ladder_c06597 n (by omega) (by omega)
        · -- n <= 283525613971630421
          rcases Nat.lt_or_ge 281926929063038461 n with h10 | h10
          · -- n > 281926929063038461
            rcases Nat.lt_or_ge 282725142891354277 n with h12 | h12
            · -- n > 282725142891354277
              exact RamareSaouter2003.prime_interval_nat_ladder_c06596 n (by omega) (by omega)
            · -- n <= 282725142891354277
              exact RamareSaouter2003.prime_interval_nat_ladder_c06595 n (by omega) (by omega)
          · -- n <= 281926929063038461
            exact RamareSaouter2003.prime_interval_nat_ladder_c06594 n (by omega) (by omega)
      · -- n <= 281130967633057709
        rcases Nat.lt_or_ge 278756620212199357 n with h8 | h8
        · -- n > 278756620212199357
          rcases Nat.lt_or_ge 279545860384824217 n with h10 | h10
          · -- n > 279545860384824217
            rcases Nat.lt_or_ge 280337301626853017 n with h12 | h12
            · -- n > 280337301626853017
              exact RamareSaouter2003.prime_interval_nat_ladder_c06593 n (by omega) (by omega)
            · -- n <= 280337301626853017
              exact RamareSaouter2003.prime_interval_nat_ladder_c06592 n (by omega) (by omega)
          · -- n <= 279545860384824217
            exact RamareSaouter2003.prime_interval_nat_ladder_c06591 n (by omega) (by omega)
        · -- n <= 278756620212199357
          rcases Nat.lt_or_ge 277184895500835589 n with h10 | h10
          · -- n > 277184895500835589
            rcases Nat.lt_or_ge 277969656727198187 n with h12 | h12
            · -- n > 277969656727198187
              exact RamareSaouter2003.prime_interval_nat_ladder_c06590 n (by omega) (by omega)
            · -- n <= 277969656727198187
              exact RamareSaouter2003.prime_interval_nat_ladder_c06589 n (by omega) (by omega)
          · -- n <= 277184895500835589
            exact RamareSaouter2003.prime_interval_nat_ladder_c06588 n (by omega) (by omega)
    · -- n <= 276402330827677979
      rcases Nat.lt_or_ge 271753144015351217 n with h6 | h6
      · -- n > 271753144015351217
        rcases Nat.lt_or_ge 274067920779932107 n with h8 | h8
        · -- n > 274067920779932107
          rcases Nat.lt_or_ge 274843822979945399 n with h10 | h10
          · -- n > 274843822979945399
            rcases Nat.lt_or_ge 275621973797943533 n with h12 | h12
            · -- n > 275621973797943533
              exact RamareSaouter2003.prime_interval_nat_ladder_c06587 n (by omega) (by omega)
            · -- n <= 275621973797943533
              exact RamareSaouter2003.prime_interval_nat_ladder_c06586 n (by omega) (by omega)
          · -- n <= 274843822979945399
            exact RamareSaouter2003.prime_interval_nat_ladder_c06585 n (by omega) (by omega)
        · -- n <= 274067920779932107
          rcases Nat.lt_or_ge 272522556598987091 n with h10 | h10
          · -- n > 272522556598987091
            rcases Nat.lt_or_ge 273294142058659847 n with h12 | h12
            · -- n > 273294142058659847
              exact RamareSaouter2003.prime_interval_nat_ladder_c06584 n (by omega) (by omega)
            · -- n <= 273294142058659847
              exact RamareSaouter2003.prime_interval_nat_ladder_c06583 n (by omega) (by omega)
          · -- n <= 272522556598987091
            exact RamareSaouter2003.prime_interval_nat_ladder_c06582 n (by omega) (by omega)
      · -- n <= 271753144015351217
        rcases Nat.lt_or_ge 269457948212281639 n with h8 | h8
        · -- n > 269457948212281639
          rcases Nat.lt_or_ge 270220854903685337 n with h10 | h10
          · -- n > 270220854903685337
            rcases Nat.lt_or_ge 270985922815714087 n with h12 | h12
            · -- n > 270985922815714087
              exact RamareSaouter2003.prime_interval_nat_ladder_c06581 n (by omega) (by omega)
            · -- n <= 270985922815714087
              exact RamareSaouter2003.prime_interval_nat_ladder_c06580 n (by omega) (by omega)
          · -- n <= 270220854903685337
            exact RamareSaouter2003.prime_interval_nat_ladder_c06579 n (by omega) (by omega)
        · -- n <= 269457948212281639
          rcases Nat.lt_or_ge 267938658224437859 n with h10 | h10
          · -- n > 267938658224437859
            rcases Nat.lt_or_ge 268697213687901221 n with h12 | h12
            · -- n > 268697213687901221
              exact RamareSaouter2003.prime_interval_nat_ladder_c06578 n (by omega) (by omega)
            · -- n <= 268697213687901221
              exact RamareSaouter2003.prime_interval_nat_ladder_c06577 n (by omega) (by omega)
          · -- n <= 267938658224437859
            exact RamareSaouter2003.prime_interval_nat_ladder_c06576 n (by omega) (by omega)
  · -- n <= 267182183919043499
    rcases Nat.lt_or_ge 257540349369898337 n with h4 | h4
    · -- n > 257540349369898337
      rcases Nat.lt_or_ge 261946431432146369 n with h6 | h6
      · -- n > 261946431432146369
        rcases Nat.lt_or_ge 264177647732856593 n with h8 | h8
        · -- n > 264177647732856593
          rcases Nat.lt_or_ge 265675666027804871 n with h10 | h10
          · -- n > 265675666027804871
            rcases Nat.lt_or_ge 266427873308101331 n with h12 | h12
            · -- n > 266427873308101331
              exact RamareSaouter2003.prime_interval_nat_ladder_c06575 n (by omega) (by omega)
            · -- n <= 266427873308101331
              exact RamareSaouter2003.prime_interval_nat_ladder_c06574 n (by omega) (by omega)
          · -- n <= 265675666027804871
            rcases Nat.lt_or_ge 264925583420199827 n with h12 | h12
            · -- n > 264925583420199827
              exact RamareSaouter2003.prime_interval_nat_ladder_c06573 n (by omega) (by omega)
            · -- n <= 264925583420199827
              exact RamareSaouter2003.prime_interval_nat_ladder_c06572 n (by omega) (by omega)
        · -- n <= 264177647732856593
          rcases Nat.lt_or_ge 262688065396293217 n with h10 | h10
          · -- n > 262688065396293217
            rcases Nat.lt_or_ge 263431814332439161 n with h12 | h12
            · -- n > 263431814332439161
              exact RamareSaouter2003.prime_interval_nat_ladder_c06571 n (by omega) (by omega)
            · -- n <= 263431814332439161
              exact RamareSaouter2003.prime_interval_nat_ladder_c06570 n (by omega) (by omega)
          · -- n <= 262688065396293217
            exact RamareSaouter2003.prime_interval_nat_ladder_c06569 n (by omega) (by omega)
      · -- n <= 261946431432146369
        rcases Nat.lt_or_ge 259734036380638789 n with h8 | h8
        · -- n > 259734036380638789
          rcases Nat.lt_or_ge 260469413667902729 n with h10 | h10
          · -- n > 260469413667902729
            rcases Nat.lt_or_ge 261206878210406861 n with h12 | h12
            · -- n > 261206878210406861
              exact RamareSaouter2003.prime_interval_nat_ladder_c06568 n (by omega) (by omega)
            · -- n <= 261206878210406861
              exact RamareSaouter2003.prime_interval_nat_ladder_c06567 n (by omega) (by omega)
          · -- n <= 260469413667902729
            exact RamareSaouter2003.prime_interval_nat_ladder_c06566 n (by omega) (by omega)
        · -- n <= 259734036380638789
          rcases Nat.lt_or_ge 258269496390091253 n with h10 | h10
          · -- n > 258269496390091253
            rcases Nat.lt_or_ge 259000735810820537 n with h12 | h12
            · -- n > 259000735810820537
              exact RamareSaouter2003.prime_interval_nat_ladder_c06565 n (by omega) (by omega)
            · -- n <= 259000735810820537
              exact RamareSaouter2003.prime_interval_nat_ladder_c06564 n (by omega) (by omega)
          · -- n <= 258269496390091253
            exact RamareSaouter2003.prime_interval_nat_ladder_c06563 n (by omega) (by omega)
    · -- n <= 257540349369898337
      rcases Nat.lt_or_ge 253208464354757447 n with h6 | h6
      · -- n > 253208464354757447
        rcases Nat.lt_or_ge 255365241386645681 n with h8 | h8
        · -- n > 255365241386645681
          rcases Nat.lt_or_ge 256088252517850783 n with h10 | h10
          · -- n > 256088252517850783
            rcases Nat.lt_or_ge 256813259714555801 n with h12 | h12
            · -- n > 256813259714555801
              exact RamareSaouter2003.prime_interval_nat_ladder_c06562 n (by omega) (by omega)
            · -- n <= 256813259714555801
              exact RamareSaouter2003.prime_interval_nat_ladder_c06561 n (by omega) (by omega)
          · -- n <= 256088252517850783
            exact RamareSaouter2003.prime_interval_nat_ladder_c06560 n (by omega) (by omega)
        · -- n <= 255365241386645681
          rcases Nat.lt_or_ge 253925373327315887 n with h10 | h10
          · -- n > 253925373327315887
            rcases Nat.lt_or_ge 254644267624728391 n with h12 | h12
            · -- n > 254644267624728391
              exact RamareSaouter2003.prime_interval_nat_ladder_c06559 n (by omega) (by omega)
            · -- n <= 254644267624728391
              exact RamareSaouter2003.prime_interval_nat_ladder_c06558 n (by omega) (by omega)
          · -- n <= 253925373327315887
            exact RamareSaouter2003.prime_interval_nat_ladder_c06557 n (by omega) (by omega)
      · -- n <= 253208464354757447
        rcases Nat.lt_or_ge 251069906164634153 n with h8 | h8
        · -- n > 251069906164634153
          rcases Nat.lt_or_ge 251780738583830873 n with h10 | h10
          · -- n > 251780738583830873
            rcases Nat.lt_or_ge 252493584884170009 n with h12 | h12
            · -- n > 252493584884170009
              exact RamareSaouter2003.prime_interval_nat_ladder_c06556 n (by omega) (by omega)
            · -- n <= 252493584884170009
              exact RamareSaouter2003.prime_interval_nat_ladder_c06555 n (by omega) (by omega)
          · -- n <= 251780738583830873
            exact RamareSaouter2003.prime_interval_nat_ladder_c06554 n (by omega) (by omega)
        · -- n <= 251069906164634153
          rcases Nat.lt_or_ge 249654236715007459 n with h10 | h10
          · -- n > 249654236715007459
            rcases Nat.lt_or_ge 250361062268769719 n with h12 | h12
            · -- n > 250361062268769719
              exact RamareSaouter2003.prime_interval_nat_ladder_c06553 n (by omega) (by omega)
            · -- n <= 250361062268769719
              exact RamareSaouter2003.prime_interval_nat_ladder_c06552 n (by omega) (by omega)
          · -- n <= 249654236715007459
            exact RamareSaouter2003.prime_interval_nat_ladder_c06551 n (by omega) (by omega)
