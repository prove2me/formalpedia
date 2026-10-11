-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp012
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T20:55:42.164975+00:00
-- url     : https://prove2.me/submissions/729f321e-090a-4dce-a316-579273855621

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00570
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00590
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00600

theorem solution (n : Nat)
    (hn : 36137549639 < n) (hupper : n <= 40472556721) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 38242283221 n with h2 | h2
  · -- n > 38242283221
    rcases Nat.lt_or_ge 39296686267 n with h4 | h4
    · -- n > 39296686267
      rcases Nat.lt_or_ge 39834991639 n with h6 | h6
      · -- n > 39834991639
        rcases Nat.lt_or_ge 40106966359 n with h8 | h8
        · -- n > 40106966359
          rcases Nat.lt_or_ge 40289337433 n with h10 | h10
          · -- n > 40289337433
            rcases Nat.lt_or_ge 40380840793 n with h12 | h12
            · -- n > 40380840793
              exact RamareSaouter2003.prime_interval_nat_ladder_c00600 n (by omega) (by omega)
            · -- n <= 40380840793
              exact RamareSaouter2003.prime_interval_nat_ladder_c00599 n (by omega) (by omega)
          · -- n <= 40289337433
            rcases Nat.lt_or_ge 40198046113 n with h12 | h12
            · -- n > 40198046113
              exact RamareSaouter2003.prime_interval_nat_ladder_c00598 n (by omega) (by omega)
            · -- n <= 40198046113
              exact RamareSaouter2003.prime_interval_nat_ladder_c00597 n (by omega) (by omega)
        · -- n <= 40106966359
          rcases Nat.lt_or_ge 39925439717 n with h10 | h10
          · -- n > 39925439717
            rcases Nat.lt_or_ge 40016097761 n with h12 | h12
            · -- n > 40016097761
              exact RamareSaouter2003.prime_interval_nat_ladder_c00596 n (by omega) (by omega)
            · -- n <= 40016097761
              exact RamareSaouter2003.prime_interval_nat_ladder_c00595 n (by omega) (by omega)
          · -- n <= 39925439717
            exact RamareSaouter2003.prime_interval_nat_ladder_c00594 n (by omega) (by omega)
      · -- n <= 39834991639
        rcases Nat.lt_or_ge 39564902653 n with h8 | h8
        · -- n > 39564902653
          rcases Nat.lt_or_ge 39654723601 n with h10 | h10
          · -- n > 39654723601
            rcases Nat.lt_or_ge 39744753077 n with h12 | h12
            · -- n > 39744753077
              exact RamareSaouter2003.prime_interval_nat_ladder_c00593 n (by omega) (by omega)
            · -- n <= 39744753077
              exact RamareSaouter2003.prime_interval_nat_ladder_c00592 n (by omega) (by omega)
          · -- n <= 39654723601
            exact RamareSaouter2003.prime_interval_nat_ladder_c00591 n (by omega) (by omega)
        · -- n <= 39564902653
          rcases Nat.lt_or_ge 39385884451 n with h10 | h10
          · -- n > 39385884451
            rcases Nat.lt_or_ge 39475289759 n with h12 | h12
            · -- n > 39475289759
              exact RamareSaouter2003.prime_interval_nat_ladder_c00590 n (by omega) (by omega)
            · -- n <= 39475289759
              exact RamareSaouter2003.prime_interval_nat_ladder_c00589 n (by omega) (by omega)
          · -- n <= 39385884451
            exact RamareSaouter2003.prime_interval_nat_ladder_c00588 n (by omega) (by omega)
    · -- n <= 39296686267
      rcases Nat.lt_or_ge 38765818561 n with h6 | h6
      · -- n > 38765818561
        rcases Nat.lt_or_ge 39030329363 n with h8 | h8
        · -- n > 39030329363
          rcases Nat.lt_or_ge 39118909153 n with h10 | h10
          · -- n > 39118909153
            rcases Nat.lt_or_ge 39207694639 n with h12 | h12
            · -- n > 39207694639
              exact RamareSaouter2003.prime_interval_nat_ladder_c00587 n (by omega) (by omega)
            · -- n <= 39207694639
              exact RamareSaouter2003.prime_interval_nat_ladder_c00586 n (by omega) (by omega)
          · -- n <= 39118909153
            exact RamareSaouter2003.prime_interval_nat_ladder_c00585 n (by omega) (by omega)
        · -- n <= 39030329363
          rcases Nat.lt_or_ge 38853784547 n with h10 | h10
          · -- n > 38853784547
            rcases Nat.lt_or_ge 38941954687 n with h12 | h12
            · -- n > 38941954687
              exact RamareSaouter2003.prime_interval_nat_ladder_c00584 n (by omega) (by omega)
            · -- n <= 38941954687
              exact RamareSaouter2003.prime_interval_nat_ladder_c00583 n (by omega) (by omega)
          · -- n <= 38853784547
            exact RamareSaouter2003.prime_interval_nat_ladder_c00582 n (by omega) (by omega)
      · -- n <= 38765818561
        rcases Nat.lt_or_ge 38503140787 n with h8 | h8
        · -- n > 38503140787
          rcases Nat.lt_or_ge 38590497191 n with h10 | h10
          · -- n > 38590497191
            rcases Nat.lt_or_ge 38678056303 n with h12 | h12
            · -- n > 38678056303
              exact RamareSaouter2003.prime_interval_nat_ladder_c00581 n (by omega) (by omega)
            · -- n <= 38678056303
              exact RamareSaouter2003.prime_interval_nat_ladder_c00580 n (by omega) (by omega)
          · -- n <= 38590497191
            exact RamareSaouter2003.prime_interval_nat_ladder_c00579 n (by omega) (by omega)
        · -- n <= 38503140787
          rcases Nat.lt_or_ge 38329034329 n with h10 | h10
          · -- n > 38329034329
            rcases Nat.lt_or_ge 38415986617 n with h12 | h12
            · -- n > 38415986617
              exact RamareSaouter2003.prime_interval_nat_ladder_c00578 n (by omega) (by omega)
            · -- n <= 38415986617
              exact RamareSaouter2003.prime_interval_nat_ladder_c00577 n (by omega) (by omega)
          · -- n <= 38329034329
            exact RamareSaouter2003.prime_interval_nat_ladder_c00576 n (by omega) (by omega)
  · -- n <= 38242283221
    rcases Nat.lt_or_ge 37132620563 n with h4 | h4
    · -- n > 37132620563
      rcases Nat.lt_or_ge 37640621573 n with h6 | h6
      · -- n > 37640621573
        rcases Nat.lt_or_ge 37897282201 n with h8 | h8
        · -- n > 37897282201
          rcases Nat.lt_or_ge 38069382971 n with h10 | h10
          · -- n > 38069382971
            rcases Nat.lt_or_ge 38155732931 n with h12 | h12
            · -- n > 38155732931
              exact RamareSaouter2003.prime_interval_nat_ladder_c00575 n (by omega) (by omega)
            · -- n <= 38155732931
              exact RamareSaouter2003.prime_interval_nat_ladder_c00574 n (by omega) (by omega)
          · -- n <= 38069382971
            rcases Nat.lt_or_ge 37983232873 n with h12 | h12
            · -- n > 37983232873
              exact RamareSaouter2003.prime_interval_nat_ladder_c00573 n (by omega) (by omega)
            · -- n <= 37983232873
              exact RamareSaouter2003.prime_interval_nat_ladder_c00572 n (by omega) (by omega)
        · -- n <= 37897282201
          rcases Nat.lt_or_ge 37725976993 n with h10 | h10
          · -- n > 37725976993
            rcases Nat.lt_or_ge 37811530391 n with h12 | h12
            · -- n > 37811530391
              exact RamareSaouter2003.prime_interval_nat_ladder_c00571 n (by omega) (by omega)
            · -- n <= 37811530391
              exact RamareSaouter2003.prime_interval_nat_ladder_c00570 n (by omega) (by omega)
          · -- n <= 37725976993
            exact RamareSaouter2003.prime_interval_nat_ladder_c00569 n (by omega) (by omega)
      · -- n <= 37640621573
        rcases Nat.lt_or_ge 37385738449 n with h8 | h8
        · -- n > 37385738449
          rcases Nat.lt_or_ge 37470502759 n with h10 | h10
          · -- n > 37470502759
            rcases Nat.lt_or_ge 37555463651 n with h12 | h12
            · -- n > 37555463651
              exact RamareSaouter2003.prime_interval_nat_ladder_c00568 n (by omega) (by omega)
            · -- n <= 37555463651
              exact RamareSaouter2003.prime_interval_nat_ladder_c00567 n (by omega) (by omega)
          · -- n <= 37470502759
            exact RamareSaouter2003.prime_interval_nat_ladder_c00566 n (by omega) (by omega)
        · -- n <= 37385738449
          rcases Nat.lt_or_ge 37216797707 n with h10 | h10
          · -- n > 37216797707
            rcases Nat.lt_or_ge 37301170271 n with h12 | h12
            · -- n > 37301170271
              exact RamareSaouter2003.prime_interval_nat_ladder_c00565 n (by omega) (by omega)
            · -- n <= 37301170271
              exact RamareSaouter2003.prime_interval_nat_ladder_c00564 n (by omega) (by omega)
          · -- n <= 37216797707
            exact RamareSaouter2003.prime_interval_nat_ladder_c00563 n (by omega) (by omega)
    · -- n <= 37132620563
      rcases Nat.lt_or_ge 36631629637 n with h6 | h6
      · -- n > 36631629637
        rcases Nat.lt_or_ge 36881255161 n with h8 | h8
        · -- n > 36881255161
          rcases Nat.lt_or_ge 36964849699 n with h10 | h10
          · -- n > 36964849699
            rcases Nat.lt_or_ge 37048637957 n with h12 | h12
            · -- n > 37048637957
              exact RamareSaouter2003.prime_interval_nat_ladder_c00562 n (by omega) (by omega)
            · -- n <= 37048637957
              exact RamareSaouter2003.prime_interval_nat_ladder_c00561 n (by omega) (by omega)
          · -- n <= 36964849699
            exact RamareSaouter2003.prime_interval_nat_ladder_c00560 n (by omega) (by omega)
        · -- n <= 36881255161
          rcases Nat.lt_or_ge 36714645553 n with h10 | h10
          · -- n > 36714645553
            rcases Nat.lt_or_ge 36797853923 n with h12 | h12
            · -- n > 36797853923
              exact RamareSaouter2003.prime_interval_nat_ladder_c00559 n (by omega) (by omega)
            · -- n <= 36797853923
              exact RamareSaouter2003.prime_interval_nat_ladder_c00558 n (by omega) (by omega)
          · -- n <= 36714645553
            exact RamareSaouter2003.prime_interval_nat_ladder_c00557 n (by omega) (by omega)
      · -- n <= 36631629637
        rcases Nat.lt_or_ge 36383731861 n with h8 | h8
        · -- n > 36383731861
          rcases Nat.lt_or_ge 36466173223 n with h10 | h10
          · -- n > 36466173223
            rcases Nat.lt_or_ge 36548805659 n with h12 | h12
            · -- n > 36548805659
              exact RamareSaouter2003.prime_interval_nat_ladder_c00556 n (by omega) (by omega)
            · -- n <= 36548805659
              exact RamareSaouter2003.prime_interval_nat_ladder_c00555 n (by omega) (by omega)
          · -- n <= 36466173223
            exact RamareSaouter2003.prime_interval_nat_ladder_c00554 n (by omega) (by omega)
        · -- n <= 36383731861
          rcases Nat.lt_or_ge 36219420511 n with h10 | h10
          · -- n > 36219420511
            rcases Nat.lt_or_ge 36301481093 n with h12 | h12
            · -- n > 36301481093
              exact RamareSaouter2003.prime_interval_nat_ladder_c00553 n (by omega) (by omega)
            · -- n <= 36301481093
              exact RamareSaouter2003.prime_interval_nat_ladder_c00552 n (by omega) (by omega)
          · -- n <= 36219420511
            exact RamareSaouter2003.prime_interval_nat_ladder_c00551 n (by omega) (by omega)
