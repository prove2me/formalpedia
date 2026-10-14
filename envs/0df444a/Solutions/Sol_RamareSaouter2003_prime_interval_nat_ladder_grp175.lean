-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp175
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T16:52:18.456987+00:00
-- url     : https://prove2.me/submissions/e98da036-9c9d-46ae-ac23-539ab399f880

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08688
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08700
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08717

theorem solution (n : Nat)
    (hn : 78908309765868443269 < n) (hupper : n <= 88937429173397375471) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 83670704066800660669 n with h2 | h2
  · -- n > 83670704066800660669
    rcases Nat.lt_or_ge 86158627674850747451 n with h4 | h4
    · -- n > 86158627674850747451
      rcases Nat.lt_or_ge 87430194860725025483 n with h6 | h6
      · -- n > 87430194860725025483
        rcases Nat.lt_or_ge 88072999013415786049 n with h8 | h8
        · -- n > 88072999013415786049
          rcases Nat.lt_or_ge 88504158714198478373 n with h10 | h10
          · -- n > 88504158714198478373
            rcases Nat.lt_or_ge 88720529557906519267 n with h12 | h12
            · -- n > 88720529557906519267
              exact RamareSaouter2003.prime_interval_nat_ladder_c08717 n (by omega) (by omega)
            · -- n <= 88720529557906519267
              exact RamareSaouter2003.prime_interval_nat_ladder_c08716 n (by omega) (by omega)
          · -- n <= 88504158714198478373
            rcases Nat.lt_or_ge 88288315784157557389 n with h12 | h12
            · -- n > 88288315784157557389
              exact RamareSaouter2003.prime_interval_nat_ladder_c08715 n (by omega) (by omega)
            · -- n <= 88288315784157557389
              exact RamareSaouter2003.prime_interval_nat_ladder_c08714 n (by omega) (by omega)
        · -- n <= 88072999013415786049
          rcases Nat.lt_or_ge 87643940119935692777 n with h10 | h10
          · -- n > 87643940119935692777
            rcases Nat.lt_or_ge 87858207627058529909 n with h12 | h12
            · -- n > 87858207627058529909
              exact RamareSaouter2003.prime_interval_nat_ladder_c08713 n (by omega) (by omega)
            · -- n <= 87858207627058529909
              exact RamareSaouter2003.prime_interval_nat_ladder_c08712 n (by omega) (by omega)
          · -- n <= 87643940119935692777
            exact RamareSaouter2003.prime_interval_nat_ladder_c08711 n (by omega) (by omega)
      · -- n <= 87430194860725025483
        rcases Nat.lt_or_ge 86792083412090892469 n with h8 | h8
        · -- n > 86792083412090892469
          rcases Nat.lt_or_ge 87004268365290821161 n with h10 | h10
          · -- n > 87004268365290821161
            rcases Nat.lt_or_ge 87216972238513064869 n with h12 | h12
            · -- n > 87216972238513064869
              exact RamareSaouter2003.prime_interval_nat_ladder_c08710 n (by omega) (by omega)
            · -- n <= 87216972238513064869
              exact RamareSaouter2003.prime_interval_nat_ladder_c08709 n (by omega) (by omega)
          · -- n <= 87004268365290821161
            exact RamareSaouter2003.prime_interval_nat_ladder_c08708 n (by omega) (by omega)
        · -- n <= 86792083412090892469
          rcases Nat.lt_or_ge 86369264289123833431 n with h10 | h10
          · -- n > 86369264289123833431
            rcases Nat.lt_or_ge 86580415740394765823 n with h12 | h12
            · -- n > 86580415740394765823
              exact RamareSaouter2003.prime_interval_nat_ladder_c08707 n (by omega) (by omega)
            · -- n <= 86580415740394765823
              exact RamareSaouter2003.prime_interval_nat_ladder_c08706 n (by omega) (by omega)
          · -- n <= 86369264289123833431
            exact RamareSaouter2003.prime_interval_nat_ladder_c08705 n (by omega) (by omega)
    · -- n <= 86158627674850747451
      rcases Nat.lt_or_ge 84905554691841011633 n with h6 | h6
      · -- n > 84905554691841011633
        rcases Nat.lt_or_ge 85529797449360032009 n with h8 | h8
        · -- n > 85529797449360032009
          rcases Nat.lt_or_ge 85738896249511059979 n with h10 | h10
          · -- n > 85738896249511059979
            rcases Nat.lt_or_ge 85948505952129944491 n with h12 | h12
            · -- n > 85948505952129944491
              exact RamareSaouter2003.prime_interval_nat_ladder_c08704 n (by omega) (by omega)
            · -- n <= 85948505952129944491
              exact RamareSaouter2003.prime_interval_nat_ladder_c08703 n (by omega) (by omega)
          · -- n <= 85738896249511059979
            exact RamareSaouter2003.prime_interval_nat_ladder_c08702 n (by omega) (by omega)
        · -- n <= 85529797449360032009
          rcases Nat.lt_or_ge 85113127759192232303 n with h10 | h10
          · -- n > 85113127759192232303
            rcases Nat.lt_or_ge 85321208132972000701 n with h12 | h12
            · -- n > 85321208132972000701
              exact RamareSaouter2003.prime_interval_nat_ladder_c08701 n (by omega) (by omega)
            · -- n <= 85321208132972000701
              exact RamareSaouter2003.prime_interval_nat_ladder_c08700 n (by omega) (by omega)
          · -- n <= 85113127759192232303
            exact RamareSaouter2003.prime_interval_nat_ladder_c08699 n (by omega) (by omega)
      · -- n <= 84905554691841011633
        rcases Nat.lt_or_ge 84285867928496568779 n with h8 | h8
        · -- n > 84285867928496568779
          rcases Nat.lt_or_ge 84491925988347657271 n with h10 | h10
          · -- n > 84491925988347657271
            rcases Nat.lt_or_ge 84698487880665901661 n with h12 | h12
            · -- n > 84698487880665901661
              exact RamareSaouter2003.prime_interval_nat_ladder_c08698 n (by omega) (by omega)
            · -- n <= 84698487880665901661
              exact RamareSaouter2003.prime_interval_nat_ladder_c08697 n (by omega) (by omega)
          · -- n <= 84491925988347657271
            exact RamareSaouter2003.prime_interval_nat_ladder_c08696 n (by omega) (by omega)
        · -- n <= 84285867928496568779
          rcases Nat.lt_or_ge 83875258042194195113 n with h10 | h10
          · -- n > 83875258042194195113
            rcases Nat.lt_or_ge 84080312357477489003 n with h12 | h12
            · -- n > 84080312357477489003
              exact RamareSaouter2003.prime_interval_nat_ladder_c08695 n (by omega) (by omega)
            · -- n <= 84080312357477489003
              exact RamareSaouter2003.prime_interval_nat_ladder_c08694 n (by omega) (by omega)
          · -- n <= 83875258042194195113
            exact RamareSaouter2003.prime_interval_nat_ladder_c08693 n (by omega) (by omega)
  · -- n <= 83670704066800660669
    rcases Nat.lt_or_ge 81254622564983973779 n with h4 | h4
    · -- n > 81254622564983973779
      rcases Nat.lt_or_ge 82453813977716692417 n with h6 | h6
      · -- n > 82453813977716692417
        rcases Nat.lt_or_ge 83060030537390409101 n with h8 | h8
        · -- n > 83060030537390409101
          rcases Nat.lt_or_ge 83263091608476578657 n with h10 | h10
          · -- n > 83263091608476578657
            rcases Nat.lt_or_ge 83466648856214588387 n with h12 | h12
            · -- n > 83466648856214588387
              exact RamareSaouter2003.prime_interval_nat_ladder_c08692 n (by omega) (by omega)
            · -- n <= 83466648856214588387
              exact RamareSaouter2003.prime_interval_nat_ladder_c08691 n (by omega) (by omega)
          · -- n <= 83263091608476578657
            exact RamareSaouter2003.prime_interval_nat_ladder_c08690 n (by omega) (by omega)
        · -- n <= 83060030537390409101
          rcases Nat.lt_or_ge 82655392908847600763 n with h10 | h10
          · -- n > 82655392908847600763
            rcases Nat.lt_or_ge 82857464460121135999 n with h12 | h12
            · -- n > 82857464460121135999
              exact RamareSaouter2003.prime_interval_nat_ladder_c08689 n (by omega) (by omega)
            · -- n <= 82857464460121135999
              exact RamareSaouter2003.prime_interval_nat_ladder_c08688 n (by omega) (by omega)
          · -- n <= 82655392908847600763
            exact RamareSaouter2003.prime_interval_nat_ladder_c08687 n (by omega) (by omega)
      · -- n <= 82453813977716692417
        rcases Nat.lt_or_ge 81852022820094101321 n with h8 | h8
        · -- n > 81852022820094101321
          rcases Nat.lt_or_ge 82052130574841476453 n with h10 | h10
          · -- n > 82052130574841476453
            rcases Nat.lt_or_ge 82252727802038194763 n with h12 | h12
            · -- n > 82252727802038194763
              exact RamareSaouter2003.prime_interval_nat_ladder_c08686 n (by omega) (by omega)
            · -- n <= 82252727802038194763
              exact RamareSaouter2003.prime_interval_nat_ladder_c08685 n (by omega) (by omega)
          · -- n <= 82052130574841476453
            exact RamareSaouter2003.prime_interval_nat_ladder_c08684 n (by omega) (by omega)
        · -- n <= 81852022820094101321
          rcases Nat.lt_or_ge 81453269968445892053 n with h10 | h10
          · -- n > 81453269968445892053
            rcases Nat.lt_or_ge 81652402932664810333 n with h12 | h12
            · -- n > 81652402932664810333
              exact RamareSaouter2003.prime_interval_nat_ladder_c08683 n (by omega) (by omega)
            · -- n <= 81652402932664810333
              exact RamareSaouter2003.prime_interval_nat_ladder_c08682 n (by omega) (by omega)
          · -- n <= 81453269968445892053
            exact RamareSaouter2003.prime_interval_nat_ladder_c08681 n (by omega) (by omega)
    · -- n <= 81254622564983973779
      rcases Nat.lt_or_ge 80072873675774635267 n with h6 | h6
      · -- n > 80072873675774635267
        rcases Nat.lt_or_ge 80661584042606879537 n with h8 | h8
        · -- n > 80661584042606879537
          rcases Nat.lt_or_ge 80858781126132523357 n with h10 | h10
          · -- n > 80858781126132523357
            rcases Nat.lt_or_ge 81056460430200862837 n with h12 | h12
            · -- n > 81056460430200862837
              exact RamareSaouter2003.prime_interval_nat_ladder_c08680 n (by omega) (by omega)
            · -- n <= 81056460430200862837
              exact RamareSaouter2003.prime_interval_nat_ladder_c08679 n (by omega) (by omega)
          · -- n <= 80858781126132523357
            exact RamareSaouter2003.prime_interval_nat_ladder_c08678 n (by omega) (by omega)
        · -- n <= 80661584042606879537
          rcases Nat.lt_or_ge 80268631814242232087 n with h10 | h10
          · -- n > 80268631814242232087
            rcases Nat.lt_or_ge 80464867574824996199 n with h12 | h12
            · -- n > 80464867574824996199
              exact RamareSaouter2003.prime_interval_nat_ladder_c08677 n (by omega) (by omega)
            · -- n <= 80464867574824996199
              exact RamareSaouter2003.prime_interval_nat_ladder_c08676 n (by omega) (by omega)
          · -- n <= 80268631814242232087
            exact RamareSaouter2003.prime_interval_nat_ladder_c08675 n (by omega) (by omega)
      · -- n <= 80072873675774635267
        rcases Nat.lt_or_ge 79488459012643321807 n with h8 | h8
        · -- n > 79488459012643321807
          rcases Nat.lt_or_ge 79682788048847759861 n with h10 | h10
          · -- n > 79682788048847759861
            rcases Nat.lt_or_ge 79877592824769741137 n with h12 | h12
            · -- n > 79877592824769741137
              exact RamareSaouter2003.prime_interval_nat_ladder_c08674 n (by omega) (by omega)
            · -- n <= 79877592824769741137
              exact RamareSaouter2003.prime_interval_nat_ladder_c08673 n (by omega) (by omega)
          · -- n <= 79682788048847759861
            exact RamareSaouter2003.prime_interval_nat_ladder_c08672 n (by omega) (by omega)
        · -- n <= 79488459012643321807
          rcases Nat.lt_or_ge 79101220505216809213 n with h10 | h10
          · -- n > 79101220505216809213
            rcases Nat.lt_or_ge 79294603416776721221 n with h12 | h12
            · -- n > 79294603416776721221
              exact RamareSaouter2003.prime_interval_nat_ladder_c08671 n (by omega) (by omega)
            · -- n <= 79294603416776721221
              exact RamareSaouter2003.prime_interval_nat_ladder_c08670 n (by omega) (by omega)
          · -- n <= 79101220505216809213
            exact RamareSaouter2003.prime_interval_nat_ladder_c08669 n (by omega) (by omega)
