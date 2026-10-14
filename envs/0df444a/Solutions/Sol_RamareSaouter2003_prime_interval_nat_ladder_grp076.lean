-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp076
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T07:11:12.41911+00:00
-- url     : https://prove2.me/submissions/07b4998f-0dc8-4f58-9627-cab824ec3eaf

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03766
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03767
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03768
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03769
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03770
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03771
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03772
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03773
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03774
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03775
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03776
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03777
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03778
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03779
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03780
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03781
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03782
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03783
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03784
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03785
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03786
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03787
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03788
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03789
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03790
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03791
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03792
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03793
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03794
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03795
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03796
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03797
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03798
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03799
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03800

theorem solution (n : Nat)
    (hn : 96869306228069 < n) (hupper : n <= 109611978750817) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 103043856370751 n with h2 | h2
  · -- n > 103043856370751
    rcases Nat.lt_or_ge 106145929012367 n with h4 | h4
    · -- n > 106145929012367
      rcases Nat.lt_or_ge 107731811333309 n with h6 | h6
      · -- n > 107731811333309
        rcases Nat.lt_or_ge 108533615745587 n with h8 | h8
        · -- n > 108533615745587
          rcases Nat.lt_or_ge 109071464567257 n with h10 | h10
          · -- n > 109071464567257
            rcases Nat.lt_or_ge 109341387664811 n with h12 | h12
            · -- n > 109341387664811
              exact RamareSaouter2003.prime_interval_nat_ladder_c03800 n (by omega) (by omega)
            · -- n <= 109341387664811
              exact RamareSaouter2003.prime_interval_nat_ladder_c03799 n (by omega) (by omega)
          · -- n <= 109071464567257
            rcases Nat.lt_or_ge 108802207809167 n with h12 | h12
            · -- n > 108802207809167
              exact RamareSaouter2003.prime_interval_nat_ladder_c03798 n (by omega) (by omega)
            · -- n <= 108802207809167
              exact RamareSaouter2003.prime_interval_nat_ladder_c03797 n (by omega) (by omega)
        · -- n <= 108533615745587
          rcases Nat.lt_or_ge 107998419142391 n with h10 | h10
          · -- n > 107998419142391
            rcases Nat.lt_or_ge 108265686735601 n with h12 | h12
            · -- n > 108265686735601
              exact RamareSaouter2003.prime_interval_nat_ladder_c03796 n (by omega) (by omega)
            · -- n <= 108265686735601
              exact RamareSaouter2003.prime_interval_nat_ladder_c03795 n (by omega) (by omega)
          · -- n <= 107998419142391
            exact RamareSaouter2003.prime_interval_nat_ladder_c03794 n (by omega) (by omega)
      · -- n <= 107731811333309
        rcases Nat.lt_or_ge 106935930342251 n with h8 | h8
        · -- n > 106935930342251
          rcases Nat.lt_or_ge 107200568556019 n with h10 | h10
          · -- n > 107200568556019
            rcases Nat.lt_or_ge 107465861679331 n with h12 | h12
            · -- n > 107465861679331
              exact RamareSaouter2003.prime_interval_nat_ladder_c03793 n (by omega) (by omega)
            · -- n <= 107465861679331
              exact RamareSaouter2003.prime_interval_nat_ladder_c03792 n (by omega) (by omega)
          · -- n <= 107200568556019
            exact RamareSaouter2003.prime_interval_nat_ladder_c03791 n (by omega) (by omega)
        · -- n <= 106935930342251
          rcases Nat.lt_or_ge 106408612181197 n with h10 | h10
          · -- n > 106408612181197
            rcases Nat.lt_or_ge 106671945421507 n with h12 | h12
            · -- n > 106671945421507
              exact RamareSaouter2003.prime_interval_nat_ladder_c03790 n (by omega) (by omega)
            · -- n <= 106671945421507
              exact RamareSaouter2003.prime_interval_nat_ladder_c03789 n (by omega) (by omega)
          · -- n <= 106408612181197
            exact RamareSaouter2003.prime_interval_nat_ladder_c03788 n (by omega) (by omega)
    · -- n <= 106145929012367
      rcases Nat.lt_or_ge 104583391910611 n with h6 | h6
      · -- n > 104583391910611
        rcases Nat.lt_or_ge 105361763907229 n with h8 | h8
        · -- n > 105361763907229
          rcases Nat.lt_or_ge 105622506474257 n with h10 | h10
          · -- n > 105622506474257
            rcases Nat.lt_or_ge 105883894310459 n with h12 | h12
            · -- n > 105883894310459
              exact RamareSaouter2003.prime_interval_nat_ladder_c03787 n (by omega) (by omega)
            · -- n <= 105883894310459
              exact RamareSaouter2003.prime_interval_nat_ladder_c03786 n (by omega) (by omega)
          · -- n <= 105622506474257
            exact RamareSaouter2003.prime_interval_nat_ladder_c03785 n (by omega) (by omega)
        · -- n <= 105361763907229
          rcases Nat.lt_or_ge 104842208212471 n with h10 | h10
          · -- n > 104842208212471
            rcases Nat.lt_or_ge 105101665016207 n with h12 | h12
            · -- n > 105101665016207
              exact RamareSaouter2003.prime_interval_nat_ladder_c03784 n (by omega) (by omega)
            · -- n <= 105101665016207
              exact RamareSaouter2003.prime_interval_nat_ladder_c03783 n (by omega) (by omega)
          · -- n <= 104842208212471
            exact RamareSaouter2003.prime_interval_nat_ladder_c03782 n (by omega) (by omega)
      · -- n <= 104583391910611
        rcases Nat.lt_or_ge 103810770225521 n with h8 | h8
        · -- n > 103810770225521
          rcases Nat.lt_or_ge 104067674492527 n with h10 | h10
          · -- n > 104067674492527
            rcases Nat.lt_or_ge 104325214529797 n with h12 | h12
            · -- n > 104325214529797
              exact RamareSaouter2003.prime_interval_nat_ladder_c03781 n (by omega) (by omega)
            · -- n <= 104325214529797
              exact RamareSaouter2003.prime_interval_nat_ladder_c03780 n (by omega) (by omega)
          · -- n <= 104067674492527
            exact RamareSaouter2003.prime_interval_nat_ladder_c03779 n (by omega) (by omega)
        · -- n <= 103810770225521
          rcases Nat.lt_or_ge 103298862728291 n with h10 | h10
          · -- n > 103298862728291
            rcases Nat.lt_or_ge 103554500159309 n with h12 | h12
            · -- n > 103554500159309
              exact RamareSaouter2003.prime_interval_nat_ladder_c03778 n (by omega) (by omega)
            · -- n <= 103554500159309
              exact RamareSaouter2003.prime_interval_nat_ladder_c03777 n (by omega) (by omega)
          · -- n <= 103298862728291
            exact RamareSaouter2003.prime_interval_nat_ladder_c03776 n (by omega) (by omega)
  · -- n <= 103043856370751
    rcases Nat.lt_or_ge 99785497791277 n with h4 | h4
    · -- n > 99785497791277
      rcases Nat.lt_or_ge 101276351546197 n with h6 | h6
      · -- n > 101276351546197
        rcases Nat.lt_or_ge 102030110575199 n with h8 | h8
        · -- n > 102030110575199
          rcases Nat.lt_or_ge 102535730648497 n with h10 | h10
          · -- n > 102535730648497
            rcases Nat.lt_or_ge 102789479528971 n with h12 | h12
            · -- n > 102789479528971
              exact RamareSaouter2003.prime_interval_nat_ladder_c03775 n (by omega) (by omega)
            · -- n <= 102789479528971
              exact RamareSaouter2003.prime_interval_nat_ladder_c03774 n (by omega) (by omega)
          · -- n <= 102535730648497
            rcases Nat.lt_or_ge 102282608179369 n with h12 | h12
            · -- n > 102282608179369
              exact RamareSaouter2003.prime_interval_nat_ladder_c03773 n (by omega) (by omega)
            · -- n <= 102282608179369
              exact RamareSaouter2003.prime_interval_nat_ladder_c03772 n (by omega) (by omega)
        · -- n <= 102030110575199
          rcases Nat.lt_or_ge 101526983795623 n with h10 | h10
          · -- n > 101526983795623
            rcases Nat.lt_or_ge 101778236293403 n with h12 | h12
            · -- n > 101778236293403
              exact RamareSaouter2003.prime_interval_nat_ladder_c03771 n (by omega) (by omega)
            · -- n <= 101778236293403
              exact RamareSaouter2003.prime_interval_nat_ladder_c03770 n (by omega) (by omega)
          · -- n <= 101526983795623
            exact RamareSaouter2003.prime_interval_nat_ladder_c03769 n (by omega) (by omega)
      · -- n <= 101276351546197
        rcases Nat.lt_or_ge 100528160997401 n with h8 | h8
        · -- n > 100528160997401
          rcases Nat.lt_or_ge 100776941672549 n with h10 | h10
          · -- n > 100776941672549
            rcases Nat.lt_or_ge 101026338014311 n with h12 | h12
            · -- n > 101026338014311
              exact RamareSaouter2003.prime_interval_nat_ladder_c03768 n (by omega) (by omega)
            · -- n <= 101026338014311
              exact RamareSaouter2003.prime_interval_nat_ladder_c03767 n (by omega) (by omega)
          · -- n <= 100776941672549
            exact RamareSaouter2003.prime_interval_nat_ladder_c03766 n (by omega) (by omega)
        · -- n <= 100528160997401
          rcases Nat.lt_or_ge 100032440571023 n with h10 | h10
          · -- n > 100032440571023
            rcases Nat.lt_or_ge 100279994468987 n with h12 | h12
            · -- n > 100279994468987
              exact RamareSaouter2003.prime_interval_nat_ladder_c03765 n (by omega) (by omega)
            · -- n <= 100279994468987
              exact RamareSaouter2003.prime_interval_nat_ladder_c03764 n (by omega) (by omega)
          · -- n <= 100032440571023
            exact RamareSaouter2003.prime_interval_nat_ladder_c03763 n (by omega) (by omega)
    · -- n <= 99785497791277
      rcases Nat.lt_or_ge 98316590373427 n with h6 | h6
      · -- n > 98316590373427
        rcases Nat.lt_or_ge 99048321094033 n with h8 | h8
        · -- n > 99048321094033
          rcases Nat.lt_or_ge 99293439555899 n with h10 | h10
          · -- n > 99293439555899
            rcases Nat.lt_or_ge 99539164621321 n with h12 | h12
            · -- n > 99539164621321
              exact RamareSaouter2003.prime_interval_nat_ladder_c03762 n (by omega) (by omega)
            · -- n <= 99539164621321
              exact RamareSaouter2003.prime_interval_nat_ladder_c03761 n (by omega) (by omega)
          · -- n <= 99293439555899
            exact RamareSaouter2003.prime_interval_nat_ladder_c03760 n (by omega) (by omega)
        · -- n <= 99048321094033
          rcases Nat.lt_or_ge 98559897994801 n with h10 | h10
          · -- n > 98559897994801
            rcases Nat.lt_or_ge 98803807738343 n with h12 | h12
            · -- n > 98803807738343
              exact RamareSaouter2003.prime_interval_nat_ladder_c03759 n (by omega) (by omega)
            · -- n <= 98803807738343
              exact RamareSaouter2003.prime_interval_nat_ladder_c03758 n (by omega) (by omega)
          · -- n <= 98559897994801
            exact RamareSaouter2003.prime_interval_nat_ladder_c03757 n (by omega) (by omega)
      · -- n <= 98316590373427
        rcases Nat.lt_or_ge 97590265396639 n with h8 | h8
        · -- n > 97590265396639
          rcases Nat.lt_or_ge 97831775555329 n with h10 | h10
          · -- n > 97831775555329
            rcases Nat.lt_or_ge 98073883387873 n with h12 | h12
            · -- n > 98073883387873
              exact RamareSaouter2003.prime_interval_nat_ladder_c03756 n (by omega) (by omega)
            · -- n <= 98073883387873
              exact RamareSaouter2003.prime_interval_nat_ladder_c03755 n (by omega) (by omega)
          · -- n <= 97831775555329
            exact RamareSaouter2003.prime_interval_nat_ladder_c03754 n (by omega) (by omega)
        · -- n <= 97590265396639
          rcases Nat.lt_or_ge 97109032202893 n with h10 | h10
          · -- n > 97109032202893
            rcases Nat.lt_or_ge 97349351436443 n with h12 | h12
            · -- n > 97349351436443
              exact RamareSaouter2003.prime_interval_nat_ladder_c03753 n (by omega) (by omega)
            · -- n <= 97349351436443
              exact RamareSaouter2003.prime_interval_nat_ladder_c03752 n (by omega) (by omega)
          · -- n <= 97109032202893
            exact RamareSaouter2003.prime_interval_nat_ladder_c03751 n (by omega) (by omega)
