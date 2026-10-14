-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp136
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T01:34:27.947989+00:00
-- url     : https://prove2.me/submissions/c58eb0e9-6776-47cd-8f94-016470402056

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06766
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06767
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06768
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06769
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06770
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06771
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06772
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06773
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06774
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06775
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06776
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06777
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06778
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06779
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06780
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06781
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06782
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06783
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06784
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06785
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06786
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06787
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06788
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06789
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06790
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06791
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06792
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06793
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06794
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06795
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06796
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06797
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06798
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06799
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06800

theorem solution (n : Nat)
    (hn : 438210345612193751 < n) (hupper : n <= 504749525047989457) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 470304712968160199 n with h2 | h2
  · -- n > 470304712968160199
    rcases Nat.lt_or_ge 486534629435624621 n with h4 | h4
    · -- n > 486534629435624621
      rcases Nat.lt_or_ge 494858431815761327 n with h6 | h6
      · -- n > 494858431815761327
        rcases Nat.lt_or_ge 499073448055941769 n with h8 | h8
        · -- n > 499073448055941769
          rcases Nat.lt_or_ge 501903457021518427 n with h10 | h10
          · -- n > 501903457021518427
            rcases Nat.lt_or_ge 503324461481009239 n with h12 | h12
            · -- n > 503324461481009239
              exact RamareSaouter2003.prime_interval_nat_ladder_c06800 n (by omega) (by omega)
            · -- n <= 503324461481009239
              exact RamareSaouter2003.prime_interval_nat_ladder_c06799 n (by omega) (by omega)
          · -- n <= 501903457021518427
            rcases Nat.lt_or_ge 500486456307300877 n with h12 | h12
            · -- n > 500486456307300877
              exact RamareSaouter2003.prime_interval_nat_ladder_c06798 n (by omega) (by omega)
            · -- n <= 500486456307300877
              exact RamareSaouter2003.prime_interval_nat_ladder_c06797 n (by omega) (by omega)
        · -- n <= 499073448055941769
          rcases Nat.lt_or_ge 496259493671394781 n with h10 | h10
          · -- n > 496259493671394781
            rcases Nat.lt_or_ge 497664542442558787 n with h12 | h12
            · -- n > 497664542442558787
              exact RamareSaouter2003.prime_interval_nat_ladder_c06796 n (by omega) (by omega)
            · -- n <= 497664542442558787
              exact RamareSaouter2003.prime_interval_nat_ladder_c06795 n (by omega) (by omega)
          · -- n <= 496259493671394781
            exact RamareSaouter2003.prime_interval_nat_ladder_c06794 n (by omega) (by omega)
      · -- n <= 494858431815761327
        rcases Nat.lt_or_ge 490678872347699291 n with h8 | h8
        · -- n > 490678872347699291
          rcases Nat.lt_or_ge 492068121043580951 n with h10 | h10
          · -- n > 492068121043580951
            rcases Nat.lt_or_ge 493461297709027457 n with h12 | h12
            · -- n > 493461297709027457
              exact RamareSaouter2003.prime_interval_nat_ladder_c06793 n (by omega) (by omega)
            · -- n <= 493461297709027457
              exact RamareSaouter2003.prime_interval_nat_ladder_c06792 n (by omega) (by omega)
          · -- n <= 492068121043580951
            exact RamareSaouter2003.prime_interval_nat_ladder_c06791 n (by omega) (by omega)
        · -- n <= 490678872347699291
          rcases Nat.lt_or_ge 487912129985540189 n with h10 | h10
          · -- n > 487912129985540189
            rcases Nat.lt_or_ge 489293544790350731 n with h12 | h12
            · -- n > 489293544790350731
              exact RamareSaouter2003.prime_interval_nat_ladder_c06790 n (by omega) (by omega)
            · -- n <= 489293544790350731
              exact RamareSaouter2003.prime_interval_nat_ladder_c06789 n (by omega) (by omega)
          · -- n <= 487912129985540189
            exact RamareSaouter2003.prime_interval_nat_ladder_c06788 n (by omega) (by omega)
    · -- n <= 486534629435624621
      rcases Nat.lt_or_ge 478350849472311863 n with h6 | h6
      · -- n > 478350849472311863
        rcases Nat.lt_or_ge 482425363337295449 n with h8 | h8
        · -- n > 482425363337295449
          rcases Nat.lt_or_ge 483791254308158759 n with h10 | h10
          · -- n > 483791254308158759
            rcases Nat.lt_or_ge 485161009666059569 n with h12 | h12
            · -- n > 485161009666059569
              exact RamareSaouter2003.prime_interval_nat_ladder_c06787 n (by omega) (by omega)
            · -- n <= 485161009666059569
              exact RamareSaouter2003.prime_interval_nat_ladder_c06786 n (by omega) (by omega)
          · -- n <= 483791254308158759
            exact RamareSaouter2003.prime_interval_nat_ladder_c06785 n (by omega) (by omega)
        · -- n <= 482425363337295449
          rcases Nat.lt_or_ge 479705205861394397 n with h10 | h10
          · -- n > 479705205861394397
            rcases Nat.lt_or_ge 481063357714801387 n with h12 | h12
            · -- n > 481063357714801387
              exact RamareSaouter2003.prime_interval_nat_ladder_c06784 n (by omega) (by omega)
            · -- n <= 481063357714801387
              exact RamareSaouter2003.prime_interval_nat_ladder_c06783 n (by omega) (by omega)
          · -- n <= 479705205861394397
            exact RamareSaouter2003.prime_interval_nat_ladder_c06782 n (by omega) (by omega)
      · -- n <= 478350849472311863
        rcases Nat.lt_or_ge 474310730574080683 n with h8 | h8
        · -- n > 474310730574080683
          rcases Nat.lt_or_ge 475653647518047517 n with h10 | h10
          · -- n > 475653647518047517
            rcases Nat.lt_or_ge 477000330467961763 n with h12 | h12
            · -- n > 477000330467961763
              exact RamareSaouter2003.prime_interval_nat_ladder_c06781 n (by omega) (by omega)
            · -- n <= 477000330467961763
              exact RamareSaouter2003.prime_interval_nat_ladder_c06780 n (by omega) (by omega)
          · -- n <= 475653647518047517
            exact RamareSaouter2003.prime_interval_nat_ladder_c06779 n (by omega) (by omega)
        · -- n <= 474310730574080683
          rcases Nat.lt_or_ge 471636283732409017 n with h10 | h10
          · -- n > 471636283732409017
            rcases Nat.lt_or_ge 472971603228447889 n with h12 | h12
            · -- n > 472971603228447889
              exact RamareSaouter2003.prime_interval_nat_ladder_c06778 n (by omega) (by omega)
            · -- n <= 472971603228447889
              exact RamareSaouter2003.prime_interval_nat_ladder_c06777 n (by omega) (by omega)
          · -- n <= 471636283732409017
            exact RamareSaouter2003.prime_interval_nat_ladder_c06776 n (by omega) (by omega)
  · -- n <= 470304712968160199
    rcases Nat.lt_or_ge 453332697891017573 n with h4 | h4
    · -- n > 453332697891017573
      rcases Nat.lt_or_ge 461088465622220063 n with h6 | h6
      · -- n > 461088465622220063
        rcases Nat.lt_or_ge 465015975210484567 n with h8 | h8
        · -- n > 465015975210484567
          rcases Nat.lt_or_ge 467652860470527049 n with h10 | h10
          · -- n > 467652860470527049
            rcases Nat.lt_or_ge 468976912059197111 n with h12 | h12
            · -- n > 468976912059197111
              exact RamareSaouter2003.prime_interval_nat_ladder_c06775 n (by omega) (by omega)
            · -- n <= 468976912059197111
              exact RamareSaouter2003.prime_interval_nat_ladder_c06774 n (by omega) (by omega)
          · -- n <= 467652860470527049
            rcases Nat.lt_or_ge 466332566720647687 n with h12 | h12
            · -- n > 466332566720647687
              exact RamareSaouter2003.prime_interval_nat_ladder_c06773 n (by omega) (by omega)
            · -- n <= 466332566720647687
              exact RamareSaouter2003.prime_interval_nat_ladder_c06772 n (by omega) (by omega)
        · -- n <= 465015975210484567
          rcases Nat.lt_or_ge 462393944724790877 n with h10 | h10
          · -- n > 462393944724790877
            rcases Nat.lt_or_ge 463703094258969343 n with h12 | h12
            · -- n > 463703094258969343
              exact RamareSaouter2003.prime_interval_nat_ladder_c06771 n (by omega) (by omega)
            · -- n <= 463703094258969343
              exact RamareSaouter2003.prime_interval_nat_ladder_c06770 n (by omega) (by omega)
          · -- n <= 462393944724790877
            exact RamareSaouter2003.prime_interval_nat_ladder_c06769 n (by omega) (by omega)
      · -- n <= 461088465622220063
        rcases Nat.lt_or_ge 457194138853678399 n with h8 | h8
        · -- n > 457194138853678399
          rcases Nat.lt_or_ge 458488561011800603 n with h10 | h10
          · -- n > 458488561011800603
            rcases Nat.lt_or_ge 459786669581952989 n with h12 | h12
            · -- n > 459786669581952989
              exact RamareSaouter2003.prime_interval_nat_ladder_c06768 n (by omega) (by omega)
            · -- n <= 459786669581952989
              exact RamareSaouter2003.prime_interval_nat_ladder_c06767 n (by omega) (by omega)
          · -- n <= 458488561011800603
            exact RamareSaouter2003.prime_interval_nat_ladder_c06766 n (by omega) (by omega)
        · -- n <= 457194138853678399
          rcases Nat.lt_or_ge 454616198153284619 n with h10 | h10
          · -- n > 454616198153284619
            rcases Nat.lt_or_ge 455903342524555297 n with h12 | h12
            · -- n > 455903342524555297
              exact RamareSaouter2003.prime_interval_nat_ladder_c06765 n (by omega) (by omega)
            · -- n <= 455903342524555297
              exact RamareSaouter2003.prime_interval_nat_ladder_c06764 n (by omega) (by omega)
          · -- n <= 454616198153284619
            exact RamareSaouter2003.prime_interval_nat_ladder_c06763 n (by omega) (by omega)
    · -- n <= 453332697891017573
      rcases Nat.lt_or_ge 445707391599062893 n with h6 | h6
      · -- n > 445707391599062893
        rcases Nat.lt_or_ge 449503857877253827 n with h8 | h8
        · -- n > 449503857877253827
          rcases Nat.lt_or_ge 450776530745112601 n with h10 | h10
          · -- n > 450776530745112601
            rcases Nat.lt_or_ge 452052816792460489 n with h12 | h12
            · -- n > 452052816792460489
              exact RamareSaouter2003.prime_interval_nat_ladder_c06762 n (by omega) (by omega)
            · -- n <= 452052816792460489
              exact RamareSaouter2003.prime_interval_nat_ladder_c06761 n (by omega) (by omega)
          · -- n <= 450776530745112601
            exact RamareSaouter2003.prime_interval_nat_ladder_c06760 n (by omega) (by omega)
        · -- n <= 449503857877253827
          rcases Nat.lt_or_ge 446969288580411347 n with h10 | h10
          · -- n > 446969288580411347
            rcases Nat.lt_or_ge 448234791747076889 n with h12 | h12
            · -- n > 448234791747076889
              exact RamareSaouter2003.prime_interval_nat_ladder_c06759 n (by omega) (by omega)
            · -- n <= 448234791747076889
              exact RamareSaouter2003.prime_interval_nat_ladder_c06758 n (by omega) (by omega)
          · -- n <= 446969288580411347
            exact RamareSaouter2003.prime_interval_nat_ladder_c06757 n (by omega) (by omega)
      · -- n <= 445707391599062893
        rcases Nat.lt_or_ge 441942951290012527 n with h8 | h8
        · -- n > 441942951290012527
          rcases Nat.lt_or_ge 443194212477917861 n with h10 | h10
          · -- n > 443194212477917861
            rcases Nat.lt_or_ge 444449021202680297 n with h12 | h12
            · -- n > 444449021202680297
              exact RamareSaouter2003.prime_interval_nat_ladder_c06756 n (by omega) (by omega)
            · -- n <= 444449021202680297
              exact RamareSaouter2003.prime_interval_nat_ladder_c06755 n (by omega) (by omega)
          · -- n <= 443194212477917861
            exact RamareSaouter2003.prime_interval_nat_ladder_c06754 n (by omega) (by omega)
        · -- n <= 441942951290012527
          rcases Nat.lt_or_ge 439451021295422791 n with h10 | h10
          · -- n > 439451021295422791
            rcases Nat.lt_or_ge 440695222036574137 n with h12 | h12
            · -- n > 440695222036574137
              exact RamareSaouter2003.prime_interval_nat_ladder_c06753 n (by omega) (by omega)
            · -- n <= 440695222036574137
              exact RamareSaouter2003.prime_interval_nat_ladder_c06752 n (by omega) (by omega)
          · -- n <= 439451021295422791
            exact RamareSaouter2003.prime_interval_nat_ladder_c06751 n (by omega) (by omega)
