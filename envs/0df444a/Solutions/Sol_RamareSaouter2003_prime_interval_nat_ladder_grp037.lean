-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp037
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T12:04:26.17898+00:00
-- url     : https://prove2.me/submissions/6c4dcd8c-c8db-4ee1-bb85-804b67e003f6

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01801
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01802
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01803
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01804
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01805
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01806
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01807
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01808
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01809
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01810
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01811
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01812
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01813
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01814
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01815
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01816
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01817
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01818
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01819
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01820
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01821
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01822
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01823
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01824
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01825
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01826
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01827
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01828
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01829
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01830
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01831
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01832
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01833
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01834
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01835
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01836
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01837
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01838
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01839
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01840
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01841
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01842
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01843
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01844
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01845
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01846
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01847
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01848
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01849
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01850

theorem solution (n : Nat)
    (hn : 755098777861 < n) (hupper : n <= 857157375181) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 804496505083 n with h2 | h2
  · -- n > 804496505083
    rcases Nat.lt_or_ge 829353415063 n with h4 | h4
    · -- n > 829353415063
      rcases Nat.lt_or_ge 842071092491 n with h6 | h6
      · -- n > 842071092491
        rcases Nat.lt_or_ge 848503553197 n with h8 | h8
        · -- n > 848503553197
          rcases Nat.lt_or_ge 852819387011 n with h10 | h10
          · -- n > 852819387011
            rcases Nat.lt_or_ge 854985604663 n with h12 | h12
            · -- n > 854985604663
              exact RamareSaouter2003.prime_interval_nat_ladder_c01850 n (by omega) (by omega)
            · -- n <= 854985604663
              exact RamareSaouter2003.prime_interval_nat_ladder_c01849 n (by omega) (by omega)
          · -- n <= 852819387011
            rcases Nat.lt_or_ge 850658707957 n with h12 | h12
            · -- n > 850658707957
              exact RamareSaouter2003.prime_interval_nat_ladder_c01848 n (by omega) (by omega)
            · -- n <= 850658707957
              exact RamareSaouter2003.prime_interval_nat_ladder_c01847 n (by omega) (by omega)
        · -- n <= 848503553197
          rcases Nat.lt_or_ge 844209759691 n with h10 | h10
          · -- n > 844209759691
            rcases Nat.lt_or_ge 846353908553 n with h12 | h12
            · -- n > 846353908553
              exact RamareSaouter2003.prime_interval_nat_ladder_c01846 n (by omega) (by omega)
            · -- n <= 846353908553
              exact RamareSaouter2003.prime_interval_nat_ladder_c01845 n (by omega) (by omega)
          · -- n <= 844209759691
            exact RamareSaouter2003.prime_interval_nat_ladder_c01844 n (by omega) (by omega)
      · -- n <= 842071092491
        rcases Nat.lt_or_ge 835687839713 n with h8 | h8
        · -- n > 835687839713
          rcases Nat.lt_or_ge 837810146603 n with h10 | h10
          · -- n > 837810146603
            rcases Nat.lt_or_ge 839937892853 n with h12 | h12
            · -- n > 839937892853
              exact RamareSaouter2003.prime_interval_nat_ladder_c01843 n (by omega) (by omega)
            · -- n <= 839937892853
              exact RamareSaouter2003.prime_interval_nat_ladder_c01842 n (by omega) (by omega)
          · -- n <= 837810146603
            exact RamareSaouter2003.prime_interval_nat_ladder_c01841 n (by omega) (by omega)
        · -- n <= 835687839713
          rcases Nat.lt_or_ge 831459487907 n with h10 | h10
          · -- n > 831459487907
            rcases Nat.lt_or_ge 833570958149 n with h12 | h12
            · -- n > 833570958149
              exact RamareSaouter2003.prime_interval_nat_ladder_c01840 n (by omega) (by omega)
            · -- n <= 833570958149
              exact RamareSaouter2003.prime_interval_nat_ladder_c01839 n (by omega) (by omega)
          · -- n <= 831459487907
            exact RamareSaouter2003.prime_interval_nat_ladder_c01838 n (by omega) (by omega)
    · -- n <= 829353415063
      rcases Nat.lt_or_ge 816829545913 n with h6 | h6
      · -- n > 816829545913
        rcases Nat.lt_or_ge 823067441743 n with h8 | h8
        · -- n > 823067441743
          rcases Nat.lt_or_ge 825157405847 n with h10 | h10
          · -- n > 825157405847
            rcases Nat.lt_or_ge 827252725643 n with h12 | h12
            · -- n > 827252725643
              exact RamareSaouter2003.prime_interval_nat_ladder_c01837 n (by omega) (by omega)
            · -- n <= 827252725643
              exact RamareSaouter2003.prime_interval_nat_ladder_c01836 n (by omega) (by omega)
          · -- n <= 825157405847
            exact RamareSaouter2003.prime_interval_nat_ladder_c01835 n (by omega) (by omega)
        · -- n <= 823067441743
          rcases Nat.lt_or_ge 818903525569 n with h10 | h10
          · -- n > 818903525569
            rcases Nat.lt_or_ge 820982819641 n with h12 | h12
            · -- n > 820982819641
              exact RamareSaouter2003.prime_interval_nat_ladder_c01834 n (by omega) (by omega)
            · -- n <= 820982819641
              exact RamareSaouter2003.prime_interval_nat_ladder_c01833 n (by omega) (by omega)
          · -- n <= 818903525569
            exact RamareSaouter2003.prime_interval_nat_ladder_c01832 n (by omega) (by omega)
      · -- n <= 816829545913
        rcases Nat.lt_or_ge 810639356369 n with h8 | h8
        · -- n > 810639356369
          rcases Nat.lt_or_ge 812697474959 n with h10 | h10
          · -- n > 812697474959
            rcases Nat.lt_or_ge 814760866949 n with h12 | h12
            · -- n > 814760866949
              exact RamareSaouter2003.prime_interval_nat_ladder_c01831 n (by omega) (by omega)
            · -- n <= 814760866949
              exact RamareSaouter2003.prime_interval_nat_ladder_c01830 n (by omega) (by omega)
          · -- n <= 812697474959
            exact RamareSaouter2003.prime_interval_nat_ladder_c01829 n (by omega) (by omega)
        · -- n <= 810639356369
          rcases Nat.lt_or_ge 806538884971 n with h10 | h10
          · -- n > 806538884971
            rcases Nat.lt_or_ge 808586497561 n with h12 | h12
            · -- n > 808586497561
              exact RamareSaouter2003.prime_interval_nat_ladder_c01828 n (by omega) (by omega)
            · -- n <= 808586497561
              exact RamareSaouter2003.prime_interval_nat_ladder_c01827 n (by omega) (by omega)
          · -- n <= 806538884971
            exact RamareSaouter2003.prime_interval_nat_ladder_c01826 n (by omega) (by omega)
  · -- n <= 804496505083
    rcases Nat.lt_or_ge 778415650919 n with h4 | h4
    · -- n > 778415650919
      rcases Nat.lt_or_ge 790345232543 n with h6 | h6
      · -- n > 790345232543
        rcases Nat.lt_or_ge 796379043311 n with h8 | h8
        · -- n > 796379043311
          rcases Nat.lt_or_ge 800427389533 n with h10 | h10
          · -- n > 800427389533
            rcases Nat.lt_or_ge 802459344397 n with h12 | h12
            · -- n > 802459344397
              exact RamareSaouter2003.prime_interval_nat_ladder_c01825 n (by omega) (by omega)
            · -- n <= 802459344397
              exact RamareSaouter2003.prime_interval_nat_ladder_c01824 n (by omega) (by omega)
          · -- n <= 800427389533
            rcases Nat.lt_or_ge 798400626973 n with h12 | h12
            · -- n > 798400626973
              exact RamareSaouter2003.prime_interval_nat_ladder_c01823 n (by omega) (by omega)
            · -- n <= 798400626973
              exact RamareSaouter2003.prime_interval_nat_ladder_c01822 n (by omega) (by omega)
        · -- n <= 796379043311
          rcases Nat.lt_or_ge 792351359411 n with h10 | h10
          · -- n > 792351359411
            rcases Nat.lt_or_ge 794362625213 n with h12 | h12
            · -- n > 794362625213
              exact RamareSaouter2003.prime_interval_nat_ladder_c01821 n (by omega) (by omega)
            · -- n <= 794362625213
              exact RamareSaouter2003.prime_interval_nat_ladder_c01820 n (by omega) (by omega)
          · -- n <= 792351359411
            exact RamareSaouter2003.prime_interval_nat_ladder_c01819 n (by omega) (by omega)
      · -- n <= 790345232543
        rcases Nat.lt_or_ge 784357553779 n with h8 | h8
        · -- n > 784357553779
          rcases Nat.lt_or_ge 786348343031 n with h10 | h10
          · -- n > 786348343031
            rcases Nat.lt_or_ge 788344231627 n with h12 | h12
            · -- n > 788344231627
              exact RamareSaouter2003.prime_interval_nat_ladder_c01818 n (by omega) (by omega)
            · -- n <= 788344231627
              exact RamareSaouter2003.prime_interval_nat_ladder_c01817 n (by omega) (by omega)
          · -- n <= 786348343031
            exact RamareSaouter2003.prime_interval_nat_ladder_c01816 n (by omega) (by omega)
        · -- n <= 784357553779
          rcases Nat.lt_or_ge 780391220867 n with h10 | h10
          · -- n > 780391220867
            rcases Nat.lt_or_ge 782371850857 n with h12 | h12
            · -- n > 782371850857
              exact RamareSaouter2003.prime_interval_nat_ladder_c01815 n (by omega) (by omega)
            · -- n <= 782371850857
              exact RamareSaouter2003.prime_interval_nat_ladder_c01814 n (by omega) (by omega)
          · -- n <= 780391220867
            exact RamareSaouter2003.prime_interval_nat_ladder_c01813 n (by omega) (by omega)
    · -- n <= 778415650919
      rcases Nat.lt_or_ge 766667763227 n with h6 | h6
      · -- n > 766667763227
        rcases Nat.lt_or_ge 772519170803 n with h8 | h8
        · -- n > 772519170803
          rcases Nat.lt_or_ge 774479638873 n with h10 | h10
          · -- n > 774479638873
            rcases Nat.lt_or_ge 776445127897 n with h12 | h12
            · -- n > 776445127897
              exact RamareSaouter2003.prime_interval_nat_ladder_c01812 n (by omega) (by omega)
            · -- n <= 776445127897
              exact RamareSaouter2003.prime_interval_nat_ladder_c01811 n (by omega) (by omega)
          · -- n <= 774479638873
            exact RamareSaouter2003.prime_interval_nat_ladder_c01810 n (by omega) (by omega)
        · -- n <= 772519170803
          rcases Nat.lt_or_ge 768613245901 n with h10 | h10
          · -- n > 768613245901
            rcases Nat.lt_or_ge 770563710803 n with h12 | h12
            · -- n > 770563710803
              exact RamareSaouter2003.prime_interval_nat_ladder_c01809 n (by omega) (by omega)
            · -- n <= 770563710803
              exact RamareSaouter2003.prime_interval_nat_ladder_c01808 n (by omega) (by omega)
          · -- n <= 768613245901
            exact RamareSaouter2003.prime_interval_nat_ladder_c01807 n (by omega) (by omega)
      · -- n <= 766667763227
        rcases Nat.lt_or_ge 760861080517 n with h8 | h8
        · -- n > 760861080517
          rcases Nat.lt_or_ge 762791693347 n with h10 | h10
          · -- n > 762791693347
            rcases Nat.lt_or_ge 764727250003 n with h12 | h12
            · -- n > 764727250003
              exact RamareSaouter2003.prime_interval_nat_ladder_c01806 n (by omega) (by omega)
            · -- n <= 764727250003
              exact RamareSaouter2003.prime_interval_nat_ladder_c01805 n (by omega) (by omega)
          · -- n <= 762791693347
            exact RamareSaouter2003.prime_interval_nat_ladder_c01804 n (by omega) (by omega)
        · -- n <= 760861080517
          rcases Nat.lt_or_ge 757014635473 n with h10 | h10
          · -- n > 757014635473
            rcases Nat.lt_or_ge 758935398811 n with h12 | h12
            · -- n > 758935398811
              exact RamareSaouter2003.prime_interval_nat_ladder_c01803 n (by omega) (by omega)
            · -- n <= 758935398811
              exact RamareSaouter2003.prime_interval_nat_ladder_c01802 n (by omega) (by omega)
          · -- n <= 757014635473
            exact RamareSaouter2003.prime_interval_nat_ladder_c01801 n (by omega) (by omega)
