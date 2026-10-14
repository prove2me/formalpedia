-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp116
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T18:28:04.280956+00:00
-- url     : https://prove2.me/submissions/725e8bc4-a5a3-487e-8e2f-8095c5c1c3a1

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05766
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05767
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05768
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05769
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05770
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05771
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05772
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05773
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05774
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05775
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05776
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05777
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05778
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05779
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05780
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05781
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05782
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05783
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05784
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05785
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05786
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05787
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05788
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05789
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05790
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05791
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05792
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05793
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05794
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05795
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05796
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05797
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05798
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05799
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05800

theorem solution (n : Nat)
    (hn : 25933117750214453 < n) (hupper : n <= 29870561433150253) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 27832329855660383 n with h2 | h2
  · -- n > 27832329855660383
    rcases Nat.lt_or_ge 28792674881097289 n with h4 | h4
    · -- n > 28792674881097289
      rcases Nat.lt_or_ge 29285233936089277 n with h6 | h6
      · -- n > 29285233936089277
        rcases Nat.lt_or_ge 29534670006963419 n with h8 | h8
        · -- n > 29534670006963419
          rcases Nat.lt_or_ge 29702146170264457 n with h10 | h10
          · -- n > 29702146170264457
            rcases Nat.lt_or_ge 29786238366792287 n with h12 | h12
            · -- n > 29786238366792287
              exact RamareSaouter2003.prime_interval_nat_ladder_c05800 n (by omega) (by omega)
            · -- n <= 29786238366792287
              exact RamareSaouter2003.prime_interval_nat_ladder_c05799 n (by omega) (by omega)
          · -- n <= 29702146170264457
            rcases Nat.lt_or_ge 29618291251878233 n with h12 | h12
            · -- n > 29618291251878233
              exact RamareSaouter2003.prime_interval_nat_ladder_c05798 n (by omega) (by omega)
            · -- n <= 29618291251878233
              exact RamareSaouter2003.prime_interval_nat_ladder_c05797 n (by omega) (by omega)
        · -- n <= 29534670006963419
          rcases Nat.lt_or_ge 29368136872128143 n with h10 | h10
          · -- n > 29368136872128143
            rcases Nat.lt_or_ge 29451285731483711 n with h12 | h12
            · -- n > 29451285731483711
              exact RamareSaouter2003.prime_interval_nat_ladder_c05796 n (by omega) (by omega)
            · -- n <= 29451285731483711
              exact RamareSaouter2003.prime_interval_nat_ladder_c05795 n (by omega) (by omega)
          · -- n <= 29368136872128143
            exact RamareSaouter2003.prime_interval_nat_ladder_c05794 n (by omega) (by omega)
      · -- n <= 29285233936089277
        rcases Nat.lt_or_ge 29037913511789893 n with h8 | h8
        · -- n > 29037913511789893
          rcases Nat.lt_or_ge 29120123930271961 n with h10 | h10
          · -- n > 29120123930271961
            rcases Nat.lt_or_ge 29202555118792067 n with h12 | h12
            · -- n > 29202555118792067
              exact RamareSaouter2003.prime_interval_nat_ladder_c05793 n (by omega) (by omega)
            · -- n <= 29202555118792067
              exact RamareSaouter2003.prime_interval_nat_ladder_c05792 n (by omega) (by omega)
          · -- n <= 29120123930271961
            exact RamareSaouter2003.prime_interval_nat_ladder_c05791 n (by omega) (by omega)
        · -- n <= 29037913511789893
          rcases Nat.lt_or_ge 28874188975646659 n with h10 | h10
          · -- n > 28874188975646659
            rcases Nat.lt_or_ge 28955936719744283 n with h12 | h12
            · -- n > 28955936719744283
              exact RamareSaouter2003.prime_interval_nat_ladder_c05790 n (by omega) (by omega)
            · -- n <= 28955936719744283
              exact RamareSaouter2003.prime_interval_nat_ladder_c05789 n (by omega) (by omega)
          · -- n <= 28874188975646659
            exact RamareSaouter2003.prime_interval_nat_ladder_c05788 n (by omega) (by omega)
    · -- n <= 28792674881097289
      rcases Nat.lt_or_ge 28308422381545091 n with h6 | h6
      · -- n > 28308422381545091
        rcases Nat.lt_or_ge 28549517062764619 n with h8 | h8
        · -- n > 28549517062764619
          rcases Nat.lt_or_ge 28630334168107897 n with h10 | h10
          · -- n > 28630334168107897
            rcases Nat.lt_or_ge 28711390569795919 n with h12 | h12
            · -- n > 28711390569795919
              exact RamareSaouter2003.prime_interval_nat_ladder_c05787 n (by omega) (by omega)
            · -- n <= 28711390569795919
              exact RamareSaouter2003.prime_interval_nat_ladder_c05786 n (by omega) (by omega)
          · -- n <= 28630334168107897
            exact RamareSaouter2003.prime_interval_nat_ladder_c05785 n (by omega) (by omega)
        · -- n <= 28549517062764619
          rcases Nat.lt_or_ge 28388558074513279 n with h10 | h10
          · -- n > 28388558074513279
            rcases Nat.lt_or_ge 28468913707696087 n with h12 | h12
            · -- n > 28468913707696087
              exact RamareSaouter2003.prime_interval_nat_ladder_c05784 n (by omega) (by omega)
            · -- n <= 28468913707696087
              exact RamareSaouter2003.prime_interval_nat_ladder_c05783 n (by omega) (by omega)
          · -- n <= 28388558074513279
            exact RamareSaouter2003.prime_interval_nat_ladder_c05782 n (by omega) (by omega)
      · -- n <= 28308422381545091
        rcases Nat.lt_or_ge 28069343495992297 n with h8 | h8
        · -- n > 28069343495992297
          rcases Nat.lt_or_ge 28148808166659227 n with h10 | h10
          · -- n > 28148808166659227
            rcases Nat.lt_or_ge 28228501067246453 n with h12 | h12
            · -- n > 28228501067246453
              exact RamareSaouter2003.prime_interval_nat_ladder_c05781 n (by omega) (by omega)
            · -- n <= 28228501067246453
              exact RamareSaouter2003.prime_interval_nat_ladder_c05780 n (by omega) (by omega)
          · -- n <= 28148808166659227
            exact RamareSaouter2003.prime_interval_nat_ladder_c05779 n (by omega) (by omega)
        · -- n <= 28069343495992297
          rcases Nat.lt_or_ge 27911118725755787 n with h10 | h10
          · -- n > 27911118725755787
            rcases Nat.lt_or_ge 27990140758440127 n with h12 | h12
            · -- n > 27990140758440127
              exact RamareSaouter2003.prime_interval_nat_ladder_c05778 n (by omega) (by omega)
            · -- n <= 27990140758440127
              exact RamareSaouter2003.prime_interval_nat_ladder_c05777 n (by omega) (by omega)
          · -- n <= 27911118725755787
            exact RamareSaouter2003.prime_interval_nat_ladder_c05776 n (by omega) (by omega)
  · -- n <= 27832329855660383
    rcases Nat.lt_or_ge 26827998777647933 n with h4 | h4
    · -- n > 26827998777647933
      rcases Nat.lt_or_ge 27286943800394507 n with h6 | h6
      · -- n > 27286943800394507
        rcases Nat.lt_or_ge 27519357318504959 n with h8 | h8
        · -- n > 27519357318504959
          rcases Nat.lt_or_ge 27675402961587169 n with h10 | h10
          · -- n > 27675402961587169
            rcases Nat.lt_or_ge 27753752635691963 n with h12 | h12
            · -- n > 27753752635691963
              exact RamareSaouter2003.prime_interval_nat_ladder_c05775 n (by omega) (by omega)
            · -- n <= 27753752635691963
              exact RamareSaouter2003.prime_interval_nat_ladder_c05774 n (by omega) (by omega)
          · -- n <= 27675402961587169
            rcases Nat.lt_or_ge 27597269339849089 n with h12 | h12
            · -- n > 27597269339849089
              exact RamareSaouter2003.prime_interval_nat_ladder_c05773 n (by omega) (by omega)
            · -- n <= 27597269339849089
              exact RamareSaouter2003.prime_interval_nat_ladder_c05772 n (by omega) (by omega)
        · -- n <= 27519357318504959
          rcases Nat.lt_or_ge 27364200485723557 n with h10 | h10
          · -- n > 27364200485723557
            rcases Nat.lt_or_ge 27441666091401923 n with h12 | h12
            · -- n > 27441666091401923
              exact RamareSaouter2003.prime_interval_nat_ladder_c05771 n (by omega) (by omega)
            · -- n <= 27441666091401923
              exact RamareSaouter2003.prime_interval_nat_ladder_c05770 n (by omega) (by omega)
          · -- n <= 27364200485723557
            exact RamareSaouter2003.prime_interval_nat_ladder_c05769 n (by omega) (by omega)
      · -- n <= 27286943800394507
        rcases Nat.lt_or_ge 27056508066862457 n with h8 | h8
        · -- n > 27056508066862457
          rcases Nat.lt_or_ge 27133110588425747 n with h10 | h10
          · -- n > 27133110588425747
            rcases Nat.lt_or_ge 27209925669284399 n with h12 | h12
            · -- n > 27209925669284399
              exact RamareSaouter2003.prime_interval_nat_ladder_c05768 n (by omega) (by omega)
            · -- n <= 27209925669284399
              exact RamareSaouter2003.prime_interval_nat_ladder_c05767 n (by omega) (by omega)
          · -- n <= 27133110588425747
            exact RamareSaouter2003.prime_interval_nat_ladder_c05766 n (by omega) (by omega)
        · -- n <= 27056508066862457
          rcases Nat.lt_or_ge 26903956558578397 n with h10 | h10
          · -- n > 26903956558578397
            rcases Nat.lt_or_ge 26980119260380513 n with h12 | h12
            · -- n > 26980119260380513
              exact RamareSaouter2003.prime_interval_nat_ladder_c05765 n (by omega) (by omega)
            · -- n <= 26980119260380513
              exact RamareSaouter2003.prime_interval_nat_ladder_c05764 n (by omega) (by omega)
          · -- n <= 26903956558578397
            exact RamareSaouter2003.prime_interval_nat_ladder_c05763 n (by omega) (by omega)
    · -- n <= 26827998777647933
      rcases Nat.lt_or_ge 26376773648339063 n with h6 | h6
      · -- n > 26376773648339063
        rcases Nat.lt_or_ge 26601429646831517 n with h8 | h8
        · -- n > 26601429646831517
          rcases Nat.lt_or_ge 26676740869841129 n with h10 | h10
          · -- n > 26676740869841129
            rcases Nat.lt_or_ge 26752264202954489 n with h12 | h12
            · -- n > 26752264202954489
              exact RamareSaouter2003.prime_interval_nat_ladder_c05762 n (by omega) (by omega)
            · -- n <= 26752264202954489
              exact RamareSaouter2003.prime_interval_nat_ladder_c05761 n (by omega) (by omega)
          · -- n <= 26676740869841129
            exact RamareSaouter2003.prime_interval_nat_ladder_c05760 n (by omega) (by omega)
        · -- n <= 26601429646831517
          rcases Nat.lt_or_ge 26451447627655019 n with h10 | h10
          · -- n > 26451447627655019
            rcases Nat.lt_or_ge 26526337913342447 n with h12 | h12
            · -- n > 26526337913342447
              exact RamareSaouter2003.prime_interval_nat_ladder_c05759 n (by omega) (by omega)
            · -- n <= 26526337913342447
              exact RamareSaouter2003.prime_interval_nat_ladder_c05758 n (by omega) (by omega)
          · -- n <= 26451447627655019
            exact RamareSaouter2003.prime_interval_nat_ladder_c05757 n (by omega) (by omega)
      · -- n <= 26376773648339063
        rcases Nat.lt_or_ge 26154007967938423 n with h8 | h8
        · -- n > 26154007967938423
          rcases Nat.lt_or_ge 26228056195644403 n with h10 | h10
          · -- n > 26228056195644403
            rcases Nat.lt_or_ge 26302309008834953 n with h12 | h12
            · -- n > 26302309008834953
              exact RamareSaouter2003.prime_interval_nat_ladder_c05756 n (by omega) (by omega)
            · -- n <= 26302309008834953
              exact RamareSaouter2003.prime_interval_nat_ladder_c05755 n (by omega) (by omega)
          · -- n <= 26228056195644403
            exact RamareSaouter2003.prime_interval_nat_ladder_c05754 n (by omega) (by omega)
        · -- n <= 26154007967938423
          rcases Nat.lt_or_ge 26006539990476803 n with h10 | h10
          · -- n > 26006539990476803
            rcases Nat.lt_or_ge 26080170348444973 n with h12 | h12
            · -- n > 26080170348444973
              exact RamareSaouter2003.prime_interval_nat_ladder_c05753 n (by omega) (by omega)
            · -- n <= 26080170348444973
              exact RamareSaouter2003.prime_interval_nat_ladder_c05752 n (by omega) (by omega)
          · -- n <= 26006539990476803
            exact RamareSaouter2003.prime_interval_nat_ladder_c05751 n (by omega) (by omega)
