-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp159
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T10:52:34.443452+00:00
-- url     : https://prove2.me/submissions/e2362996-8e31-49a9-bf53-360f5d6898f2

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07885
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07886
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07887
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07888
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07889
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07890
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07891
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07892
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07893
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07894
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07895
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07896
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07897
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07898
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07899
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07900
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07901
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07902
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07903
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07904
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07905
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07906
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07907
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07908
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07909
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07910
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07911
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07912
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07913
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07914
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07915
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07916
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07917
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07918
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07919
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07920
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07921
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07922
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07923
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07924
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07925
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07926
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07927
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07928
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07929
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07930
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07931
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07932
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07933

theorem solution (n : Nat)
    (hn : 10816557704663328019 < n) (hupper : n <= 12423819217158574193) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 11575989636431613179 n with h2 | h2
  · -- n > 11575989636431613179
    rcases Nat.lt_or_ge 11975473730315685059 n with h4 | h4
    · -- n > 11975473730315685059
      rcases Nat.lt_or_ge 12180355836877149431 n with h6 | h6
      · -- n > 12180355836877149431
        rcases Nat.lt_or_ge 12284107308567224803 n with h8 | h8
        · -- n > 12284107308567224803
          rcases Nat.lt_or_ge 12353765865222523061 n with h10 | h10
          · -- n > 12353765865222523061
            rcases Nat.lt_or_ge 12388743169836437323 n with h12 | h12
            · -- n > 12388743169836437323
              exact RamareSaouter2003.prime_interval_nat_ladder_c07933 n (by omega) (by omega)
            · -- n <= 12388743169836437323
              exact RamareSaouter2003.prime_interval_nat_ladder_c07932 n (by omega) (by omega)
          · -- n <= 12353765865222523061
            rcases Nat.lt_or_ge 12318887389413421967 n with h12 | h12
            · -- n > 12318887389413421967
              exact RamareSaouter2003.prime_interval_nat_ladder_c07931 n (by omega) (by omega)
            · -- n <= 12318887389413421967
              exact RamareSaouter2003.prime_interval_nat_ladder_c07930 n (by omega) (by omega)
        · -- n <= 12284107308567224803
          rcases Nat.lt_or_ge 12214841981738606543 n with h10 | h10
          · -- n > 12214841981738606543
            rcases Nat.lt_or_ge 12249425792769958033 n with h12 | h12
            · -- n > 12249425792769958033
              exact RamareSaouter2003.prime_interval_nat_ladder_c07929 n (by omega) (by omega)
            · -- n <= 12249425792769958033
              exact RamareSaouter2003.prime_interval_nat_ladder_c07928 n (by omega) (by omega)
          · -- n <= 12214841981738606543
            exact RamareSaouter2003.prime_interval_nat_ladder_c07927 n (by omega) (by omega)
      · -- n <= 12180355836877149431
        rcases Nat.lt_or_ge 12077480404887213473 n with h8 | h8
        · -- n > 12077480404887213473
          rcases Nat.lt_or_ge 12111675389824346711 n with h10 | h10
          · -- n > 12111675389824346711
            rcases Nat.lt_or_ge 12145966906716801097 n with h12 | h12
            · -- n > 12145966906716801097
              exact RamareSaouter2003.prime_interval_nat_ladder_c07926 n (by omega) (by omega)
            · -- n <= 12145966906716801097
              exact RamareSaouter2003.prime_interval_nat_ladder_c07925 n (by omega) (by omega)
          · -- n <= 12111675389824346711
            exact RamareSaouter2003.prime_interval_nat_ladder_c07924 n (by omega) (by omega)
        · -- n <= 12077480404887213473
          rcases Nat.lt_or_ge 12009379838150775841 n with h10 | h10
          · -- n > 12009379838150775841
            rcases Nat.lt_or_ge 12043381928242464967 n with h12 | h12
            · -- n > 12043381928242464967
              exact RamareSaouter2003.prime_interval_nat_ladder_c07923 n (by omega) (by omega)
            · -- n <= 12043381928242464967
              exact RamareSaouter2003.prime_interval_nat_ladder_c07922 n (by omega) (by omega)
          · -- n <= 12009379838150775841
            exact RamareSaouter2003.prime_interval_nat_ladder_c07921 n (by omega) (by omega)
    · -- n <= 11975473730315685059
      rcases Nat.lt_or_ge 11774037544125691547 n with h6 | h6
      · -- n > 11774037544125691547
        rcases Nat.lt_or_ge 11874328575701731873 n with h8 | h8
        · -- n > 11874328575701731873
          rcases Nat.lt_or_ge 11907948273575589449 n with h10 | h10
          · -- n > 11907948273575589449
            rcases Nat.lt_or_ge 11941663234644516973 n with h12 | h12
            · -- n > 11941663234644516973
              exact RamareSaouter2003.prime_interval_nat_ladder_c07920 n (by omega) (by omega)
            · -- n <= 11941663234644516973
              exact RamareSaouter2003.prime_interval_nat_ladder_c07919 n (by omega) (by omega)
          · -- n <= 11907948273575589449
            exact RamareSaouter2003.prime_interval_nat_ladder_c07918 n (by omega) (by omega)
        · -- n <= 11874328575701731873
          rcases Nat.lt_or_ge 11807373377111810899 n with h10 | h10
          · -- n > 11807373377111810899
            rcases Nat.lt_or_ge 11840803670157143821 n with h12 | h12
            · -- n > 11840803670157143821
              exact RamareSaouter2003.prime_interval_nat_ladder_c07917 n (by omega) (by omega)
            · -- n <= 11840803670157143821
              exact RamareSaouter2003.prime_interval_nat_ladder_c07916 n (by omega) (by omega)
          · -- n <= 11807373377111810899
            exact RamareSaouter2003.prime_interval_nat_ladder_c07915 n (by omega) (by omega)
      · -- n <= 11774037544125691547
        rcases Nat.lt_or_ge 11674593615738689003 n with h8 | h8
        · -- n > 11674593615738689003
          rcases Nat.lt_or_ge 11707647917184459599 n with h10 | h10
          · -- n > 11707647917184459599
            rcases Nat.lt_or_ge 11740795806729650939 n with h12 | h12
            · -- n > 11740795806729650939
              exact RamareSaouter2003.prime_interval_nat_ladder_c07914 n (by omega) (by omega)
            · -- n <= 11740795806729650939
              exact RamareSaouter2003.prime_interval_nat_ladder_c07913 n (by omega) (by omega)
          · -- n <= 11707647917184459599
            exact RamareSaouter2003.prime_interval_nat_ladder_c07912 n (by omega) (by omega)
        · -- n <= 11674593615738689003
          rcases Nat.lt_or_ge 11608764819202722649 n with h10 | h10
          · -- n > 11608764819202722649
            rcases Nat.lt_or_ge 11641632744265080047 n with h12 | h12
            · -- n > 11641632744265080047
              exact RamareSaouter2003.prime_interval_nat_ladder_c07911 n (by omega) (by omega)
            · -- n <= 11641632744265080047
              exact RamareSaouter2003.prime_interval_nat_ladder_c07910 n (by omega) (by omega)
          · -- n <= 11608764819202722649
            exact RamareSaouter2003.prime_interval_nat_ladder_c07909 n (by omega) (by omega)
  · -- n <= 11575989636431613179
    rcases Nat.lt_or_ge 11189833385870506039 n with h4 | h4
    · -- n > 11189833385870506039
      rcases Nat.lt_or_ge 11381274208299825779 n with h6 | h6
      · -- n > 11381274208299825779
        rcases Nat.lt_or_ge 11478219034790463359 n with h8 | h8
        · -- n > 11478219034790463359
          rcases Nat.lt_or_ge 11510717323544654791 n with h10 | h10
          · -- n > 11510717323544654791
            rcases Nat.lt_or_ge 11543307509705489911 n with h12 | h12
            · -- n > 11543307509705489911
              exact RamareSaouter2003.prime_interval_nat_ladder_c07908 n (by omega) (by omega)
            · -- n <= 11543307509705489911
              exact RamareSaouter2003.prime_interval_nat_ladder_c07907 n (by omega) (by omega)
          · -- n <= 11510717323544654791
            exact RamareSaouter2003.prime_interval_nat_ladder_c07906 n (by omega) (by omega)
        · -- n <= 11478219034790463359
          rcases Nat.lt_or_ge 11413497921831418607 n with h10 | h10
          · -- n > 11413497921831418607
            rcases Nat.lt_or_ge 11445812697752893283 n with h12 | h12
            · -- n > 11445812697752893283
              exact RamareSaouter2003.prime_interval_nat_ladder_c07905 n (by omega) (by omega)
            · -- n <= 11445812697752893283
              exact RamareSaouter2003.prime_interval_nat_ladder_c07904 n (by omega) (by omega)
          · -- n <= 11413497921831418607
            exact RamareSaouter2003.prime_interval_nat_ladder_c07903 n (by omega) (by omega)
      · -- n <= 11381274208299825779
        rcases Nat.lt_or_ge 11285148183592271983 n with h8 | h8
        · -- n > 11285148183592271983
          rcases Nat.lt_or_ge 11317099902537442807 n with h10 | h10
          · -- n > 11317099902537442807
            rcases Nat.lt_or_ge 11349142087656104383 n with h12 | h12
            · -- n > 11349142087656104383
              exact RamareSaouter2003.prime_interval_nat_ladder_c07902 n (by omega) (by omega)
            · -- n <= 11349142087656104383
              exact RamareSaouter2003.prime_interval_nat_ladder_c07901 n (by omega) (by omega)
          · -- n <= 11317099902537442807
            exact RamareSaouter2003.prime_interval_nat_ladder_c07900 n (by omega) (by omega)
        · -- n <= 11285148183592271983
          rcases Nat.lt_or_ge 11221515196416632179 n with h10 | h10
          · -- n > 11221515196416632179
            rcases Nat.lt_or_ge 11253286685240948129 n with h12 | h12
            · -- n > 11253286685240948129
              exact RamareSaouter2003.prime_interval_nat_ladder_c07899 n (by omega) (by omega)
            · -- n <= 11253286685240948129
              exact RamareSaouter2003.prime_interval_nat_ladder_c07898 n (by omega) (by omega)
          · -- n <= 11221515196416632179
            exact RamareSaouter2003.prime_interval_nat_ladder_c07897 n (by omega) (by omega)
    · -- n <= 11189833385870506039
      rcases Nat.lt_or_ge 11001612276196946519 n with h6 | h6
      · -- n > 11001612276196946519
        rcases Nat.lt_or_ge 11095323770793968011 n with h8 | h8
        · -- n > 11095323770793968011
          rcases Nat.lt_or_ge 11126737778913780433 n with h10 | h10
          · -- n > 11126737778913780433
            rcases Nat.lt_or_ge 11158240976409686479 n with h12 | h12
            · -- n > 11158240976409686479
              exact RamareSaouter2003.prime_interval_nat_ladder_c07896 n (by omega) (by omega)
            · -- n <= 11158240976409686479
              exact RamareSaouter2003.prime_interval_nat_ladder_c07895 n (by omega) (by omega)
          · -- n <= 11126737778913780433
            exact RamareSaouter2003.prime_interval_nat_ladder_c07894 n (by omega) (by omega)
        · -- n <= 11095323770793968011
          rcases Nat.lt_or_ge 11032761210325921501 n with h10 | h10
          · -- n > 11032761210325921501
            rcases Nat.lt_or_ge 11063998303936923311 n with h12 | h12
            · -- n > 11063998303936923311
              exact RamareSaouter2003.prime_interval_nat_ladder_c07893 n (by omega) (by omega)
            · -- n <= 11063998303936923311
              exact RamareSaouter2003.prime_interval_nat_ladder_c07892 n (by omega) (by omega)
          · -- n <= 11032761210325921501
            exact RamareSaouter2003.prime_interval_nat_ladder_c07891 n (by omega) (by omega)
      · -- n <= 11001612276196946519
        rcases Nat.lt_or_ge 10908692654410059337 n with h8 | h8
        · -- n > 10908692654410059337
          rcases Nat.lt_or_ge 10939578426316599529 n with h10 | h10
          · -- n > 10939578426316599529
            rcases Nat.lt_or_ge 10970551375453184687 n with h12 | h12
            · -- n > 10970551375453184687
              exact RamareSaouter2003.prime_interval_nat_ladder_c07890 n (by omega) (by omega)
            · -- n <= 10970551375453184687
              exact RamareSaouter2003.prime_interval_nat_ladder_c07889 n (by omega) (by omega)
          · -- n <= 10939578426316599529
            exact RamareSaouter2003.prime_interval_nat_ladder_c07888 n (by omega) (by omega)
        · -- n <= 10908692654410059337
          rcases Nat.lt_or_ge 10847182438417416677 n with h10 | h10
          · -- n > 10847182438417416677
            rcases Nat.lt_or_ge 10877894060030258953 n with h12 | h12
            · -- n > 10877894060030258953
              exact RamareSaouter2003.prime_interval_nat_ladder_c07887 n (by omega) (by omega)
            · -- n <= 10877894060030258953
              exact RamareSaouter2003.prime_interval_nat_ladder_c07886 n (by omega) (by omega)
          · -- n <= 10847182438417416677
            exact RamareSaouter2003.prime_interval_nat_ladder_c07885 n (by omega) (by omega)
