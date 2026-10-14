-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp142
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T04:40:13.6174+00:00
-- url     : https://prove2.me/submissions/683b9abf-b9bc-4cfd-98fd-f5139dedb371

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07100

theorem solution (n : Nat)
    (hn : 1023391151980165547 < n) (hupper : n <= 1178786480577465181) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1098344295172336391 n with h2 | h2
  · -- n > 1098344295172336391
    rcases Nat.lt_or_ge 1136247279940535557 n with h4 | h4
    · -- n > 1136247279940535557
      rcases Nat.lt_or_ge 1155686609580275939 n with h6 | h6
      · -- n > 1155686609580275939
        rcases Nat.lt_or_ge 1165530489251140093 n with h8 | h8
        · -- n > 1165530489251140093
          rcases Nat.lt_or_ge 1172139764459223617 n with h10 | h10
          · -- n > 1172139764459223617
            rcases Nat.lt_or_ge 1175458432803432331 n with h12 | h12
            · -- n > 1175458432803432331
              exact RamareSaouter2003.prime_interval_nat_ladder_c07100 n (by omega) (by omega)
            · -- n <= 1175458432803432331
              exact RamareSaouter2003.prime_interval_nat_ladder_c07099 n (by omega) (by omega)
          · -- n <= 1172139764459223617
            rcases Nat.lt_or_ge 1168830462307768853 n with h12 | h12
            · -- n > 1168830462307768853
              exact RamareSaouter2003.prime_interval_nat_ladder_c07098 n (by omega) (by omega)
            · -- n <= 1168830462307768853
              exact RamareSaouter2003.prime_interval_nat_ladder_c07097 n (by omega) (by omega)
        · -- n <= 1165530489251140093
          rcases Nat.lt_or_ge 1158958481466096149 n with h10 | h10
          · -- n > 1158958481466096149
            rcases Nat.lt_or_ge 1162239838459899973 n with h12 | h12
            · -- n > 1162239838459899973
              exact RamareSaouter2003.prime_interval_nat_ladder_c07096 n (by omega) (by omega)
            · -- n <= 1162239838459899973
              exact RamareSaouter2003.prime_interval_nat_ladder_c07095 n (by omega) (by omega)
          · -- n <= 1158958481466096149
            exact RamareSaouter2003.prime_interval_nat_ladder_c07094 n (by omega) (by omega)
      · -- n <= 1155686609580275939
        rcases Nat.lt_or_ge 1145925721471675439 n with h8 | h8
        · -- n > 1145925721471675439
          rcases Nat.lt_or_ge 1149170166071243581 n with h10 | h10
          · -- n > 1149170166071243581
            rcases Nat.lt_or_ge 1152423819804356081 n with h12 | h12
            · -- n > 1152423819804356081
              exact RamareSaouter2003.prime_interval_nat_ladder_c07093 n (by omega) (by omega)
            · -- n <= 1152423819804356081
              exact RamareSaouter2003.prime_interval_nat_ladder_c07092 n (by omega) (by omega)
          · -- n <= 1149170166071243581
            exact RamareSaouter2003.prime_interval_nat_ladder_c07091 n (by omega) (by omega)
        · -- n <= 1145925721471675439
          rcases Nat.lt_or_ge 1139464321290118919 n with h10 | h10
          · -- n > 1139464321290118919
            rcases Nat.lt_or_ge 1142690472720930739 n with h12 | h12
            · -- n > 1142690472720930739
              exact RamareSaouter2003.prime_interval_nat_ladder_c07090 n (by omega) (by omega)
            · -- n <= 1142690472720930739
              exact RamareSaouter2003.prime_interval_nat_ladder_c07089 n (by omega) (by omega)
          · -- n <= 1139464321290118919
            exact RamareSaouter2003.prime_interval_nat_ladder_c07088 n (by omega) (by omega)
    · -- n <= 1136247279940535557
      rcases Nat.lt_or_ge 1117135093169633003 n with h6 | h6
      · -- n > 1117135093169633003
        rcases Nat.lt_or_ge 1126650665874249221 n with h8 | h8
        · -- n > 1126650665874249221
          rcases Nat.lt_or_ge 1129840414068831833 n with h10 | h10
          · -- n > 1129840414068831833
            rcases Nat.lt_or_ge 1133039303817970357 n with h12 | h12
            · -- n > 1133039303817970357
              exact RamareSaouter2003.prime_interval_nat_ladder_c07087 n (by omega) (by omega)
            · -- n <= 1133039303817970357
              exact RamareSaouter2003.prime_interval_nat_ladder_c07086 n (by omega) (by omega)
          · -- n <= 1129840414068831833
            exact RamareSaouter2003.prime_interval_nat_ladder_c07085 n (by omega) (by omega)
        · -- n <= 1126650665874249221
          rcases Nat.lt_or_ge 1120298036996312393 n with h10 | h10
          · -- n > 1120298036996312393
            rcases Nat.lt_or_ge 1123469793493410887 n with h12 | h12
            · -- n > 1123469793493410887
              exact RamareSaouter2003.prime_interval_nat_ladder_c07084 n (by omega) (by omega)
            · -- n <= 1123469793493410887
              exact RamareSaouter2003.prime_interval_nat_ladder_c07083 n (by omega) (by omega)
          · -- n <= 1120298036996312393
            exact RamareSaouter2003.prime_interval_nat_ladder_c07082 n (by omega) (by omega)
      · -- n <= 1117135093169633003
        rcases Nat.lt_or_ge 1107699748389186919 n with h8 | h8
        · -- n > 1107699748389186919
          rcases Nat.lt_or_ge 1110835975087275887 n with h10 | h10
          · -- n > 1110835975087275887
            rcases Nat.lt_or_ge 1113981087334355441 n with h12 | h12
            · -- n > 1113981087334355441
              exact RamareSaouter2003.prime_interval_nat_ladder_c07081 n (by omega) (by omega)
            · -- n <= 1113981087334355441
              exact RamareSaouter2003.prime_interval_nat_ladder_c07080 n (by omega) (by omega)
          · -- n <= 1110835975087275887
            exact RamareSaouter2003.prime_interval_nat_ladder_c07079 n (by omega) (by omega)
        · -- n <= 1107699748389186919
          rcases Nat.lt_or_ge 1101453869499602639 n with h10 | h10
          · -- n > 1101453869499602639
            rcases Nat.lt_or_ge 1104572419818534911 n with h12 | h12
            · -- n > 1104572419818534911
              exact RamareSaouter2003.prime_interval_nat_ladder_c07078 n (by omega) (by omega)
            · -- n <= 1104572419818534911
              exact RamareSaouter2003.prime_interval_nat_ladder_c07077 n (by omega) (by omega)
          · -- n <= 1101453869499602639
            exact RamareSaouter2003.prime_interval_nat_ladder_c07076 n (by omega) (by omega)
  · -- n <= 1098344295172336391
    rcases Nat.lt_or_ge 1058707905085886689 n with h4 | h4
    · -- n > 1058707905085886689
      rcases Nat.lt_or_ge 1076820795836329913 n with h6 | h6
      · -- n > 1076820795836329913
        rcases Nat.lt_or_ge 1085993069421192007 n with h8 | h8
        · -- n > 1085993069421192007
          rcases Nat.lt_or_ge 1092151277235397751 n with h10 | h10
          · -- n > 1092151277235397751
            rcases Nat.lt_or_ge 1095243327559280437 n with h12 | h12
            · -- n > 1095243327559280437
              exact RamareSaouter2003.prime_interval_nat_ladder_c07075 n (by omega) (by omega)
            · -- n <= 1095243327559280437
              exact RamareSaouter2003.prime_interval_nat_ladder_c07074 n (by omega) (by omega)
          · -- n <= 1092151277235397751
            rcases Nat.lt_or_ge 1089067847141481619 n with h12 | h12
            · -- n > 1089067847141481619
              exact RamareSaouter2003.prime_interval_nat_ladder_c07073 n (by omega) (by omega)
            · -- n <= 1089067847141481619
              exact RamareSaouter2003.prime_interval_nat_ladder_c07072 n (by omega) (by omega)
        · -- n <= 1085993069421192007
          rcases Nat.lt_or_ge 1079869599600995743 n with h10 | h10
          · -- n > 1079869599600995743
            rcases Nat.lt_or_ge 1082927013172832507 n with h12 | h12
            · -- n > 1082927013172832507
              exact RamareSaouter2003.prime_interval_nat_ladder_c07071 n (by omega) (by omega)
            · -- n <= 1082927013172832507
              exact RamareSaouter2003.prime_interval_nat_ladder_c07070 n (by omega) (by omega)
          · -- n <= 1079869599600995743
            exact RamareSaouter2003.prime_interval_nat_ladder_c07069 n (by omega) (by omega)
      · -- n <= 1076820795836329913
        rcases Nat.lt_or_ge 1067725932197611669 n with h8 | h8
        · -- n > 1067725932197611669
          rcases Nat.lt_or_ge 1070748988653334723 n with h10 | h10
          · -- n > 1070748988653334723
            rcases Nat.lt_or_ge 1073780606502889927 n with h12 | h12
            · -- n > 1073780606502889927
              exact RamareSaouter2003.prime_interval_nat_ladder_c07068 n (by omega) (by omega)
            · -- n <= 1073780606502889927
              exact RamareSaouter2003.prime_interval_nat_ladder_c07067 n (by omega) (by omega)
          · -- n <= 1070748988653334723
            exact RamareSaouter2003.prime_interval_nat_ladder_c07066 n (by omega) (by omega)
        · -- n <= 1067725932197611669
          rcases Nat.lt_or_ge 1061705424991458437 n with h10 | h10
          · -- n > 1061705424991458437
            rcases Nat.lt_or_ge 1064711408750593861 n with h12 | h12
            · -- n > 1064711408750593861
              exact RamareSaouter2003.prime_interval_nat_ladder_c07065 n (by omega) (by omega)
            · -- n <= 1064711408750593861
              exact RamareSaouter2003.prime_interval_nat_ladder_c07064 n (by omega) (by omega)
          · -- n <= 1061705424991458437
            exact RamareSaouter2003.prime_interval_nat_ladder_c07063 n (by omega) (by omega)
    · -- n <= 1058707905085886689
      rcases Nat.lt_or_ge 1040899694905188043 n with h6 | h6
      · -- n > 1040899694905188043
        rcases Nat.lt_or_ge 1049766042223203343 n with h8 | h8
        · -- n > 1049766042223203343
          rcases Nat.lt_or_ge 1052738234695091951 n with h10 | h10
          · -- n > 1052738234695091951
            rcases Nat.lt_or_ge 1055718853708261121 n with h12 | h12
            · -- n > 1055718853708261121
              exact RamareSaouter2003.prime_interval_nat_ladder_c07062 n (by omega) (by omega)
            · -- n <= 1055718853708261121
              exact RamareSaouter2003.prime_interval_nat_ladder_c07061 n (by omega) (by omega)
          · -- n <= 1052738234695091951
            exact RamareSaouter2003.prime_interval_nat_ladder_c07060 n (by omega) (by omega)
        · -- n <= 1049766042223203343
          rcases Nat.lt_or_ge 1043846773736847569 n with h10 | h10
          · -- n > 1043846773736847569
            rcases Nat.lt_or_ge 1046802223719459979 n with h12 | h12
            · -- n > 1046802223719459979
              exact RamareSaouter2003.prime_interval_nat_ladder_c07059 n (by omega) (by omega)
            · -- n <= 1046802223719459979
              exact RamareSaouter2003.prime_interval_nat_ladder_c07058 n (by omega) (by omega)
          · -- n <= 1043846773736847569
            exact RamareSaouter2003.prime_interval_nat_ladder_c07057 n (by omega) (by omega)
      · -- n <= 1040899694905188043
        rcases Nat.lt_or_ge 1032108261835286683 n with h8 | h8
        · -- n > 1032108261835286683
          rcases Nat.lt_or_ge 1035030473866393547 n with h10 | h10
          · -- n > 1035030473866393547
            rcases Nat.lt_or_ge 1037960943006279209 n with h12 | h12
            · -- n > 1037960943006279209
              exact RamareSaouter2003.prime_interval_nat_ladder_c07056 n (by omega) (by omega)
            · -- n <= 1037960943006279209
              exact RamareSaouter2003.prime_interval_nat_ladder_c07055 n (by omega) (by omega)
          · -- n <= 1035030473866393547
            exact RamareSaouter2003.prime_interval_nat_ladder_c07054 n (by omega) (by omega)
        · -- n <= 1032108261835286683
          rcases Nat.lt_or_ge 1026288656992815269 n with h10 | h10
          · -- n > 1026288656992815269
            rcases Nat.lt_or_ge 1029194356498060591 n with h12 | h12
            · -- n > 1029194356498060591
              exact RamareSaouter2003.prime_interval_nat_ladder_c07053 n (by omega) (by omega)
            · -- n <= 1029194356498060591
              exact RamareSaouter2003.prime_interval_nat_ladder_c07052 n (by omega) (by omega)
          · -- n <= 1026288656992815269
            exact RamareSaouter2003.prime_interval_nat_ladder_c07051 n (by omega) (by omega)
