-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp162
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T12:06:28.349865+00:00
-- url     : https://prove2.me/submissions/9e181d33-55d6-454a-a311-d8e081ba7727

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08050
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08080

theorem solution (n : Nat)
    (hn : 16390314104476856209 < n) (hupper : n <= 18775057895451734561) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 17541080249299231333 n with h2 | h2
  · -- n > 17541080249299231333
    rcases Nat.lt_or_ge 18146417021814391907 n with h4 | h4
    · -- n > 18146417021814391907
      rcases Nat.lt_or_ge 18456874972930351487 n with h6 | h6
      · -- n > 18456874972930351487
        rcases Nat.lt_or_ge 18592573540188019847 n with h8 | h8
        · -- n > 18592573540188019847
          rcases Nat.lt_or_ge 18683592793947070027 n with h10 | h10
          · -- n > 18683592793947070027
            rcases Nat.lt_or_ge 18729269526919720253 n with h12 | h12
            · -- n > 18729269526919720253
              exact RamareSaouter2003.prime_interval_nat_ladder_c08080 n (by omega) (by omega)
            · -- n <= 18729269526919720253
              exact RamareSaouter2003.prime_interval_nat_ladder_c08079 n (by omega) (by omega)
          · -- n <= 18683592793947070027
            rcases Nat.lt_or_ge 18638027700200840381 n with h12 | h12
            · -- n > 18638027700200840381
              exact RamareSaouter2003.prime_interval_nat_ladder_c08078 n (by omega) (by omega)
            · -- n <= 18638027700200840381
              exact RamareSaouter2003.prime_interval_nat_ladder_c08077 n (by omega) (by omega)
        · -- n <= 18592573540188019847
          rcases Nat.lt_or_ge 18501997443393056867 n with h10 | h10
          · -- n > 18501997443393056867
            rcases Nat.lt_or_ge 18547230231638446319 n with h12 | h12
            · -- n > 18547230231638446319
              exact RamareSaouter2003.prime_interval_nat_ladder_c08076 n (by omega) (by omega)
            · -- n <= 18547230231638446319
              exact RamareSaouter2003.prime_interval_nat_ladder_c08075 n (by omega) (by omega)
          · -- n <= 18501997443393056867
            exact RamareSaouter2003.prime_interval_nat_ladder_c08074 n (by omega) (by omega)
      · -- n <= 18456874972930351487
        rcases Nat.lt_or_ge 18300987940366322531 n with h8 | h8
        · -- n > 18300987940366322531
          rcases Nat.lt_or_ge 18352803502810142789 n with h10 | h10
          · -- n > 18352803502810142789
            rcases Nat.lt_or_ge 18404765580198457267 n with h12 | h12
            · -- n > 18404765580198457267
              exact RamareSaouter2003.prime_interval_nat_ladder_c08073 n (by omega) (by omega)
            · -- n <= 18404765580198457267
              exact RamareSaouter2003.prime_interval_nat_ladder_c08072 n (by omega) (by omega)
          · -- n <= 18352803502810142789
            exact RamareSaouter2003.prime_interval_nat_ladder_c08071 n (by omega) (by omega)
        · -- n <= 18300987940366322531
          rcases Nat.lt_or_ge 18197795025849212461 n with h10 | h10
          · -- n > 18197795025849212461
            rcases Nat.lt_or_ge 18249318556710917993 n with h12 | h12
            · -- n > 18249318556710917993
              exact RamareSaouter2003.prime_interval_nat_ladder_c08070 n (by omega) (by omega)
            · -- n <= 18249318556710917993
              exact RamareSaouter2003.prime_interval_nat_ladder_c08069 n (by omega) (by omega)
          · -- n <= 18197795025849212461
            exact RamareSaouter2003.prime_interval_nat_ladder_c08068 n (by omega) (by omega)
    · -- n <= 18146417021814391907
      rcases Nat.lt_or_ge 17841181870057346309 n with h6 | h6
      · -- n > 17841181870057346309
        rcases Nat.lt_or_ge 17993151982686361487 n with h8 | h8
        · -- n > 17993151982686361487
          rcases Nat.lt_or_ge 18044096130147886787 n with h10 | h10
          · -- n > 18044096130147886787
            rcases Nat.lt_or_ge 18095184005651157311 n with h12 | h12
            · -- n > 18095184005651157311
              exact RamareSaouter2003.prime_interval_nat_ladder_c08067 n (by omega) (by omega)
            · -- n <= 18095184005651157311
              exact RamareSaouter2003.prime_interval_nat_ladder_c08066 n (by omega) (by omega)
          · -- n <= 18044096130147886787
            exact RamareSaouter2003.prime_interval_nat_ladder_c08065 n (by omega) (by omega)
        · -- n <= 17993151982686361487
          rcases Nat.lt_or_ge 17891695276004247043 n with h10 | h10
          · -- n > 17891695276004247043
            rcases Nat.lt_or_ge 17942352073908219389 n with h12 | h12
            · -- n > 17942352073908219389
              exact RamareSaouter2003.prime_interval_nat_ladder_c08064 n (by omega) (by omega)
            · -- n <= 17942352073908219389
              exact RamareSaouter2003.prime_interval_nat_ladder_c08063 n (by omega) (by omega)
          · -- n <= 17891695276004247043
            exact RamareSaouter2003.prime_interval_nat_ladder_c08062 n (by omega) (by omega)
      · -- n <= 17841181870057346309
        rcases Nat.lt_or_ge 17690494599975654851 n with h8 | h8
        · -- n > 17690494599975654851
          rcases Nat.lt_or_ge 17740581689765322767 n with h10 | h10
          · -- n > 17740581689765322767
            rcases Nat.lt_or_ge 17790810656688336523 n with h12 | h12
            · -- n > 17790810656688336523
              exact RamareSaouter2003.prime_interval_nat_ladder_c08061 n (by omega) (by omega)
            · -- n <= 17790810656688336523
              exact RamareSaouter2003.prime_interval_nat_ladder_c08060 n (by omega) (by omega)
          · -- n <= 17740581689765322767
            exact RamareSaouter2003.prime_interval_nat_ladder_c08059 n (by omega) (by omega)
        · -- n <= 17690494599975654851
          rcases Nat.lt_or_ge 17590744279224166513 n with h10 | h10
          · -- n > 17590744279224166513
            rcases Nat.lt_or_ge 17640548868688986959 n with h12 | h12
            · -- n > 17640548868688986959
              exact RamareSaouter2003.prime_interval_nat_ladder_c08058 n (by omega) (by omega)
            · -- n <= 17640548868688986959
              exact RamareSaouter2003.prime_interval_nat_ladder_c08057 n (by omega) (by omega)
          · -- n <= 17590744279224166513
            exact RamareSaouter2003.prime_interval_nat_ladder_c08056 n (by omega) (by omega)
  · -- n <= 17541080249299231333
    rcases Nat.lt_or_ge 16955937034941535261 n with h4 | h4
    · -- n > 16955937034941535261
      rcases Nat.lt_or_ge 17246027647034915017 n with h6 | h6
      · -- n > 17246027647034915017
        rcases Nat.lt_or_ge 17392928358707030891 n with h8 | h8
        · -- n > 17392928358707030891
          rcases Nat.lt_or_ge 17442172865756441639 n with h10 | h10
          · -- n > 17442172865756441639
            rcases Nat.lt_or_ge 17491556646881294569 n with h12 | h12
            · -- n > 17491556646881294569
              exact RamareSaouter2003.prime_interval_nat_ladder_c08055 n (by omega) (by omega)
            · -- n <= 17491556646881294569
              exact RamareSaouter2003.prime_interval_nat_ladder_c08054 n (by omega) (by omega)
          · -- n <= 17442172865756441639
            exact RamareSaouter2003.prime_interval_nat_ladder_c08053 n (by omega) (by omega)
        · -- n <= 17392928358707030891
          rcases Nat.lt_or_ge 17294856414282104657 n with h10 | h10
          · -- n > 17294856414282104657
            rcases Nat.lt_or_ge 17343822881585132137 n with h12 | h12
            · -- n > 17343822881585132137
              exact RamareSaouter2003.prime_interval_nat_ladder_c08052 n (by omega) (by omega)
            · -- n <= 17343822881585132137
              exact RamareSaouter2003.prime_interval_nat_ladder_c08051 n (by omega) (by omega)
          · -- n <= 17294856414282104657
            exact RamareSaouter2003.prime_interval_nat_ladder_c08050 n (by omega) (by omega)
      · -- n <= 17246027647034915017
        rcases Nat.lt_or_ge 17100367452824070983 n with h8 | h8
        · -- n > 17100367452824070983
          rcases Nat.lt_or_ge 17148783802529316521 n with h10 | h10
          · -- n > 17148783802529316521
            rcases Nat.lt_or_ge 17197336921565530577 n with h12 | h12
            · -- n > 17197336921565530577
              exact RamareSaouter2003.prime_interval_nat_ladder_c08049 n (by omega) (by omega)
            · -- n <= 17197336921565530577
              exact RamareSaouter2003.prime_interval_nat_ladder_c08048 n (by omega) (by omega)
          · -- n <= 17148783802529316521
            exact RamareSaouter2003.prime_interval_nat_ladder_c08047 n (by omega) (by omega)
        · -- n <= 17100367452824070983
          rcases Nat.lt_or_ge 17003944490025753527 n with h10 | h10
          · -- n > 17003944490025753527
            rcases Nat.lt_or_ge 17052087805993466011 n with h12 | h12
            · -- n > 17052087805993466011
              exact RamareSaouter2003.prime_interval_nat_ladder_c08046 n (by omega) (by omega)
            · -- n <= 17052087805993466011
              exact RamareSaouter2003.prime_interval_nat_ladder_c08045 n (by omega) (by omega)
          · -- n <= 17003944490025753527
            exact RamareSaouter2003.prime_interval_nat_ladder_c08044 n (by omega) (by omega)
    · -- n <= 16955937034941535261
      rcases Nat.lt_or_ge 16670726551096915543 n with h6 | h6
      · -- n > 16670726551096915543
        rcases Nat.lt_or_ge 16812726958504248571 n with h8 | h8
        · -- n > 16812726958504248571
          rcases Nat.lt_or_ge 16860328613591938261 n with h10 | h10
          · -- n > 16860328613591938261
            rcases Nat.lt_or_ge 16908065177054745229 n with h12 | h12
            · -- n > 16908065177054745229
              exact RamareSaouter2003.prime_interval_nat_ladder_c08043 n (by omega) (by omega)
            · -- n <= 16908065177054745229
              exact RamareSaouter2003.prime_interval_nat_ladder_c08042 n (by omega) (by omega)
          · -- n <= 16860328613591938261
            exact RamareSaouter2003.prime_interval_nat_ladder_c08041 n (by omega) (by omega)
        · -- n <= 16812726958504248571
          rcases Nat.lt_or_ge 16717926468917603693 n with h10 | h10
          · -- n > 16717926468917603693
            rcases Nat.lt_or_ge 16765259778319800197 n with h12 | h12
            · -- n > 16765259778319800197
              exact RamareSaouter2003.prime_interval_nat_ladder_c08040 n (by omega) (by omega)
            · -- n <= 16765259778319800197
              exact RamareSaouter2003.prime_interval_nat_ladder_c08039 n (by omega) (by omega)
          · -- n <= 16717926468917603693
            exact RamareSaouter2003.prime_interval_nat_ladder_c08038 n (by omega) (by omega)
      · -- n <= 16670726551096915543
        rcases Nat.lt_or_ge 16529925481222116191 n with h8 | h8
        · -- n > 16529925481222116191
          rcases Nat.lt_or_ge 16576726640996539603 n with h10 | h10
          · -- n > 16576726640996539603
            rcases Nat.lt_or_ge 16623660010951085243 n with h12 | h12
            · -- n > 16623660010951085243
              exact RamareSaouter2003.prime_interval_nat_ladder_c08037 n (by omega) (by omega)
            · -- n <= 16623660010951085243
              exact RamareSaouter2003.prime_interval_nat_ladder_c08036 n (by omega) (by omega)
          · -- n <= 16576726640996539603
            exact RamareSaouter2003.prime_interval_nat_ladder_c08035 n (by omega) (by omega)
        · -- n <= 16529925481222116191
          rcases Nat.lt_or_ge 16436719164411425713 n with h10 | h10
          · -- n > 16436719164411425713
            rcases Nat.lt_or_ge 16483256367246992597 n with h12 | h12
            · -- n > 16483256367246992597
              exact RamareSaouter2003.prime_interval_nat_ladder_c08034 n (by omega) (by omega)
            · -- n <= 16483256367246992597
              exact RamareSaouter2003.prime_interval_nat_ladder_c08033 n (by omega) (by omega)
          · -- n <= 16436719164411425713
            exact RamareSaouter2003.prime_interval_nat_ladder_c08032 n (by omega) (by omega)
