-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp120
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T19:51:00.122993+00:00
-- url     : https://prove2.me/submissions/6bd5da4f-0767-4264-9213-8d1cc2dc10df

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05951
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05952
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05953
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05954
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05955
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05956
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05957
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05958
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05959
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05960
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05961
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05962
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05963
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05964
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05965
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05966
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05967
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05968
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05969
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05970
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05971
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05972
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05973
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05974
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05975
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05976
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05977
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05978
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05979
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05980
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05981
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05982
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05983
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05984
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05985
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05986
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05987
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05988
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05989
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05990
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05991
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05992
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05993
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05994
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05995
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05996
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05997
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05998
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05999
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06000

theorem solution (n : Nat)
    (hn : 45647159062049219 < n) (hupper : n <= 52577951070072157) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 48990174618878459 n with h2 | h2
  · -- n > 48990174618878459
    rcases Nat.lt_or_ge 50680689030056167 n with h4 | h4
    · -- n > 50680689030056167
      rcases Nat.lt_or_ge 51547710187723391 n with h6 | h6
      · -- n > 51547710187723391
        rcases Nat.lt_or_ge 51986731472004001 n with h8 | h8
        · -- n > 51986731472004001
          rcases Nat.lt_or_ge 52281523516584163 n with h10 | h10
          · -- n > 52281523516584163
            rcases Nat.lt_or_ge 52429527668252957 n with h12 | h12
            · -- n > 52429527668252957
              exact RamareSaouter2003.prime_interval_nat_ladder_c06000 n (by omega) (by omega)
            · -- n <= 52429527668252957
              exact RamareSaouter2003.prime_interval_nat_ladder_c05999 n (by omega) (by omega)
          · -- n <= 52281523516584163
            rcases Nat.lt_or_ge 52133917137639367 n with h12 | h12
            · -- n > 52133917137639367
              exact RamareSaouter2003.prime_interval_nat_ladder_c05998 n (by omega) (by omega)
            · -- n <= 52133917137639367
              exact RamareSaouter2003.prime_interval_nat_ladder_c05997 n (by omega) (by omega)
        · -- n <= 51986731472004001
          rcases Nat.lt_or_ge 51693643237939799 n with h10 | h10
          · -- n > 51693643237939799
            rcases Nat.lt_or_ge 51839976535395683 n with h12 | h12
            · -- n > 51839976535395683
              exact RamareSaouter2003.prime_interval_nat_ladder_c05996 n (by omega) (by omega)
            · -- n <= 51839976535395683
              exact RamareSaouter2003.prime_interval_nat_ladder_c05995 n (by omega) (by omega)
          · -- n <= 51693643237939799
            exact RamareSaouter2003.prime_interval_nat_ladder_c05994 n (by omega) (by omega)
      · -- n <= 51547710187723391
        rcases Nat.lt_or_ge 51112347379822541 n with h8 | h8
        · -- n > 51112347379822541
          rcases Nat.lt_or_ge 51257061522238177 n with h10 | h10
          · -- n > 51257061522238177
            rcases Nat.lt_or_ge 51402182026563013 n with h12 | h12
            · -- n > 51402182026563013
              exact RamareSaouter2003.prime_interval_nat_ladder_c05993 n (by omega) (by omega)
            · -- n <= 51402182026563013
              exact RamareSaouter2003.prime_interval_nat_ladder_c05992 n (by omega) (by omega)
          · -- n <= 51257061522238177
            exact RamareSaouter2003.prime_interval_nat_ladder_c05991 n (by omega) (by omega)
        · -- n <= 51112347379822541
          rcases Nat.lt_or_ge 50824160876346113 n with h10 | h10
          · -- n > 50824160876346113
            rcases Nat.lt_or_ge 50968049562026897 n with h12 | h12
            · -- n > 50968049562026897
              exact RamareSaouter2003.prime_interval_nat_ladder_c05990 n (by omega) (by omega)
            · -- n <= 50968049562026897
              exact RamareSaouter2003.prime_interval_nat_ladder_c05989 n (by omega) (by omega)
          · -- n <= 50824160876346113
            exact RamareSaouter2003.prime_interval_nat_ladder_c05988 n (by omega) (by omega)
    · -- n <= 50680689030056167
      rcases Nat.lt_or_ge 49828282537902301 n with h6 | h6
      · -- n > 49828282537902301
        rcases Nat.lt_or_ge 50252659860809981 n with h8 | h8
        · -- n > 50252659860809981
          rcases Nat.lt_or_ge 50394924297009931 n with h10 | h10
          · -- n > 50394924297009931
            rcases Nat.lt_or_ge 50537601585282509 n with h12 | h12
            · -- n > 50537601585282509
              exact RamareSaouter2003.prime_interval_nat_ladder_c05987 n (by omega) (by omega)
            · -- n <= 50537601585282509
              exact RamareSaouter2003.prime_interval_nat_ladder_c05986 n (by omega) (by omega)
          · -- n <= 50394924297009931
            exact RamareSaouter2003.prime_interval_nat_ladder_c05985 n (by omega) (by omega)
        · -- n <= 50252659860809981
          rcases Nat.lt_or_ge 49969351251746347 n with h10 | h10
          · -- n > 49969351251746347
            rcases Nat.lt_or_ge 50110822626898829 n with h12 | h12
            · -- n > 50110822626898829
              exact RamareSaouter2003.prime_interval_nat_ladder_c05984 n (by omega) (by omega)
            · -- n <= 50110822626898829
              exact RamareSaouter2003.prime_interval_nat_ladder_c05983 n (by omega) (by omega)
          · -- n <= 49969351251746347
            exact RamareSaouter2003.prime_interval_nat_ladder_c05982 n (by omega) (by omega)
      · -- n <= 49828282537902301
        rcases Nat.lt_or_ge 49407465570805301 n with h8 | h8
        · -- n > 49407465570805301
          rcases Nat.lt_or_ge 49547349690578717 n with h10 | h10
          · -- n > 49547349690578717
            rcases Nat.lt_or_ge 49687613854043441 n with h12 | h12
            · -- n > 49687613854043441
              exact RamareSaouter2003.prime_interval_nat_ladder_c05981 n (by omega) (by omega)
            · -- n <= 49687613854043441
              exact RamareSaouter2003.prime_interval_nat_ladder_c05980 n (by omega) (by omega)
          · -- n <= 49547349690578717
            exact RamareSaouter2003.prime_interval_nat_ladder_c05979 n (by omega) (by omega)
        · -- n <= 49407465570805301
          rcases Nat.lt_or_ge 49128875788624781 n with h10 | h10
          · -- n > 49128875788624781
            rcases Nat.lt_or_ge 49267974124117741 n with h12 | h12
            · -- n > 49267974124117741
              exact RamareSaouter2003.prime_interval_nat_ladder_c05978 n (by omega) (by omega)
            · -- n <= 49267974124117741
              exact RamareSaouter2003.prime_interval_nat_ladder_c05977 n (by omega) (by omega)
          · -- n <= 49128875788624781
            exact RamareSaouter2003.prime_interval_nat_ladder_c05976 n (by omega) (by omega)
  · -- n <= 48990174618878459
    rcases Nat.lt_or_ge 47222349787253777 n with h4 | h4
    · -- n > 47222349787253777
      rcases Nat.lt_or_ge 48030184309685159 n with h6 | h6
      · -- n > 48030184309685159
        rcases Nat.lt_or_ge 48439292053216609 n with h8 | h8
        · -- n > 48439292053216609
          rcases Nat.lt_or_ge 48713966995850459 n with h10 | h10
          · -- n > 48713966995850459
            rcases Nat.lt_or_ge 48851888341873579 n with h12 | h12
            · -- n > 48851888341873579
              exact RamareSaouter2003.prime_interval_nat_ladder_c05975 n (by omega) (by omega)
            · -- n <= 48851888341873579
              exact RamareSaouter2003.prime_interval_nat_ladder_c05974 n (by omega) (by omega)
          · -- n <= 48713966995850459
            rcases Nat.lt_or_ge 48576436810595501 n with h12 | h12
            · -- n > 48576436810595501
              exact RamareSaouter2003.prime_interval_nat_ladder_c05973 n (by omega) (by omega)
            · -- n <= 48576436810595501
              exact RamareSaouter2003.prime_interval_nat_ladder_c05972 n (by omega) (by omega)
        · -- n <= 48439292053216609
          rcases Nat.lt_or_ge 48166165750983607 n with h10 | h10
          · -- n > 48166165750983607
            rcases Nat.lt_or_ge 48302537215437041 n with h12 | h12
            · -- n > 48302537215437041
              exact RamareSaouter2003.prime_interval_nat_ladder_c05971 n (by omega) (by omega)
            · -- n <= 48302537215437041
              exact RamareSaouter2003.prime_interval_nat_ladder_c05970 n (by omega) (by omega)
          · -- n <= 48166165750983607
            exact RamareSaouter2003.prime_interval_nat_ladder_c05969 n (by omega) (by omega)
      · -- n <= 48030184309685159
        rcases Nat.lt_or_ge 47624543364762569 n with h8 | h8
        · -- n > 47624543364762569
          rcases Nat.lt_or_ge 47759371087108327 n with h10 | h10
          · -- n > 47759371087108327
            rcases Nat.lt_or_ge 47894587235230157 n with h12 | h12
            · -- n > 47894587235230157
              exact RamareSaouter2003.prime_interval_nat_ladder_c05968 n (by omega) (by omega)
            · -- n <= 47894587235230157
              exact RamareSaouter2003.prime_interval_nat_ladder_c05967 n (by omega) (by omega)
          · -- n <= 47759371087108327
            exact RamareSaouter2003.prime_interval_nat_ladder_c05966 n (by omega) (by omega)
        · -- n <= 47624543364762569
          rcases Nat.lt_or_ge 47356043327294809 n with h10 | h10
          · -- n > 47356043327294809
            rcases Nat.lt_or_ge 47490107147715917 n with h12 | h12
            · -- n > 47490107147715917
              exact RamareSaouter2003.prime_interval_nat_ladder_c05965 n (by omega) (by omega)
            · -- n <= 47490107147715917
              exact RamareSaouter2003.prime_interval_nat_ladder_c05964 n (by omega) (by omega)
          · -- n <= 47356043327294809
            exact RamareSaouter2003.prime_interval_nat_ladder_c05963 n (by omega) (by omega)
    · -- n <= 47222349787253777
      rcases Nat.lt_or_ge 46428053317184683 n with h6 | h6
      · -- n > 46428053317184683
        rcases Nat.lt_or_ge 46823519194527539 n with h8 | h8
        · -- n > 46823519194527539
          rcases Nat.lt_or_ge 46956087854639903 n with h10 | h10
          · -- n > 46956087854639903
            rcases Nat.lt_or_ge 47089030975783183 n with h12 | h12
            · -- n > 47089030975783183
              exact RamareSaouter2003.prime_interval_nat_ladder_c05962 n (by omega) (by omega)
            · -- n <= 47089030975783183
              exact RamareSaouter2003.prime_interval_nat_ladder_c05961 n (by omega) (by omega)
          · -- n <= 46956087854639903
            exact RamareSaouter2003.prime_interval_nat_ladder_c05960 n (by omega) (by omega)
        · -- n <= 46823519194527539
          rcases Nat.lt_or_ge 46559504231049353 n with h10 | h10
          · -- n > 46559504231049353
            rcases Nat.lt_or_ge 46691324199942181 n with h12 | h12
            · -- n > 46691324199942181
              exact RamareSaouter2003.prime_interval_nat_ladder_c05959 n (by omega) (by omega)
            · -- n <= 46691324199942181
              exact RamareSaouter2003.prime_interval_nat_ladder_c05958 n (by omega) (by omega)
          · -- n <= 46559504231049353
            exact RamareSaouter2003.prime_interval_nat_ladder_c05957 n (by omega) (by omega)
      · -- n <= 46428053317184683
        rcases Nat.lt_or_ge 46035954849072271 n with h8 | h8
        · -- n > 46035954849072271
          rcases Nat.lt_or_ge 46166267600448683 n with h10 | h10
          · -- n > 46166267600448683
            rcases Nat.lt_or_ge 46296976726111091 n with h12 | h12
            · -- n > 46296976726111091
              exact RamareSaouter2003.prime_interval_nat_ladder_c05956 n (by omega) (by omega)
            · -- n <= 46296976726111091
              exact RamareSaouter2003.prime_interval_nat_ladder_c05955 n (by omega) (by omega)
          · -- n <= 46166267600448683
            exact RamareSaouter2003.prime_interval_nat_ladder_c05954 n (by omega) (by omega)
        · -- n <= 46035954849072271
          rcases Nat.lt_or_ge 45776383750572359 n with h10 | h10
          · -- n > 45776383750572359
            rcases Nat.lt_or_ge 45905987804844491 n with h12 | h12
            · -- n > 45905987804844491
              exact RamareSaouter2003.prime_interval_nat_ladder_c05953 n (by omega) (by omega)
            · -- n <= 45905987804844491
              exact RamareSaouter2003.prime_interval_nat_ladder_c05952 n (by omega) (by omega)
          · -- n <= 45776383750572359
            exact RamareSaouter2003.prime_interval_nat_ladder_c05951 n (by omega) (by omega)
