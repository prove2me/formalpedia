-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp102
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T14:31:51.614466+00:00
-- url     : https://prove2.me/submissions/99cdbb9d-5bd3-4717-accb-0cb9e2be87da

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05100

theorem solution (n : Nat)
    (hn : 3584629562138893 < n) (hupper : n <= 4128840276810539) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 3847121185123453 n with h2 | h2
  · -- n > 3847121185123453
    rcases Nat.lt_or_ge 3979869085925581 n with h4 | h4
    · -- n > 3979869085925581
      rcases Nat.lt_or_ge 4047943962847007 n with h6 | h6
      · -- n > 4047943962847007
        rcases Nat.lt_or_ge 4082416593520039 n with h8 | h8
        · -- n > 4082416593520039
          rcases Nat.lt_or_ge 4105561861005167 n with h10 | h10
          · -- n > 4105561861005167
            rcases Nat.lt_or_ge 4117184500638331 n with h12 | h12
            · -- n > 4117184500638331
              exact RamareSaouter2003.prime_interval_nat_ladder_c05100 n (by omega) (by omega)
            · -- n <= 4117184500638331
              exact RamareSaouter2003.prime_interval_nat_ladder_c05099 n (by omega) (by omega)
          · -- n <= 4105561861005167
            rcases Nat.lt_or_ge 4093971640904449 n with h12 | h12
            · -- n > 4093971640904449
              exact RamareSaouter2003.prime_interval_nat_ladder_c05098 n (by omega) (by omega)
            · -- n <= 4093971640904449
              exact RamareSaouter2003.prime_interval_nat_ladder_c05097 n (by omega) (by omega)
        · -- n <= 4082416593520039
          rcases Nat.lt_or_ge 4059403141868923 n with h10 | h10
          · -- n > 4059403141868923
            rcases Nat.lt_or_ge 4070893182821111 n with h12 | h12
            · -- n > 4070893182821111
              exact RamareSaouter2003.prime_interval_nat_ladder_c05096 n (by omega) (by omega)
            · -- n <= 4070893182821111
              exact RamareSaouter2003.prime_interval_nat_ladder_c05095 n (by omega) (by omega)
          · -- n <= 4059403141868923
            exact RamareSaouter2003.prime_interval_nat_ladder_c05094 n (by omega) (by omega)
      · -- n <= 4047943962847007
        rcases Nat.lt_or_ge 4013767782681803 n with h8 | h8
        · -- n > 4013767782681803
          rcases Nat.lt_or_ge 4025129775460943 n with h10 | h10
          · -- n > 4025129775460943
            rcases Nat.lt_or_ge 4036523227841011 n with h12 | h12
            · -- n > 4036523227841011
              exact RamareSaouter2003.prime_interval_nat_ladder_c05093 n (by omega) (by omega)
            · -- n <= 4036523227841011
              exact RamareSaouter2003.prime_interval_nat_ladder_c05092 n (by omega) (by omega)
          · -- n <= 4025129775460943
            exact RamareSaouter2003.prime_interval_nat_ladder_c05091 n (by omega) (by omega)
        · -- n <= 4013767782681803
          rcases Nat.lt_or_ge 3991137178724851 n with h10 | h10
          · -- n > 3991137178724851
            rcases Nat.lt_or_ge 4002436006290143 n with h12 | h12
            · -- n > 4002436006290143
              exact RamareSaouter2003.prime_interval_nat_ladder_c05090 n (by omega) (by omega)
            · -- n <= 4002436006290143
              exact RamareSaouter2003.prime_interval_nat_ladder_c05089 n (by omega) (by omega)
          · -- n <= 3991137178724851
            exact RamareSaouter2003.prime_interval_nat_ladder_c05088 n (by omega) (by omega)
    · -- n <= 3979869085925581
      rcases Nat.lt_or_ge 3912932688555707 n with h6 | h6
      · -- n > 3912932688555707
        rcases Nat.lt_or_ge 3946258252372817 n with h8 | h8
        · -- n > 3946258252372817
          rcases Nat.lt_or_ge 3957431264097769 n with h10 | h10
          · -- n > 3957431264097769
            rcases Nat.lt_or_ge 3968634308151391 n with h12 | h12
            · -- n > 3968634308151391
              exact RamareSaouter2003.prime_interval_nat_ladder_c05087 n (by omega) (by omega)
            · -- n <= 3968634308151391
              exact RamareSaouter2003.prime_interval_nat_ladder_c05086 n (by omega) (by omega)
          · -- n <= 3957431264097769
            exact RamareSaouter2003.prime_interval_nat_ladder_c05085 n (by omega) (by omega)
        · -- n <= 3946258252372817
          rcases Nat.lt_or_ge 3924008340007843 n with h10 | h10
          · -- n > 3924008340007843
            rcases Nat.lt_or_ge 3935117092694351 n with h12 | h12
            · -- n > 3935117092694351
              exact RamareSaouter2003.prime_interval_nat_ladder_c05084 n (by omega) (by omega)
            · -- n <= 3935117092694351
              exact RamareSaouter2003.prime_interval_nat_ladder_c05083 n (by omega) (by omega)
          · -- n <= 3924008340007843
            exact RamareSaouter2003.prime_interval_nat_ladder_c05082 n (by omega) (by omega)
      · -- n <= 3912932688555707
        rcases Nat.lt_or_ge 3879886719910889 n with h8 | h8
        · -- n > 3879886719910889
          rcases Nat.lt_or_ge 3890871753612881 n with h10 | h10
          · -- n > 3890871753612881
            rcases Nat.lt_or_ge 3901887304785473 n with h12 | h12
            · -- n > 3901887304785473
              exact RamareSaouter2003.prime_interval_nat_ladder_c05081 n (by omega) (by omega)
            · -- n <= 3901887304785473
              exact RamareSaouter2003.prime_interval_nat_ladder_c05080 n (by omega) (by omega)
          · -- n <= 3890871753612881
            exact RamareSaouter2003.prime_interval_nat_ladder_c05079 n (by omega) (by omega)
        · -- n <= 3879886719910889
          rcases Nat.lt_or_ge 3858013307590279 n with h10 | h10
          · -- n > 3858013307590279
            rcases Nat.lt_or_ge 3868935878640557 n with h12 | h12
            · -- n > 3868935878640557
              exact RamareSaouter2003.prime_interval_nat_ladder_c05078 n (by omega) (by omega)
            · -- n <= 3868935878640557
              exact RamareSaouter2003.prime_interval_nat_ladder_c05077 n (by omega) (by omega)
          · -- n <= 3858013307590279
            exact RamareSaouter2003.prime_interval_nat_ladder_c05076 n (by omega) (by omega)
  · -- n <= 3847121185123453
    rcases Nat.lt_or_ge 3708315128217589 n with h4 | h4
    · -- n > 3708315128217589
      rcases Nat.lt_or_ge 3771748648840933 n with h6 | h6
      · -- n > 3771748648840933
        rcases Nat.lt_or_ge 3803869988030611 n with h8 | h8
        · -- n > 3803869988030611
          rcases Nat.lt_or_ge 3825436449416119 n with h10 | h10
          · -- n > 3825436449416119
            rcases Nat.lt_or_ge 3836262048858523 n with h12 | h12
            · -- n > 3836262048858523
              exact RamareSaouter2003.prime_interval_nat_ladder_c05075 n (by omega) (by omega)
            · -- n <= 3836262048858523
              exact RamareSaouter2003.prime_interval_nat_ladder_c05074 n (by omega) (by omega)
          · -- n <= 3825436449416119
            rcases Nat.lt_or_ge 3814637754191773 n with h12 | h12
            · -- n > 3814637754191773
              exact RamareSaouter2003.prime_interval_nat_ladder_c05073 n (by omega) (by omega)
            · -- n <= 3814637754191773
              exact RamareSaouter2003.prime_interval_nat_ladder_c05072 n (by omega) (by omega)
        · -- n <= 3803869988030611
          rcases Nat.lt_or_ge 3782423281479967 n with h10 | h10
          · -- n > 3782423281479967
            rcases Nat.lt_or_ge 3793131724767893 n with h12 | h12
            · -- n > 3793131724767893
              exact RamareSaouter2003.prime_interval_nat_ladder_c05071 n (by omega) (by omega)
            · -- n <= 3793131724767893
              exact RamareSaouter2003.prime_interval_nat_ladder_c05070 n (by omega) (by omega)
          · -- n <= 3782423281479967
            exact RamareSaouter2003.prime_interval_nat_ladder_c05069 n (by omega) (by omega)
      · -- n <= 3771748648840933
        rcases Nat.lt_or_ge 3739899025657943 n with h8 | h8
        · -- n > 3739899025657943
          rcases Nat.lt_or_ge 3750487130574193 n with h10 | h10
          · -- n > 3750487130574193
            rcases Nat.lt_or_ge 3761100742435121 n with h12 | h12
            · -- n > 3761100742435121
              exact RamareSaouter2003.prime_interval_nat_ladder_c05068 n (by omega) (by omega)
            · -- n <= 3761100742435121
              exact RamareSaouter2003.prime_interval_nat_ladder_c05067 n (by omega) (by omega)
          · -- n <= 3750487130574193
            exact RamareSaouter2003.prime_interval_nat_ladder_c05066 n (by omega) (by omega)
        · -- n <= 3739899025657943
          rcases Nat.lt_or_ge 3718814307613519 n with h10 | h10
          · -- n > 3718814307613519
            rcases Nat.lt_or_ge 3729341031249527 n with h12 | h12
            · -- n > 3729341031249527
              exact RamareSaouter2003.prime_interval_nat_ladder_c05065 n (by omega) (by omega)
            · -- n <= 3729341031249527
              exact RamareSaouter2003.prime_interval_nat_ladder_c05064 n (by omega) (by omega)
          · -- n <= 3718814307613519
            exact RamareSaouter2003.prime_interval_nat_ladder_c05063 n (by omega) (by omega)
    · -- n <= 3708315128217589
      rcases Nat.lt_or_ge 3645947633996489 n with h6 | h6
      · -- n > 3645947633996489
        rcases Nat.lt_or_ge 3676999291361563 n with h8 | h8
        · -- n > 3676999291361563
          rcases Nat.lt_or_ge 3687407564369719 n with h10 | h10
          · -- n > 3687407564369719
            rcases Nat.lt_or_ge 3697846112387081 n with h12 | h12
            · -- n > 3697846112387081
              exact RamareSaouter2003.prime_interval_nat_ladder_c05062 n (by omega) (by omega)
            · -- n <= 3697846112387081
              exact RamareSaouter2003.prime_interval_nat_ladder_c05061 n (by omega) (by omega)
          · -- n <= 3687407564369719
            exact RamareSaouter2003.prime_interval_nat_ladder_c05060 n (by omega) (by omega)
        · -- n <= 3676999291361563
          rcases Nat.lt_or_ge 3656270291745601 n with h10 | h10
          · -- n > 3656270291745601
            rcases Nat.lt_or_ge 3666621473355443 n with h12 | h12
            · -- n > 3666621473355443
              exact RamareSaouter2003.prime_interval_nat_ladder_c05059 n (by omega) (by omega)
            · -- n <= 3666621473355443
              exact RamareSaouter2003.prime_interval_nat_ladder_c05058 n (by omega) (by omega)
          · -- n <= 3656270291745601
            exact RamareSaouter2003.prime_interval_nat_ladder_c05057 n (by omega) (by omega)
      · -- n <= 3645947633996489
        rcases Nat.lt_or_ge 3615159443990333 n with h8 | h8
        · -- n > 3615159443990333
          rcases Nat.lt_or_ge 3625391610719317 n with h10 | h10
          · -- n > 3625391610719317
            rcases Nat.lt_or_ge 3635656090081669 n with h12 | h12
            · -- n > 3635656090081669
              exact RamareSaouter2003.prime_interval_nat_ladder_c05056 n (by omega) (by omega)
            · -- n <= 3635656090081669
              exact RamareSaouter2003.prime_interval_nat_ladder_c05055 n (by omega) (by omega)
          · -- n <= 3625391610719317
            exact RamareSaouter2003.prime_interval_nat_ladder_c05054 n (by omega) (by omega)
        · -- n <= 3615159443990333
          rcases Nat.lt_or_ge 3594776614256453 n with h10 | h10
          · -- n > 3594776614256453
            rcases Nat.lt_or_ge 3604953021258163 n with h12 | h12
            · -- n > 3604953021258163
              exact RamareSaouter2003.prime_interval_nat_ladder_c05053 n (by omega) (by omega)
            · -- n <= 3604953021258163
              exact RamareSaouter2003.prime_interval_nat_ladder_c05052 n (by omega) (by omega)
          · -- n <= 3594776614256453
            exact RamareSaouter2003.prime_interval_nat_ladder_c05051 n (by omega) (by omega)
