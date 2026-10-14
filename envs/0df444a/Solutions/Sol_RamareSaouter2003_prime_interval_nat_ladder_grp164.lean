-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp164
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T12:52:47.290385+00:00
-- url     : https://prove2.me/submissions/a07dce97-6f5f-48bd-b1fe-80ba272802c3

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08150
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08178

theorem solution (n : Nat)
    (hn : 21161333045580742687 < n) (hupper : n <= 23850902211042336817) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 22438493584392514729 n with h2 | h2
  · -- n > 22438493584392514729
    rcases Nat.lt_or_ge 23105694261714938387 n with h4 | h4
    · -- n > 23105694261714938387
      rcases Nat.lt_or_ge 23446698095757141041 n with h6 | h6
      · -- n > 23446698095757141041
        rcases Nat.lt_or_ge 23619082602937326983 n with h8 | h8
        · -- n > 23619082602937326983
          rcases Nat.lt_or_ge 23734709426749773913 n with h10 | h10
          · -- n > 23734709426749773913
            rcases Nat.lt_or_ge 23792734902766655989 n with h12 | h12
            · -- n > 23792734902766655989
              exact RamareSaouter2003.prime_interval_nat_ladder_c08178 n (by omega) (by omega)
            · -- n <= 23792734902766655989
              exact RamareSaouter2003.prime_interval_nat_ladder_c08177 n (by omega) (by omega)
          · -- n <= 23734709426749773913
            rcases Nat.lt_or_ge 23676825435884612011 n with h12 | h12
            · -- n > 23676825435884612011
              exact RamareSaouter2003.prime_interval_nat_ladder_c08176 n (by omega) (by omega)
            · -- n <= 23676825435884612011
              exact RamareSaouter2003.prime_interval_nat_ladder_c08175 n (by omega) (by omega)
        · -- n <= 23619082602937326983
          rcases Nat.lt_or_ge 23504019331159063087 n with h10 | h10
          · -- n > 23504019331159063087
            rcases Nat.lt_or_ge 23561480612433936607 n with h12 | h12
            · -- n > 23561480612433936607
              exact RamareSaouter2003.prime_interval_nat_ladder_c08174 n (by omega) (by omega)
            · -- n <= 23561480612433936607
              exact RamareSaouter2003.prime_interval_nat_ladder_c08173 n (by omega) (by omega)
          · -- n <= 23504019331159063087
            exact RamareSaouter2003.prime_interval_nat_ladder_c08172 n (by omega) (by omega)
      · -- n <= 23446698095757141041
        rcases Nat.lt_or_ge 23275571617763918267 n with h8 | h8
        · -- n > 23275571617763918267
          rcases Nat.lt_or_ge 23332474581306038983 n with h10 | h10
          · -- n > 23332474581306038983
            rcases Nat.lt_or_ge 23389516678271005993 n with h12 | h12
            · -- n > 23389516678271005993
              exact RamareSaouter2003.prime_interval_nat_ladder_c08171 n (by omega) (by omega)
            · -- n <= 23389516678271005993
              exact RamareSaouter2003.prime_interval_nat_ladder_c08170 n (by omega) (by omega)
          · -- n <= 23332474581306038983
            exact RamareSaouter2003.prime_interval_nat_ladder_c08169 n (by omega) (by omega)
        · -- n <= 23275571617763918267
          rcases Nat.lt_or_ge 23162181851018170097 n with h10 | h10
          · -- n > 23162181851018170097
            rcases Nat.lt_or_ge 23218807561833578467 n with h12 | h12
            · -- n > 23218807561833578467
              exact RamareSaouter2003.prime_interval_nat_ladder_c08168 n (by omega) (by omega)
            · -- n <= 23218807561833578467
              exact RamareSaouter2003.prime_interval_nat_ladder_c08167 n (by omega) (by omega)
          · -- n <= 23162181851018170097
            exact RamareSaouter2003.prime_interval_nat_ladder_c08166 n (by omega) (by omega)
    · -- n <= 23105694261714938387
      rcases Nat.lt_or_ge 22769649946617498697 n with h6 | h6
      · -- n > 22769649946617498697
        rcases Nat.lt_or_ge 22937056916447370419 n with h8 | h8
        · -- n > 22937056916447370419
          rcases Nat.lt_or_ge 22993132367747395913 n with h10 | h10
          · -- n > 22993132367747395913
            rcases Nat.lt_or_ge 23049344876721580409 n with h12 | h12
            · -- n > 23049344876721580409
              exact RamareSaouter2003.prime_interval_nat_ladder_c08165 n (by omega) (by omega)
            · -- n <= 23049344876721580409
              exact RamareSaouter2003.prime_interval_nat_ladder_c08164 n (by omega) (by omega)
          · -- n <= 22993132367747395913
            exact RamareSaouter2003.prime_interval_nat_ladder_c08163 n (by omega) (by omega)
        · -- n <= 22937056916447370419
          rcases Nat.lt_or_ge 22825316109317696333 n with h10 | h10
          · -- n > 22825316109317696333
            rcases Nat.lt_or_ge 22881118224580977337 n with h12 | h12
            · -- n > 22881118224580977337
              exact RamareSaouter2003.prime_interval_nat_ladder_c08162 n (by omega) (by omega)
            · -- n <= 22881118224580977337
              exact RamareSaouter2003.prime_interval_nat_ladder_c08161 n (by omega) (by omega)
          · -- n <= 22825316109317696333
            exact RamareSaouter2003.prime_interval_nat_ladder_c08160 n (by omega) (by omega)
      · -- n <= 22769649946617498697
        rcases Nat.lt_or_ge 22603465570732118353 n with h8 | h8
        · -- n > 22603465570732118353
          rcases Nat.lt_or_ge 22658725288100024119 n with h10 | h10
          · -- n > 22658725288100024119
            rcases Nat.lt_or_ge 22714119536707596521 n with h12 | h12
            · -- n > 22714119536707596521
              exact RamareSaouter2003.prime_interval_nat_ladder_c08159 n (by omega) (by omega)
            · -- n <= 22714119536707596521
              exact RamareSaouter2003.prime_interval_nat_ladder_c08158 n (by omega) (by omega)
          · -- n <= 22658725288100024119
            exact RamareSaouter2003.prime_interval_nat_ladder_c08157 n (by omega) (by omega)
        · -- n <= 22603465570732118353
          rcases Nat.lt_or_ge 22493349889273544077 n with h10 | h10
          · -- n > 22493349889273544077
            rcases Nat.lt_or_ge 22548340490847788549 n with h12 | h12
            · -- n > 22548340490847788549
              exact RamareSaouter2003.prime_interval_nat_ladder_c08156 n (by omega) (by omega)
            · -- n <= 22548340490847788549
              exact RamareSaouter2003.prime_interval_nat_ladder_c08155 n (by omega) (by omega)
          · -- n <= 22493349889273544077
            exact RamareSaouter2003.prime_interval_nat_ladder_c08154 n (by omega) (by omega)
  · -- n <= 22438493584392514729
    rcases Nat.lt_or_ge 21790558776667921117 n with h4 | h4
    · -- n > 21790558776667921117
      rcases Nat.lt_or_ge 22112153204009560429 n with h6 | h6
      · -- n > 22112153204009560429
        rcases Nat.lt_or_ge 22274725830362389291 n with h8 | h8
        · -- n > 22274725830362389291
          rcases Nat.lt_or_ge 22329181548594738709 n with h10 | h10
          · -- n > 22329181548594738709
            rcases Nat.lt_or_ge 22383770790641627863 n with h12 | h12
            · -- n > 22383770790641627863
              exact RamareSaouter2003.prime_interval_nat_ladder_c08153 n (by omega) (by omega)
            · -- n <= 22383770790641627863
              exact RamareSaouter2003.prime_interval_nat_ladder_c08152 n (by omega) (by omega)
          · -- n <= 22329181548594738709
            exact RamareSaouter2003.prime_interval_nat_ladder_c08151 n (by omega) (by omega)
        · -- n <= 22274725830362389291
          rcases Nat.lt_or_ge 22166211914172313927 n with h10 | h10
          · -- n > 22166211914172313927
            rcases Nat.lt_or_ge 22220402683796165711 n with h12 | h12
            · -- n > 22220402683796165711
              exact RamareSaouter2003.prime_interval_nat_ladder_c08150 n (by omega) (by omega)
            · -- n <= 22220402683796165711
              exact RamareSaouter2003.prime_interval_nat_ladder_c08149 n (by omega) (by omega)
          · -- n <= 22166211914172313927
            exact RamareSaouter2003.prime_interval_nat_ladder_c08148 n (by omega) (by omega)
      · -- n <= 22112153204009560429
        rcases Nat.lt_or_ge 21950767070619409667 n with h8 | h8
        · -- n > 21950767070619409667
          rcases Nat.lt_or_ge 22004431220311813667 n with h10 | h10
          · -- n > 22004431220311813667
            rcases Nat.lt_or_ge 22058226611994091747 n with h12 | h12
            · -- n > 22058226611994091747
              exact RamareSaouter2003.prime_interval_nat_ladder_c08147 n (by omega) (by omega)
            · -- n <= 22058226611994091747
              exact RamareSaouter2003.prime_interval_nat_ladder_c08146 n (by omega) (by omega)
          · -- n <= 22004431220311813667
            exact RamareSaouter2003.prime_interval_nat_ladder_c08145 n (by omega) (by omega)
        · -- n <= 21950767070619409667
          rcases Nat.lt_or_ge 21843831200465490179 n with h10 | h10
          · -- n > 21843831200465490179
            rcases Nat.lt_or_ge 21897233782543108159 n with h12 | h12
            · -- n > 21897233782543108159
              exact RamareSaouter2003.prime_interval_nat_ladder_c08144 n (by omega) (by omega)
            · -- n <= 21897233782543108159
              exact RamareSaouter2003.prime_interval_nat_ladder_c08143 n (by omega) (by omega)
          · -- n <= 21843831200465490179
            exact RamareSaouter2003.prime_interval_nat_ladder_c08142 n (by omega) (by omega)
    · -- n <= 21790558776667921117
      rcases Nat.lt_or_ge 21473641239654392903 n with h6 | h6
      · -- n > 21473641239654392903
        rcases Nat.lt_or_ge 21631519547226063841 n with h8 | h8
        · -- n > 21631519547226063841
          rcases Nat.lt_or_ge 21684403211000465753 n with h10 | h10
          · -- n > 21684403211000465753
            rcases Nat.lt_or_ge 21737416226898252691 n with h12 | h12
            · -- n > 21737416226898252691
              exact RamareSaouter2003.prime_interval_nat_ladder_c08141 n (by omega) (by omega)
            · -- n <= 21737416226898252691
              exact RamareSaouter2003.prime_interval_nat_ladder_c08140 n (by omega) (by omega)
          · -- n <= 21684403211000465753
            exact RamareSaouter2003.prime_interval_nat_ladder_c08139 n (by omega) (by omega)
        · -- n <= 21631519547226063841
          rcases Nat.lt_or_ge 21526138959352300477 n with h10 | h10
          · -- n > 21526138959352300477
            rcases Nat.lt_or_ge 21578764971749266591 n with h12 | h12
            · -- n > 21578764971749266591
              exact RamareSaouter2003.prime_interval_nat_ladder_c08138 n (by omega) (by omega)
            · -- n <= 21578764971749266591
              exact RamareSaouter2003.prime_interval_nat_ladder_c08137 n (by omega) (by omega)
          · -- n <= 21526138959352300477
            exact RamareSaouter2003.prime_interval_nat_ladder_c08136 n (by omega) (by omega)
      · -- n <= 21473641239654392903
        rcases Nat.lt_or_ge 21316915325430167161 n with h8 | h8
        · -- n > 21316915325430167161
          rcases Nat.lt_or_ge 21369029799584757733 n with h10 | h10
          · -- n > 21369029799584757733
            rcases Nat.lt_or_ge 21421271650232475743 n with h12 | h12
            · -- n > 21421271650232475743
              exact RamareSaouter2003.prime_interval_nat_ladder_c08135 n (by omega) (by omega)
            · -- n <= 21421271650232475743
              exact RamareSaouter2003.prime_interval_nat_ladder_c08134 n (by omega) (by omega)
          · -- n <= 21369029799584757733
            exact RamareSaouter2003.prime_interval_nat_ladder_c08133 n (by omega) (by omega)
        · -- n <= 21316915325430167161
          rcases Nat.lt_or_ge 21213067268106842819 n with h10 | h10
          · -- n > 21213067268106842819
            rcases Nat.lt_or_ge 21264927854333614597 n with h12 | h12
            · -- n > 21264927854333614597
              exact RamareSaouter2003.prime_interval_nat_ladder_c08132 n (by omega) (by omega)
            · -- n <= 21264927854333614597
              exact RamareSaouter2003.prime_interval_nat_ladder_c08131 n (by omega) (by omega)
          · -- n <= 21213067268106842819
            exact RamareSaouter2003.prime_interval_nat_ladder_c08130 n (by omega) (by omega)
