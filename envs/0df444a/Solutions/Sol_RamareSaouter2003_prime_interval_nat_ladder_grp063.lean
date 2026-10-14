-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp063
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T02:35:10.790136+00:00
-- url     : https://prove2.me/submissions/bec2a3d1-a30d-4b00-bd5e-c739247dde83

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03150

theorem solution (n : Nat)
    (hn : 19429088181631 < n) (hupper : n <= 21984887510237) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 20667518430761 n with h2 | h2
  · -- n > 20667518430761
    rcases Nat.lt_or_ge 21289701505837 n with h4 | h4
    · -- n > 21289701505837
      rcases Nat.lt_or_ge 21607782109811 n with h6 | h6
      · -- n > 21607782109811
        rcases Nat.lt_or_ge 21768600115303 n with h8 | h8
        · -- n > 21768600115303
          rcases Nat.lt_or_ge 21876476516863 n with h10 | h10
          · -- n > 21876476516863
            rcases Nat.lt_or_ge 21930615024299 n with h12 | h12
            · -- n > 21930615024299
              exact RamareSaouter2003.prime_interval_nat_ladder_c03150 n (by omega) (by omega)
            · -- n <= 21930615024299
              exact RamareSaouter2003.prime_interval_nat_ladder_c03149 n (by omega) (by omega)
          · -- n <= 21876476516863
            rcases Nat.lt_or_ge 21822471657187 n with h12 | h12
            · -- n > 21822471657187
              exact RamareSaouter2003.prime_interval_nat_ladder_c03148 n (by omega) (by omega)
            · -- n <= 21822471657187
              exact RamareSaouter2003.prime_interval_nat_ladder_c03147 n (by omega) (by omega)
        · -- n <= 21768600115303
          rcases Nat.lt_or_ge 21661255669531 n with h10 | h10
          · -- n > 21661255669531
            rcases Nat.lt_or_ge 21714861562193 n with h12 | h12
            · -- n > 21714861562193
              exact RamareSaouter2003.prime_interval_nat_ladder_c03146 n (by omega) (by omega)
            · -- n <= 21714861562193
              exact RamareSaouter2003.prime_interval_nat_ladder_c03145 n (by omega) (by omega)
          · -- n <= 21661255669531
            exact RamareSaouter2003.prime_interval_nat_ladder_c03144 n (by omega) (by omega)
      · -- n <= 21607782109811
        rcases Nat.lt_or_ge 21448152165763 n with h8 | h8
        · -- n > 21448152165763
          rcases Nat.lt_or_ge 21501230683423 n with h10 | h10
          · -- n > 21501230683423
            rcases Nat.lt_or_ge 21554440556437 n with h12 | h12
            · -- n > 21554440556437
              exact RamareSaouter2003.prime_interval_nat_ladder_c03143 n (by omega) (by omega)
            · -- n <= 21554440556437
              exact RamareSaouter2003.prime_interval_nat_ladder_c03142 n (by omega) (by omega)
          · -- n <= 21501230683423
            exact RamareSaouter2003.prime_interval_nat_ladder_c03141 n (by omega) (by omega)
        · -- n <= 21448152165763
          rcases Nat.lt_or_ge 21342387899999 n with h10 | h10
          · -- n > 21342387899999
            rcases Nat.lt_or_ge 21395204679061 n with h12 | h12
            · -- n > 21395204679061
              exact RamareSaouter2003.prime_interval_nat_ladder_c03140 n (by omega) (by omega)
            · -- n <= 21395204679061
              exact RamareSaouter2003.prime_interval_nat_ladder_c03139 n (by omega) (by omega)
          · -- n <= 21342387899999
            exact RamareSaouter2003.prime_interval_nat_ladder_c03138 n (by omega) (by omega)
    · -- n <= 21289701505837
      rcases Nat.lt_or_ge 20976303255433 n with h6 | h6
      · -- n > 20976303255433
        rcases Nat.lt_or_ge 21132421418393 n with h8 | h8
        · -- n > 21132421418393
          rcases Nat.lt_or_ge 21184718585773 n with h10 | h10
          · -- n > 21184718585773
            rcases Nat.lt_or_ge 21237145174877 n with h12 | h12
            · -- n > 21237145174877
              exact RamareSaouter2003.prime_interval_nat_ladder_c03137 n (by omega) (by omega)
            · -- n <= 21237145174877
              exact RamareSaouter2003.prime_interval_nat_ladder_c03136 n (by omega) (by omega)
          · -- n <= 21184718585773
            exact RamareSaouter2003.prime_interval_nat_ladder_c03135 n (by omega) (by omega)
        · -- n <= 21132421418393
          rcases Nat.lt_or_ge 21028214071489 n with h10 | h10
          · -- n > 21028214071489
            rcases Nat.lt_or_ge 21080253353219 n with h12 | h12
            · -- n > 21080253353219
              exact RamareSaouter2003.prime_interval_nat_ladder_c03134 n (by omega) (by omega)
            · -- n <= 21080253353219
              exact RamareSaouter2003.prime_interval_nat_ladder_c03133 n (by omega) (by omega)
          · -- n <= 21028214071489
            exact RamareSaouter2003.prime_interval_nat_ladder_c03132 n (by omega) (by omega)
      · -- n <= 20976303255433
        rcases Nat.lt_or_ge 20821338432931 n with h8 | h8
        · -- n > 20821338432931
          rcases Nat.lt_or_ge 20872865752073 n with h10 | h10
          · -- n > 20872865752073
            rcases Nat.lt_or_ge 20924520587681 n with h12 | h12
            · -- n > 20924520587681
              exact RamareSaouter2003.prime_interval_nat_ladder_c03131 n (by omega) (by omega)
            · -- n <= 20924520587681
              exact RamareSaouter2003.prime_interval_nat_ladder_c03130 n (by omega) (by omega)
          · -- n <= 20872865752073
            exact RamareSaouter2003.prime_interval_nat_ladder_c03129 n (by omega) (by omega)
        · -- n <= 20821338432931
          rcases Nat.lt_or_ge 20718665085977 n with h10 | h10
          · -- n > 20718665085977
            rcases Nat.lt_or_ge 20769938315509 n with h12 | h12
            · -- n > 20769938315509
              exact RamareSaouter2003.prime_interval_nat_ladder_c03128 n (by omega) (by omega)
            · -- n <= 20769938315509
              exact RamareSaouter2003.prime_interval_nat_ladder_c03127 n (by omega) (by omega)
          · -- n <= 20718665085977
            exact RamareSaouter2003.prime_interval_nat_ladder_c03126 n (by omega) (by omega)
  · -- n <= 20667518430761
    rcases Nat.lt_or_ge 20013989066821 n with h4 | h4
    · -- n > 20013989066821
      rcases Nat.lt_or_ge 20313009779861 n with h6 | h6
      · -- n > 20313009779861
        rcases Nat.lt_or_ge 20464191317111 n with h8 | h8
        · -- n > 20464191317111
          rcases Nat.lt_or_ge 20565603594817 n with h10 | h10
          · -- n > 20565603594817
            rcases Nat.lt_or_ge 20616498037547 n with h12 | h12
            · -- n > 20616498037547
              exact RamareSaouter2003.prime_interval_nat_ladder_c03125 n (by omega) (by omega)
            · -- n <= 20616498037547
              exact RamareSaouter2003.prime_interval_nat_ladder_c03124 n (by omega) (by omega)
          · -- n <= 20565603594817
            rcases Nat.lt_or_ge 20514834791377 n with h12 | h12
            · -- n > 20514834791377
              exact RamareSaouter2003.prime_interval_nat_ladder_c03123 n (by omega) (by omega)
            · -- n <= 20514834791377
              exact RamareSaouter2003.prime_interval_nat_ladder_c03122 n (by omega) (by omega)
        · -- n <= 20464191317111
          rcases Nat.lt_or_ge 20363279119639 n with h10 | h10
          · -- n > 20363279119639
            rcases Nat.lt_or_ge 20413672862753 n with h12 | h12
            · -- n > 20413672862753
              exact RamareSaouter2003.prime_interval_nat_ladder_c03121 n (by omega) (by omega)
            · -- n <= 20413672862753
              exact RamareSaouter2003.prime_interval_nat_ladder_c03120 n (by omega) (by omega)
          · -- n <= 20363279119639
            exact RamareSaouter2003.prime_interval_nat_ladder_c03119 n (by omega) (by omega)
      · -- n <= 20313009779861
        rcases Nat.lt_or_ge 20162945113217 n with h8 | h8
        · -- n > 20162945113217
          rcases Nat.lt_or_ge 20212843082587 n with h10 | h10
          · -- n > 20212843082587
            rcases Nat.lt_or_ge 20262864536287 n with h12 | h12
            · -- n > 20262864536287
              exact RamareSaouter2003.prime_interval_nat_ladder_c03118 n (by omega) (by omega)
            · -- n <= 20262864536287
              exact RamareSaouter2003.prime_interval_nat_ladder_c03117 n (by omega) (by omega)
          · -- n <= 20212843082587
            exact RamareSaouter2003.prime_interval_nat_ladder_c03116 n (by omega) (by omega)
        · -- n <= 20162945113217
          rcases Nat.lt_or_ge 20063518409219 n with h10 | h10
          · -- n > 20063518409219
            rcases Nat.lt_or_ge 20113170323387 n with h12 | h12
            · -- n > 20113170323387
              exact RamareSaouter2003.prime_interval_nat_ladder_c03115 n (by omega) (by omega)
            · -- n <= 20113170323387
              exact RamareSaouter2003.prime_interval_nat_ladder_c03114 n (by omega) (by omega)
          · -- n <= 20063518409219
            exact RamareSaouter2003.prime_interval_nat_ladder_c03113 n (by omega) (by omega)
    · -- n <= 20013989066821
      rcases Nat.lt_or_ge 19719370132981 n with h6 | h6
      · -- n > 19719370132981
        rcases Nat.lt_or_ge 19866133449671 n with h8 | h8
        · -- n > 19866133449671
          rcases Nat.lt_or_ge 19915296888479 n with h10 | h10
          · -- n > 19915296888479
            rcases Nat.lt_or_ge 19964581993831 n with h12 | h12
            · -- n > 19964581993831
              exact RamareSaouter2003.prime_interval_nat_ladder_c03112 n (by omega) (by omega)
            · -- n <= 19964581993831
              exact RamareSaouter2003.prime_interval_nat_ladder_c03111 n (by omega) (by omega)
          · -- n <= 19915296888479
            exact RamareSaouter2003.prime_interval_nat_ladder_c03110 n (by omega) (by omega)
        · -- n <= 19866133449671
          rcases Nat.lt_or_ge 19768170371281 n with h10 | h10
          · -- n > 19768170371281
            rcases Nat.lt_or_ge 19817091377311 n with h12 | h12
            · -- n > 19817091377311
              exact RamareSaouter2003.prime_interval_nat_ladder_c03109 n (by omega) (by omega)
            · -- n <= 19817091377311
              exact RamareSaouter2003.prime_interval_nat_ladder_c03108 n (by omega) (by omega)
          · -- n <= 19768170371281
            exact RamareSaouter2003.prime_interval_nat_ladder_c03107 n (by omega) (by omega)
      · -- n <= 19719370132981
        rcases Nat.lt_or_ge 19573691046713 n with h8 | h8
        · -- n > 19573691046713
          rcases Nat.lt_or_ge 19622130767749 n with h10 | h10
          · -- n > 19622130767749
            rcases Nat.lt_or_ge 19670690364229 n with h12 | h12
            · -- n > 19670690364229
              exact RamareSaouter2003.prime_interval_nat_ladder_c03106 n (by omega) (by omega)
            · -- n <= 19670690364229
              exact RamareSaouter2003.prime_interval_nat_ladder_c03105 n (by omega) (by omega)
          · -- n <= 19622130767749
            exact RamareSaouter2003.prime_interval_nat_ladder_c03104 n (by omega) (by omega)
        · -- n <= 19573691046713
          rcases Nat.lt_or_ge 19477170048541 n with h10 | h10
          · -- n > 19477170048541
            rcases Nat.lt_or_ge 19525370905409 n with h12 | h12
            · -- n > 19525370905409
              exact RamareSaouter2003.prime_interval_nat_ladder_c03103 n (by omega) (by omega)
            · -- n <= 19525370905409
              exact RamareSaouter2003.prime_interval_nat_ladder_c03102 n (by omega) (by omega)
          · -- n <= 19477170048541
            exact RamareSaouter2003.prime_interval_nat_ladder_c03101 n (by omega) (by omega)
