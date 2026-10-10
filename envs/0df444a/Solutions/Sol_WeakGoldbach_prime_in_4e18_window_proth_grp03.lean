-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp03
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:37:25.93062+00:00
-- url     : https://prove2.me/submissions/339cd7b7-672e-4b84-b42a-7c5f7b6fcecb

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg099
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg100
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg101
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg102
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg103
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg104
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg105
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg106
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg107
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg108
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg109
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg110
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg111
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg112
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg113
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg114
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg115
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg116
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg117
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg118
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg119
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg120
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg121
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg122
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg123
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg124
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg125
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg126
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg127
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg128
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg129
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg130
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg131
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg132
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg133
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg134
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg135
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg136
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg137
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg138
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg139
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg140
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg141
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg142
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg143
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg144
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg145
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg146
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg147

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp03` (12531972851867868448423937 <= x < 18797957278071626724802561) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg099` .. `WeakGoldbach.prime_in_4e18_window_proth_seg147`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 12531972851867868448423937 ≤ x) (hx : x < 18797957278071626724802561) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 15601026448418555566227457 with hc24 | hc24
  · rcases Nat.lt_or_ge x 14066499650187192472436737 with hc12 | hc12
    · rcases Nat.lt_or_ge x 13299236251062714832519169 with hc6 | hc6
      · rcases Nat.lt_or_ge x 12915604551491679919538177 with hc3 | hc3
        · rcases Nat.lt_or_ge x 12659850084882291558973441 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg099 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 12787727318019859971833857 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg100 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg101 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 13043481784629248332398593 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg102 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 13171359017327012094148609 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg103 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg104 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 13682867950211537280434177 with hc9 | hc9
        · rcases Nat.lt_or_ge x 13427113484182691059335169 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg105 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 13554990717109153239662593 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg106 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg107 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 13810745182803747925917697 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg108 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 13938622416961663129354241 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg109 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg110 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 14833763049294077926309889 with hc18 | hc18
      · rcases Nat.lt_or_ge x 14450131348878618083196929 with hc15 | hc15
        · rcases Nat.lt_or_ge x 14194376882533112513298433 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg111 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 14322254116515105856290817 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg112 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg113 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 14578008582755058309922817 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg114 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 14705885815892626722783233 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg115 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg116 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 15217394748108648839380993 with hc21 | hc21
        · rcases Nat.lt_or_ge x 14961640282114986990370817 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg117 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 15089517515446069449719809 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg118 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg119 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 15345271979522183019888641 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg120 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 15473149214753221572034561 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg121 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg122 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 17135553245875862474063873 with hc36 | hc36
    · rcases Nat.lt_or_ge x 16368289847402295717789697 with hc30 | hc30
      · rcases Nat.lt_or_ge x 15984658147461824897875969 with hc27 | hc27
        · rcases Nat.lt_or_ge x 15728903681204280258199553 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg123 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 15856780914658508019859457 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg124 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg125 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 16112535380916052659535873 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg126 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 16240412614370280421195777 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg127 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg128 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 16751921547149252491214849 with hc33 | hc33
        · rcases Nat.lt_or_ge x 16496167080117651665584129 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg129 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 16624044313624655985377281 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg130 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg131 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 16879798779794239694831617 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg132 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 17007676013512350247157761 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg133 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg134 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 17902816645791988485980161 with hc42 | hc42
      · rcases Nat.lt_or_ge x 17519184946185769200910337 with hc39 | hc39
        · rcases Nat.lt_or_ge x 17263430479365274607812609 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg135 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 17391307712872278927605761 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg136 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg137 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 17647062179200192311459841 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg138 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 17774939412284984166187009 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg139 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg140 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 18286448345099140608294913 with hc45 | hc45
        · rcases Nat.lt_or_ge x 18030693878929556898840577 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg141 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 18158571111644912846635009 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg142 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg143 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 18542202810019679108595713 with hc47 | hc47
          · rcases Nat.lt_or_ge x 18414325576917295067824129 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg144 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg145 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 18670080042629481940123649 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg146 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg147 x (by omega) (by omega)
