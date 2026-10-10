-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp02
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:21:27.724974+00:00
-- url     : https://prove2.me/submissions/3b4b2f35-b567-427b-b52c-7e69fd676338

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg050
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg051
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg052
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg053
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg054
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg055
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg056
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg057
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg058
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg059
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg060
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg061
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg062
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg063
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg064
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg065
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg066
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg067
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg068
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg069
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg070
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg071
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg072
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg073
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg074
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg075
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg076
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg077
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg078
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg079
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg080
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg081
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg082
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg083
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg084
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg085
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg086
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg087
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg088
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg089
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg090
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg091
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg092
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg093
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg094
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg095
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg096
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg097
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg098

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp02` (6265988425752071102267393 <= x < 12531972851867868448423937) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg050` .. `WeakGoldbach.prime_in_4e18_window_proth_seg098`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 6265988425752071102267393 ≤ x) (hx : x < 12531972851867868448423937) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 9335042021774992638738433 with hc24 | hc24
  · rcases Nat.lt_or_ge x 7800515224036210754191361 with hc12 | hc12
    · rcases Nat.lt_or_ge x 7033251824102492556230657 with hc6 | hc6
      · rcases Nat.lt_or_ge x 6649620125252737271070721 with hc3 | hc3
        · rcases Nat.lt_or_ge x 6393865658414650491928577 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg050 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 6521742892079984486121473 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg051 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg052 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 6777497357932908846776321 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg053 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 6905374591316767864258561 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg054 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg055 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 7416883524412399283077121 with hc9 | hc9
        · rcases Nat.lt_or_ge x 7161129057116915666780161 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg056 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 7289006291151685567905793 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg057 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg058 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 7544760757286084905271297 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg059 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 7672637990669943922753537 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg060 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg061 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 8567778622597738440687617 with hc18 | hc18
      · rcases Nat.lt_or_ge x 8184146922868373853306881 with hc15 | hc15
        · rcases Nat.lt_or_ge x 7928392457173779167051777 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg062 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 8056269690240978835734529 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg063 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg064 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 8312024156480931289366529 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg065 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 8439901389987935609159681 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg066 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg067 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 8951410322045628051357697 with hc21 | hc21
        · rcases Nat.lt_or_ge x 8695655855559384993103873 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg068 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 8823533089435825219829761 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg069 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg070 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 9079287555200788650262529 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg071 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 9207164789077228876988417 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg072 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg073 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 10869568820164685406928897 with hc36 | hc36
    · rcases Nat.lt_or_ge x 10102305421286498371633153 with hc30 | hc30
      · rcases Nat.lt_or_ge x 9718673721451580667985921 with hc27 | hc27
        · rcases Nat.lt_or_ge x 9462919255334773516664833 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg074 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 9590796488155682580725761 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg075 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg076 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 9846550954448411592491009 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg077 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 9974428188060969028550657 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg078 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg079 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 10485937120452913005592577 with hc33 | hc33
        · rcases Nat.lt_or_ge x 10230182654582396458893313 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg080 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 10358059887315344592732161 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg081 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg082 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 10613814353959917325385729 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg083 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 10741691587238223226601473 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg084 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg085 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 11636832218778989651558401 with hc42 | hc42
      · rcases Nat.lt_or_ge x 11253200519894049994309633 with hc39 | hc39
        · rcases Nat.lt_or_ge x 10997446053724466284855297 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg086 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 11125323286914811255848961 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg087 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg088 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 11381077753207540267614209 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg089 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 11508954986450661796741121 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg090 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg091 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 12020463919036119820271617 with hc45 | hc45
        · rcases Nat.lt_or_ge x 11764709452461915831795713 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg092 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 11892586684227293733191681 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg093 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg094 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 12276218385311256645992449 with hc47 | hc47
          · rcases Nat.lt_or_ge x 12148341152226464791265281 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg095 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg096 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 12404095618026612593786881 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg097 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg098 x (by omega) (by omega)
