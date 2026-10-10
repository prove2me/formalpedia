-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp01
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:18:35.686543+00:00
-- url     : https://prove2.me/submissions/a2e66a4c-22cd-4f63-b2c9-313352fa830e

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg001
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg002
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg003
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg004
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg005
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg006
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg007
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg008
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg009
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg010
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg011
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg012
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg013
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg014
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg015
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg016
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg017
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg018
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg019
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg020
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg021
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg022
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg023
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg024
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg025
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg026
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg027
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg028
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg029
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg030
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg031
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg032
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg033
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg034
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg035
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg036
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg037
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg038
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg039
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg040
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg041
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg042
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg043
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg044
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg045
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg046
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg047
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg048
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg049

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp01` (3999671458128199681 <= x < 6265988425752071102267393) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg001` .. `WeakGoldbach.prime_in_4e18_window_proth_seg049`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 3999671458128199681 ≤ x) (hx : x < 6265988425752071102267393) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 3069057595923078083248129 with hc24 | hc24
  · rcases Nat.lt_or_ge x 1534530797691714989457409 with hc12 | hc12
    · rcases Nat.lt_or_ge x 767267397089493721808897 with hc6 | hc6
      · rcases Nat.lt_or_ge x 383635699154532110958593 with hc3 | hc3
        · rcases Nat.lt_or_ge x 127881232668289052704769 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg001 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 255758464064231047168001 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg002 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg003 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 511512929653272617156609 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg004 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 639390164884311169302529 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg005 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg006 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 1150899098032719146254337 with hc9 | hc9
        · rcases Nat.lt_or_ge x 895144631124263622934529 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg007 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 1023021863874803942817793 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg008 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg009 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 1278776331328617233514497 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg010 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 1406653563551391972065281 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg011 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg012 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 2301794196798600443330561 with hc18 | hc18
      · rcases Nat.lt_or_ge x 1918162497368303018704897 with hc15 | hc15
        · rcases Nat.lt_or_ge x 1662408030794099030228993 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg013 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 1790285264283511163977729 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg014 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg015 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 2046039730347541757165569 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg016 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 2173916963608255472336897 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg017 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg018 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 2685425896264082240045057 with hc21 | hc21
        · rcases Nat.lt_or_ge x 2429671429918576670146561 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg019 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 2557548661754323315720193 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg020 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg021 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 2813303129296097536638977 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg022 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 2941180362046637856522241 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg023 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg024 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 4603584394330363037483009 with hc36 | hc36
    · rcases Nat.lt_or_ge x 3836320994167946420944897 with hc30 | hc30
      · rcases Nat.lt_or_ge x 3452689294755241182363649 with hc27 | hc27
        · rcases Nat.lt_or_ge x 3196934828955093379842049 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg025 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 3324812061318605606748161 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg026 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg027 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 3580566527910401781268481 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg028 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 3708443762033132612616193 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg029 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg030 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 4219952694495445333835777 with hc33 | hc33
        · rcases Nat.lt_or_ge x 3964198228255492880203777 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg031 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 4092075461410653479108609 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg032 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg033 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 4347829927826527793184769 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg034 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 4475707161175202438578177 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg035 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg036 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 5370847792997443840245761 with hc42 | hc42
      · rcases Nat.lt_or_ge x 4987216093637515159797761 with hc39 | hc39
        · rcases Nat.lt_or_ge x 4731461627450339264299009 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg037 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 4859338860218471770226689 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg038 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg039 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 5115093327144519479590913 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg040 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 5242970560334864450584577 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg041 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg042 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 5754479493078652148514817 with hc45 | hc45
        · rcases Nat.lt_or_ge x 5498725026610001276305409 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg043 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 5626602258727222898589697 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg044 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg045 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 6010233959424157718413313 with hc47 | hc47
          · rcases Nat.lt_or_ge x 5882356726110667445108737 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg046 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg047 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 6138111192614502689406977 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg048 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg049 x (by omega) (by omega)
