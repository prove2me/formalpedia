-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:17:38.288988+00:00
-- url     : https://prove2.me/submissions/37507592-ffe8-4d07-8351-befcdad40eb3

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg687
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg688
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg689
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg690
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg691
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg692
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg693
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg694
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg695
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg696
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg697
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg698
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg699
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg700
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg701
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg702
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg703
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg704
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg705
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg706
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg707
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg708
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg709
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg710
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg711
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg712
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg713
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg714
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg715
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg716
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg717
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg718
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg719
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg720
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg721
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg722
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg723
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg724
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg725
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg726
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg727
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg728
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg729
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg730
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg731
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg732
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg733
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg734

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp15` (87723785965626872509235201 <= x < 93861893158763431116931073) from the 48 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg687` .. `WeakGoldbach.prime_in_4e18_window_proth_seg734`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 87723785965626872509235201 ≤ x) (hx : x < 93861893158763431116931073) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 90792839561509056557350913 with hc24 | hc24
  · rcases Nat.lt_or_ge x 89258312763998973091381249 with hc12 | hc12
    · rcases Nat.lt_or_ge x 88491049363818964288798721 with hc6 | hc6
      · rcases Nat.lt_or_ge x 88107417665250683980349441 with hc3 | hc3
        · rcases Nat.lt_or_ge x 87851663198711664363962369 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg687 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 87979540431039992218779649 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg688 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg689 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 88235294898581766439698433 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg690 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 88363172131314714573537281 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg691 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg692 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 88874681063583513248268289 with hc9 | hc9
        · rcases Nat.lt_or_ge x 88618926598117616980590593 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg693 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 88746803830938526044651521 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg694 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg695 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 89002558297741428451704833 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg696 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 89130435530087348492566529 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg697 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg698 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 90025576162525316405788673 with hc18 | hc18
      · rcases Nat.lt_or_ge x 89641944463534823632273409 with hc15 | hc15
        · rcases Nat.lt_or_ge x 89386189996943027457753089 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg699 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 89514067229746344335769601 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg700 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg701 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 89769821696443693626556417 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg702 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 89897698930073843248660481 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg703 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg704 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 90409207862553748155924481 with hc21 | hc21
        · rcases Nat.lt_or_ge x 90153453395750845748871169 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg705 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 90281330629539325045374977 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg706 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg707 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 90537085095849646243184641 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg708 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 90664962328565002190979073 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg709 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg710 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 92327366360356146162696193 with hc36 | hc36
    · rcases Nat.lt_or_ge x 91560102961178891964645377 with hc30 | hc30
      · rcases Nat.lt_or_ge x 91176471261502303935397889 with hc27 | hc27
        · rcases Nat.lt_or_ge x 90920716794646624970211329 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg711 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 91048594028558249569026049 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg712 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg713 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 91304348494850978580791297 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg714 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 91432225728146876668051457 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg715 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg716 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 91943734660785111249715201 with hc33 | hc33
        · rcases Nat.lt_or_ge x 91687980193718326051995649 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg717 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 91815857427348475674099713 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg718 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg719 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 92071611893518059383554049 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg720 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 92199489126901918401036289 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg721 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg722 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 93094629759146372267769857 with hc42 | hc42
      · rcases Nat.lt_or_ge x 92710998060138287308210177 with hc39 | hc39
        · rcases Nat.lt_or_ge x 92455243592139116250136577 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg723 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 92583120826420176755884033 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg724 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg725 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 92838875293275855721070593 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg726 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 92966752525410669529399297 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg727 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg728 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 93478261458928513413283841 with hc45 | hc45
        · rcases Nat.lt_or_ge x 93222506992653376587563009 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg729 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 93350384225368732535357441 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg730 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg731 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 93606138692488294291210241 with hc46 | hc46
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg732 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 93734015925608270518026241 with hc47 | hc47
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg733 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg734 x (by omega) (by omega)
