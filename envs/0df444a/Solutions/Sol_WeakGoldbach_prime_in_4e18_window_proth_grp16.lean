-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:19:47.339314+00:00
-- url     : https://prove2.me/submissions/3e04cd84-d30f-4f9c-a460-d16c8d0e7ae0

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg735
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg736
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg737
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg738
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg739
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg740
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg741
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg742
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg743
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg744
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg745
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg746
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg747
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg748
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg749
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg750
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg751
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg752
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg753
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg754
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg755
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg756
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg757
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg758
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg759
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg760
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg761
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg762
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg763
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg764
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg765
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg766
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg767
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg768
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg769
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg770
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg771
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg772
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg773
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg774
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg775
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg776
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg777
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg778
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg779
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg780
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg781
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg782

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp16` (93861893158763431116931073 <= x < 100000000351847213166493697) from the 48 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg735` .. `WeakGoldbach.prime_in_4e18_window_proth_seg782`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 93861893158763431116931073 ≤ x) (hx : x < 100000000351847213166493697) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 96930946754944682327801857 with hc24 | hc24
  · rcases Nat.lt_or_ge x 95396419956783687978188801 with hc12 | hc12
    · rcases Nat.lt_or_ge x 94629156557061076012761089 with hc6 | hc6
      · rcases Nat.lt_or_ge x 94245524858281689471778817 with hc3 | hc3
        · rcases Nat.lt_or_ge x 93989770391900999529791489 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg735 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 94117647623877483663720449 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg736 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg737 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 94373402091577587559038977 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg738 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 94501279324117021646389249 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg739 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg740 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 95012788256421004693209089 with hc9 | hc9
        · rcases Nat.lt_or_ge x 94757033790884739681353729 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg741 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 94884911024321375256969217 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg742 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg743 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 95140665490561327710601217 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg744 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 95268542723804449239728129 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg745 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg746 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 96163683355697059385573377 with hc18 | hc18
      · rcases Nat.lt_or_ge x 95780051656601013495791617 with hc15 | hc15
        · rcases Nat.lt_or_ge x 95524297190185139181715457 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg747 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 95652174421352382757601281 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg748 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg749 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 95907928889703397536563201 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg750 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 96035806122928926879645697 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg751 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg752 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 96547315055479200531087361 with hc21 | hc21
        · rcases Nat.lt_or_ge x 96291560589327209007677441 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg753 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 96419437821567575932272641 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg754 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg755 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 96675192288370478339325953 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg756 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 96803069521033057728987137 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg757 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg758 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 98465473553193637607636993 with hc36 | hc36
    · rcases Nat.lt_or_ge x 97698210154315450572341249 with hc30 | hc30
      · rcases Nat.lt_or_ge x 97314578453319448589762561 with hc27 | hc27
        · rcases Nat.lt_or_ge x 97058823986762836787331073 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg759 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 97186701221290187897700353 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg760 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg761 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 97442455687618101281554433 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg762 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 97570332920913999368814593 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg763 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg764 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 98081841850192126415994881 with hc33 | hc33
        · rcases Nat.lt_or_ge x 97826087387593756473556993 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg765 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 97953964620731324886417409 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg766 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg767 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 98209719087112014828404737 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg768 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 98337596320267175427309569 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg769 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg770 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 99232736952494037107998721 with hc42 | hc42
      · rcases Nat.lt_or_ge x 98849105252817449078751233 with hc39 | hc39
        · rcases Nat.lt_or_ge x 98593350786753418485563393 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg771 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 98721228019187299456647169 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg772 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg773 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 98976982486113347166011393 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg774 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 99104859719039809346338817 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg775 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg776 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 99616368652153032951201793 with hc45 | hc45
        · rcases Nat.lt_or_ge x 99360614185895488311525377 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg777 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 99488491418962687980208129 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg778 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg779 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 99744245885079495131529217 with hc46 | hc46
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg780 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 99872123118551315079233537 with hc47 | hc47
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg781 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg782 x (by omega) (by omega)
