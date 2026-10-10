-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:09:47.777439+00:00
-- url     : https://prove2.me/submissions/e064fb58-1372-4dcf-b938-d993188ffe11

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg638
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg639
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg640
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg641
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg642
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg643
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg644
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg645
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg646
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg647
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg648
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg649
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg650
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg651
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg652
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg653
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg654
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg655
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg656
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg657
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg658
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg659
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg660
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg661
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg662
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg663
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg664
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg665
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg666
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg667
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg668
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg669
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg670
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg671
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg672
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg673
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg674
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg675
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg676
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg677
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg678
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg679
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg680
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg681
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg682
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg683
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg684
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg685
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg686

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp14` (81457801538138884651614209 <= x < 87723785965626872509235201) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg638` .. `WeakGoldbach.prime_in_4e18_window_proth_seg686`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 81457801538138884651614209 ≤ x) (hx : x < 87723785965626872509235201) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 84526855135868248234393601 with hc24 | hc24
  · rcases Nat.lt_or_ge x 82992328336423024303538177 with hc12 | hc12
    · rcases Nat.lt_or_ge x 82225064938582776244862977 with hc6 | hc6
      · rcases Nat.lt_or_ge x 81841433238536752308682753 with hc3 | hc3
        · rcases Nat.lt_or_ge x 81585678772754196692205569 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg638 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 81713556005293630779555841 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg639 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg640 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 81969310472378008163319809 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg641 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 82097187705040587552980993 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg642 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg643 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 82608696638417693948510209 with hc9 | hc9
        · rcases Nat.lt_or_ge x 82352942171210171262435329 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg644 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 82480819404646806838050817 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg645 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg646 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 82736573871608038919503873 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg647 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 82864451104077104262676481 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg648 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg649 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 83759591735353987896967169 with hc18 | hc18
      · rcases Nat.lt_or_ge x 83375960037524579402383361 with hc15 | hc15
        · rcases Nat.lt_or_ge x 83120205571126297274351617 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg650 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 83248082804263865687212033 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg651 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg652 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 83503837270380672838533121 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg653 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 83631714503641386553704449 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg654 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg655 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 84143223436455542995812353 with hc21 | hc21
        · rcases Nat.lt_or_ge x 83887468969177651565559809 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg656 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 84015346203476304257351681 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg657 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg658 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 84271100669364412990095361 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg659 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 84398977903029746984288257 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg660 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg661 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 86061381934293125374672897 with hc36 | hc36
    · rcases Nat.lt_or_ge x 85294118535326977409155073 with hc30 | hc30
      · rcases Nat.lt_or_ge x 84910486835228176914841601 with hc27 | hc27
        · rcases Nat.lt_or_ge x 84654732369041001019342849 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg662 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 84782609601967463199670273 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg663 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg664 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 85038364068295376583524353 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg665 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 85166241301767196531228673 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg666 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg667 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 85677750233473045252538369 with hc33 | hc33
        · rcases Nat.lt_or_ge x 85421995767567344333750273 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg668 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 85549873000845650234966017 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg669 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg670 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 85805627467437446409486337 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg671 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 85933504701261110078078977 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg672 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg673 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 86828645333540748316901377 with hc42 | hc42
      · rcases Nat.lt_or_ge x 86445013632808629124988929 with hc39 | hc39
        · rcases Nat.lt_or_ge x 86189259167325140671266817 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg674 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 86317136400621038758526977 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg675 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg676 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 86572890865998974095982593 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg677 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 86700768100367995531952129 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg678 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg679 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 87212277032320134857883649 with hc45 | hc45
        · rcases Nat.lt_or_ge x 86956522566731093287895041 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg680 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 87084399799411264863600641 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg681 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg682 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 87468031499334143497469953 with hc47 | hc47
          · rcases Nat.lt_or_ge x 87340154266266943828787201 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg683 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg684 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 87595908732278197863841793 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg685 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg686 x (by omega) (by omega)
