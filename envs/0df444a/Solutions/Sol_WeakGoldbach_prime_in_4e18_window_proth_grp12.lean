-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:04:53.446025+00:00
-- url     : https://prove2.me/submissions/c2c5cd6e-41f3-4e9f-a5a2-da124de277d4

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg540
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg541
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg542
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg543
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg544
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg545
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg546
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg547
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg548
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg549
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg550
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg551
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg552
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg553
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg554
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg555
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg556
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg557
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg558
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg559
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg560
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg561
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg562
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg563
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg564
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg565
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg566
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg567
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg568
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg569
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg570
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg571
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg572
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg573
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg574
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg575
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg576
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg577
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg578
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg579
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg580
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg581
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg582
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg583
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg584
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg585
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg586
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg587
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg588

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp12` (68925832687279480470765569 <= x < 75191817113483238747144193) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg540` .. `WeakGoldbach.prime_in_4e18_window_proth_seg588`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 68925832687279480470765569 ≤ x) (hx : x < 75191817113483238747144193) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 71994886283777391030435841 with hc24 | hc24
  · rcases Nat.lt_or_ge x 70460359485071038913445889 with hc12 | hc12
    · rcases Nat.lt_or_ge x 69693096084943806668996609 with hc6 | hc6
      · rcases Nat.lt_or_ge x 69309464386674593523302401 with hc3 | hc3
        · rcases Nat.lt_or_ge x 69053709920293903581315073 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg540 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 69181587153589801668575233 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg541 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg542 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 69437341619706608819896321 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg543 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 69565218852914545976934401 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg544 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg545 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 70076727785834255535308801 with hc9 | hc9
        · rcases Nat.lt_or_ge x 69820973318978576570122241 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg546 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 69948850552907793354981377 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg547 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg548 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 70204605018795902087725057 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg549 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 70332482252091800174985217 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg550 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg551 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 71227622884002002506874881 with hc18 | hc18
      · rcases Nat.lt_or_ge x 70843991185011509733359617 with hc15 | hc15
        · rcases Nat.lt_or_ge x 70588236718490082303016961 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg552 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 70716113951873941320499201 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg553 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg554 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 70971868417638904750931969 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg555 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 71099745651233870000947201 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg556 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg557 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 71611254583995249884921857 with hc21 | hc21
        · rcases Nat.lt_or_ge x 71355500116998833431379969 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg558 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 71483377351068787704594433 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg559 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg560 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 71739131816921712065249281 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg561 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 71867009049338000850288641 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg562 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg563 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 73529413081955977566093313 with hc36 | hc36
    · rcases Nat.lt_or_ge x 72762149682813907740131329 with hc30 | hc30
      · rcases Nat.lt_or_ge x 72378517982627146315595777 with hc27 | hc27
        · rcases Nat.lt_or_ge x 72122763516756629768896513 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg564 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 72250640749366432600424449 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg565 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg566 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 72506395216485994356277249 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg567 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 72634272449482825280782337 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg568 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg569 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 73145781382402534839156737 with hc33 | hc33
        · rcases Nat.lt_or_ge x 72890026915969068339036161 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg570 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 73017904148789977403097089 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg571 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg572 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 73273658614009583066152961 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg573 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 73401535848572118548611073 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg574 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg575 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 74296676481045270833922049 with hc42 | hc42
      · rcases Nat.lt_or_ge x 73913044781421459362807809 with hc39 | hc39
        · rcases Nat.lt_or_ge x 73657290315163914723131393 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg576 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 73785167548336667508080641 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg577 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg578 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 74040922014576619961712641 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg579 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 74168799247291975909507073 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg580 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg581 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 74680308180317238584147969 with hc45 | hc45
        · rcases Nat.lt_or_ge x 74424553714411537665359873 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg582 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 74552430947496329520087041 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg583 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg584 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 74936062647067364433068033 with hc47 | hc47
          · rcases Nat.lt_or_ge x 74808185413349253880741889 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg585 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg586 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 75063939879817904752951297 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg587 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg588 x (by omega) (by omega)
