-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:07:38.786708+00:00
-- url     : https://prove2.me/submissions/e67fefcc-bdb2-464b-9b9f-302c3d4af219

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg589
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg590
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg591
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg592
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg593
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg594
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg595
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg596
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg597
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg598
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg599
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg600
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg601
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg602
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg603
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg604
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg605
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg606
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg607
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg608
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg609
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg610
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg611
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg612
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg613
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg614
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg615
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg616
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg617
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg618
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg619
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg620
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg621
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg622
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg623
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg624
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg625
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg626
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg627
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg628
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg629
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg630
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg631
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg632
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg633
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg634
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg635
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg636
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg637

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp13` (75191817113483238747144193 <= x < 81457801538138884651614209) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg589` .. `WeakGoldbach.prime_in_4e18_window_proth_seg637`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 75191817113483238747144193 ≤ x) (hx : x < 81457801538138884651614209) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 78260870709383014981304321 with hc24 | hc24
  · rcases Nat.lt_or_ge x 76726343911362758120046593 with hc12 | hc12
    · rcases Nat.lt_or_ge x 75959080512220688294084609 with hc6 | hc6
      · rcases Nat.lt_or_ge x 75575448812473731520659457 with hc3 | hc3
        · rcases Nat.lt_or_ge x 75319694346743952462315521 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg589 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 75447571579195425619443713 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg590 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg591 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 75703326045980735840452609 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg592 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 75831203279329410485846017 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg593 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg594 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 76342712211615801346621441 with hc9 | hc9
        · rcases Nat.lt_or_ge x 76086957745498994195300353 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg595 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 76214834978495825119805441 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg596 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg597 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 76470589444595040085082113 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg598 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 76598466678577033428074497 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg599 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg600 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 77493607310768710736674817 with hc18 | hc18
      · rcases Nat.lt_or_ge x 77109975611338413312049153 with hc15 | hc15
        · rcases Nat.lt_or_ge x 76854221144799393695662081 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg601 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 76982098377796224620167169 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg602 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg603 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 77237852844335244236554241 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg604 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 77365730077631142323814401 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg605 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg606 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 77877239010339745649655809 with hc21 | hc21
        · rcases Nat.lt_or_ge x 77621484544064608823934977 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg607 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 77749361777131808492617729 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg608 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg609 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 78005116243582867178782721 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg610 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 78132993476122301266132993 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg611 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg612 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 79795397508247696772694017 with hc36 | hc36
    · rcases Nat.lt_or_ge x 79028134109158403504865281 with hc30 | hc30
      · rcases Nat.lt_or_ge x 78644502408954049894285313 with hc27 | hc27
        · rcases Nat.lt_or_ge x 78388747942291884975587329 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg613 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 78516625175376676830314497 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg614 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg615 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 78772379642249947981545473 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg616 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 78900256875000488301428737 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg617 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg618 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 79411765807726683813314561 with hc33 | hc33
        · rcases Nat.lt_or_ge x 79156011341873759452659713 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg619 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 79283888574202087307476993 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg620 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg621 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 79539643041110542830796801 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg622 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 79667520274899022127300609 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg623 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg624 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 80562660907231436924256257 with hc42 | hc42
      · rcases Nat.lt_or_ge x 80179029207290966104342529 with hc39 | hc39
        · rcases Nat.lt_or_ge x 79923274740857499604221953 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg625 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 80051151974153397691482113 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg626 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg627 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 80306906440111875168403457 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg628 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 80434783673917946650951681 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg629 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg630 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 80946292604902515744440321 with hc45 | hc45
        · rcases Nat.lt_or_ge x 80690538140474558453383169 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg631 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 80818415372697333191933953 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg632 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg633 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 81202047073112793035046913 with hc47 | hc47
          · rcases Nat.lt_or_ge x 81074169839975224622186497 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg634 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg635 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 81329924305986478657241089 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg636 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg637 x (by omega) (by omega)
