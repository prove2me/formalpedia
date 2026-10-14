-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp114
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T18:01:10.264677+00:00
-- url     : https://prove2.me/submissions/c044d25a-8b1e-4c8b-b9cb-56605edbebc6

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05668
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05688
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05700

theorem solution (n : Nat)
    (hn : 19546801688263991 < n) (hupper : n <= 22514638705499333) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 20978319526421281 n with h2 | h2
  · -- n > 20978319526421281
    rcases Nat.lt_or_ge 21702195394721087 n with h4 | h4
    · -- n > 21702195394721087
      rcases Nat.lt_or_ge 22073462662446179 n with h6 | h6
      · -- n > 22073462662446179
        rcases Nat.lt_or_ge 22261462045155413 n with h8 | h8
        · -- n > 22261462045155413
          rcases Nat.lt_or_ge 22387691414583973 n with h10 | h10
          · -- n > 22387691414583973
            rcases Nat.lt_or_ge 22451076159471919 n with h12 | h12
            · -- n > 22451076159471919
              exact RamareSaouter2003.prime_interval_nat_ladder_c05700 n (by omega) (by omega)
            · -- n <= 22451076159471919
              exact RamareSaouter2003.prime_interval_nat_ladder_c05699 n (by omega) (by omega)
          · -- n <= 22387691414583973
            rcases Nat.lt_or_ge 22324490740884347 n with h12 | h12
            · -- n > 22324490740884347
              exact RamareSaouter2003.prime_interval_nat_ladder_c05698 n (by omega) (by omega)
            · -- n <= 22324490740884347
              exact RamareSaouter2003.prime_interval_nat_ladder_c05697 n (by omega) (by omega)
        · -- n <= 22261462045155413
          rcases Nat.lt_or_ge 22135958513506697 n with h10 | h10
          · -- n > 22135958513506697
            rcases Nat.lt_or_ge 22198630029694609 n with h12 | h12
            · -- n > 22198630029694609
              exact RamareSaouter2003.prime_interval_nat_ladder_c05696 n (by omega) (by omega)
            · -- n <= 22198630029694609
              exact RamareSaouter2003.prime_interval_nat_ladder_c05695 n (by omega) (by omega)
          · -- n <= 22135958513506697
            exact RamareSaouter2003.prime_interval_nat_ladder_c05694 n (by omega) (by omega)
      · -- n <= 22073462662446179
        rcases Nat.lt_or_ge 21887038339588291 n with h8 | h8
        · -- n > 21887038339588291
          rcases Nat.lt_or_ge 21949002357372901 n with h10 | h10
          · -- n > 21949002357372901
            rcases Nat.lt_or_ge 22011142370912459 n with h12 | h12
            · -- n > 22011142370912459
              exact RamareSaouter2003.prime_interval_nat_ladder_c05693 n (by omega) (by omega)
            · -- n <= 22011142370912459
              exact RamareSaouter2003.prime_interval_nat_ladder_c05692 n (by omega) (by omega)
          · -- n <= 21949002357372901
            exact RamareSaouter2003.prime_interval_nat_ladder_c05691 n (by omega) (by omega)
        · -- n <= 21887038339588291
          rcases Nat.lt_or_ge 21763636264026511 n with h10 | h10
          · -- n > 21763636264026511
            rcases Nat.lt_or_ge 21825254991964903 n with h12 | h12
            · -- n > 21825254991964903
              exact RamareSaouter2003.prime_interval_nat_ladder_c05690 n (by omega) (by omega)
            · -- n <= 21825254991964903
              exact RamareSaouter2003.prime_interval_nat_ladder_c05689 n (by omega) (by omega)
          · -- n <= 21763636264026511
            exact RamareSaouter2003.prime_interval_nat_ladder_c05688 n (by omega) (by omega)
    · -- n <= 21702195394721087
      rcases Nat.lt_or_ge 21337178250681971 n with h6 | h6
      · -- n > 21337178250681971
        rcases Nat.lt_or_ge 21518911406756749 n with h8 | h8
        · -- n > 21518911406756749
          rcases Nat.lt_or_ge 21579832447084739 n with h10 | h10
          · -- n > 21579832447084739
            rcases Nat.lt_or_ge 21640927867826431 n with h12 | h12
            · -- n > 21640927867826431
              exact RamareSaouter2003.prime_interval_nat_ladder_c05687 n (by omega) (by omega)
            · -- n <= 21640927867826431
              exact RamareSaouter2003.prime_interval_nat_ladder_c05686 n (by omega) (by omega)
          · -- n <= 21579832447084739
            exact RamareSaouter2003.prime_interval_nat_ladder_c05685 n (by omega) (by omega)
        · -- n <= 21518911406756749
          rcases Nat.lt_or_ge 21397580132948339 n with h10 | h10
          · -- n > 21397580132948339
            rcases Nat.lt_or_ge 21458159969522671 n with h12 | h12
            · -- n > 21458159969522671
              exact RamareSaouter2003.prime_interval_nat_ladder_c05684 n (by omega) (by omega)
            · -- n <= 21458159969522671
              exact RamareSaouter2003.prime_interval_nat_ladder_c05683 n (by omega) (by omega)
          · -- n <= 21397580132948339
            exact RamareSaouter2003.prime_interval_nat_ladder_c05682 n (by omega) (by omega)
      · -- n <= 21337178250681971
        rcases Nat.lt_or_ge 21156973832831261 n with h8 | h8
        · -- n > 21156973832831261
          rcases Nat.lt_or_ge 21216869463116801 n with h10 | h10
          · -- n > 21216869463116801
            rcases Nat.lt_or_ge 21276937296842609 n with h12 | h12
            · -- n > 21276937296842609
              exact RamareSaouter2003.prime_interval_nat_ladder_c05681 n (by omega) (by omega)
            · -- n <= 21276937296842609
              exact RamareSaouter2003.prime_interval_nat_ladder_c05680 n (by omega) (by omega)
          · -- n <= 21216869463116801
            exact RamareSaouter2003.prime_interval_nat_ladder_c05679 n (by omega) (by omega)
        · -- n <= 21156973832831261
          rcases Nat.lt_or_ge 21037712151193063 n with h10 | h10
          · -- n > 21037712151193063
            rcases Nat.lt_or_ge 21097260472256923 n with h12 | h12
            · -- n > 21097260472256923
              exact RamareSaouter2003.prime_interval_nat_ladder_c05678 n (by omega) (by omega)
            · -- n <= 21097260472256923
              exact RamareSaouter2003.prime_interval_nat_ladder_c05677 n (by omega) (by omega)
          · -- n <= 21037712151193063
            exact RamareSaouter2003.prime_interval_nat_ladder_c05676 n (by omega) (by omega)
  · -- n <= 20978319526421281
    rcases Nat.lt_or_ge 20221300935097027 n with h4 | h4
    · -- n > 20221300935097027
      rcases Nat.lt_or_ge 20567239402278281 n with h6 | h6
      · -- n > 20567239402278281
        rcases Nat.lt_or_ge 20742421601100253 n with h8 | h8
        · -- n > 20742421601100253
          rcases Nat.lt_or_ge 20860040916136963 n with h10 | h10
          · -- n > 20860040916136963
            rcases Nat.lt_or_ge 20919094453188229 n with h12 | h12
            · -- n > 20919094453188229
              exact RamareSaouter2003.prime_interval_nat_ladder_c05675 n (by omega) (by omega)
            · -- n <= 20919094453188229
              exact RamareSaouter2003.prime_interval_nat_ladder_c05674 n (by omega) (by omega)
          · -- n <= 20860040916136963
            rcases Nat.lt_or_ge 20801147287365157 n with h12 | h12
            · -- n > 20801147287365157
              exact RamareSaouter2003.prime_interval_nat_ladder_c05673 n (by omega) (by omega)
            · -- n <= 20801147287365157
              exact RamareSaouter2003.prime_interval_nat_ladder_c05672 n (by omega) (by omega)
        · -- n <= 20742421601100253
          rcases Nat.lt_or_ge 20625470018560679 n with h10 | h10
          · -- n > 20625470018560679
            rcases Nat.lt_or_ge 20683862627694373 n with h12 | h12
            · -- n > 20683862627694373
              exact RamareSaouter2003.prime_interval_nat_ladder_c05671 n (by omega) (by omega)
            · -- n <= 20683862627694373
              exact RamareSaouter2003.prime_interval_nat_ladder_c05670 n (by omega) (by omega)
          · -- n <= 20625470018560679
            exact RamareSaouter2003.prime_interval_nat_ladder_c05669 n (by omega) (by omega)
      · -- n <= 20567239402278281
        rcases Nat.lt_or_ge 20393531258303459 n with h8 | h8
        · -- n > 20393531258303459
          rcases Nat.lt_or_ge 20451268788167311 n with h10 | h10
          · -- n > 20451268788167311
            rcases Nat.lt_or_ge 20509172441596103 n with h12 | h12
            · -- n > 20509172441596103
              exact RamareSaouter2003.prime_interval_nat_ladder_c05668 n (by omega) (by omega)
            · -- n <= 20509172441596103
              exact RamareSaouter2003.prime_interval_nat_ladder_c05667 n (by omega) (by omega)
          · -- n <= 20451268788167311
            exact RamareSaouter2003.prime_interval_nat_ladder_c05666 n (by omega) (by omega)
        · -- n <= 20393531258303459
          rcases Nat.lt_or_ge 20278550811043589 n with h10 | h10
          · -- n > 20278550811043589
            rcases Nat.lt_or_ge 20335955767711369 n with h12 | h12
            · -- n > 20335955767711369
              exact RamareSaouter2003.prime_interval_nat_ladder_c05665 n (by omega) (by omega)
            · -- n <= 20335955767711369
              exact RamareSaouter2003.prime_interval_nat_ladder_c05664 n (by omega) (by omega)
          · -- n <= 20278550811043589
            exact RamareSaouter2003.prime_interval_nat_ladder_c05663 n (by omega) (by omega)
    · -- n <= 20221300935097027
      rcases Nat.lt_or_ge 19881188618355593 n with h6 | h6
      · -- n > 19881188618355593
        rcases Nat.lt_or_ge 20050515759717791 n with h8 | h8
        · -- n > 20050515759717791
          rcases Nat.lt_or_ge 20107283033558801 n with h10 | h10
          · -- n > 20107283033558801
            rcases Nat.lt_or_ge 20164212075525251 n with h12 | h12
            · -- n > 20164212075525251
              exact RamareSaouter2003.prime_interval_nat_ladder_c05662 n (by omega) (by omega)
            · -- n <= 20164212075525251
              exact RamareSaouter2003.prime_interval_nat_ladder_c05661 n (by omega) (by omega)
          · -- n <= 20107283033558801
            exact RamareSaouter2003.prime_interval_nat_ladder_c05660 n (by omega) (by omega)
        · -- n <= 20050515759717791
          rcases Nat.lt_or_ge 19937474972223761 n with h10 | h10
          · -- n > 19937474972223761
            rcases Nat.lt_or_ge 19993913283652267 n with h12 | h12
            · -- n > 19993913283652267
              exact RamareSaouter2003.prime_interval_nat_ladder_c05659 n (by omega) (by omega)
            · -- n <= 19993913283652267
              exact RamareSaouter2003.prime_interval_nat_ladder_c05658 n (by omega) (by omega)
          · -- n <= 19937474972223761
            exact RamareSaouter2003.prime_interval_nat_ladder_c05657 n (by omega) (by omega)
      · -- n <= 19881188618355593
        rcases Nat.lt_or_ge 19713282072196927 n with h8 | h8
        · -- n > 19713282072196927
          rcases Nat.lt_or_ge 19769096170899961 n with h10 | h10
          · -- n > 19769096170899961
            rcases Nat.lt_or_ge 19825058710698379 n with h12 | h12
            · -- n > 19825058710698379
              exact RamareSaouter2003.prime_interval_nat_ladder_c05656 n (by omega) (by omega)
            · -- n <= 19825058710698379
              exact RamareSaouter2003.prime_interval_nat_ladder_c05655 n (by omega) (by omega)
          · -- n <= 19769096170899961
            exact RamareSaouter2003.prime_interval_nat_ladder_c05654 n (by omega) (by omega)
        · -- n <= 19713282072196927
          rcases Nat.lt_or_ge 19602136438093087 n with h10 | h10
          · -- n > 19602136438093087
            rcases Nat.lt_or_ge 19657635784990811 n with h12 | h12
            · -- n > 19657635784990811
              exact RamareSaouter2003.prime_interval_nat_ladder_c05653 n (by omega) (by omega)
            · -- n <= 19657635784990811
              exact RamareSaouter2003.prime_interval_nat_ladder_c05652 n (by omega) (by omega)
          · -- n <= 19602136438093087
            exact RamareSaouter2003.prime_interval_nat_ladder_c05651 n (by omega) (by omega)
