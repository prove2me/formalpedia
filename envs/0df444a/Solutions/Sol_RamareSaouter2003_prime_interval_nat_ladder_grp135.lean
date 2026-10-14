-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp135
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T01:15:44.970975+00:00
-- url     : https://prove2.me/submissions/35461c86-9e19-4b77-8c3f-3419a5764ba5

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06717
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06737
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06750

theorem solution (n : Nat)
    (hn : 380443069540112779 < n) (hupper : n <= 438210345612193751) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 408306544270352837 n with h2 | h2
  · -- n > 408306544270352837
    rcases Nat.lt_or_ge 422396704835269487 n with h4 | h4
    · -- n > 422396704835269487
      rcases Nat.lt_or_ge 429623154746683129 n with h6 | h6
      · -- n > 429623154746683129
        rcases Nat.lt_or_ge 433282516412456573 n with h8 | h8
        · -- n > 433282516412456573
          rcases Nat.lt_or_ge 435739477157053073 n with h10 | h10
          · -- n > 435739477157053073
            rcases Nat.lt_or_ge 436973182138222291 n with h12 | h12
            · -- n > 436973182138222291
              exact RamareSaouter2003.prime_interval_nat_ladder_c06750 n (by omega) (by omega)
            · -- n <= 436973182138222291
              exact RamareSaouter2003.prime_interval_nat_ladder_c06749 n (by omega) (by omega)
          · -- n <= 435739477157053073
            rcases Nat.lt_or_ge 434509253762101633 n with h12 | h12
            · -- n > 434509253762101633
              exact RamareSaouter2003.prime_interval_nat_ladder_c06748 n (by omega) (by omega)
            · -- n <= 434509253762101633
              exact RamareSaouter2003.prime_interval_nat_ladder_c06747 n (by omega) (by omega)
        · -- n <= 433282516412456573
          rcases Nat.lt_or_ge 430839463822163657 n with h10 | h10
          · -- n > 430839463822163657
            rcases Nat.lt_or_ge 432059289371417237 n with h12 | h12
            · -- n > 432059289371417237
              exact RamareSaouter2003.prime_interval_nat_ladder_c06746 n (by omega) (by omega)
            · -- n <= 432059289371417237
              exact RamareSaouter2003.prime_interval_nat_ladder_c06745 n (by omega) (by omega)
          · -- n <= 430839463822163657
            exact RamareSaouter2003.prime_interval_nat_ladder_c06744 n (by omega) (by omega)
      · -- n <= 429623154746683129
        rcases Nat.lt_or_ge 425994616776543037 n with h8 | h8
        · -- n > 425994616776543037
          rcases Nat.lt_or_ge 427200694494915247 n with h10 | h10
          · -- n > 427200694494915247
            rcases Nat.lt_or_ge 428410199972600969 n with h12 | h12
            · -- n > 428410199972600969
              exact RamareSaouter2003.prime_interval_nat_ladder_c06743 n (by omega) (by omega)
            · -- n <= 428410199972600969
              exact RamareSaouter2003.prime_interval_nat_ladder_c06742 n (by omega) (by omega)
          · -- n <= 427200694494915247
            exact RamareSaouter2003.prime_interval_nat_ladder_c06741 n (by omega) (by omega)
        · -- n <= 425994616776543037
          rcases Nat.lt_or_ge 423592582203001241 n with h10 | h10
          · -- n > 423592582203001241
            rcases Nat.lt_or_ge 424791901974970597 n with h12 | h12
            · -- n > 424791901974970597
              exact RamareSaouter2003.prime_interval_nat_ladder_c06740 n (by omega) (by omega)
            · -- n <= 424791901974970597
              exact RamareSaouter2003.prime_interval_nat_ladder_c06739 n (by omega) (by omega)
          · -- n <= 423592582203001241
            exact RamareSaouter2003.prime_interval_nat_ladder_c06738 n (by omega) (by omega)
    · -- n <= 422396704835269487
      rcases Nat.lt_or_ge 415291803533430961 n with h6 | h6
      · -- n > 415291803533430961
        rcases Nat.lt_or_ge 418829181821281199 n with h8 | h8
        · -- n > 418829181821281199
          rcases Nat.lt_or_ge 420014963765848559 n with h10 | h10
          · -- n > 420014963765848559
            rcases Nat.lt_or_ge 421204153425568651 n with h12 | h12
            · -- n > 421204153425568651
              exact RamareSaouter2003.prime_interval_nat_ladder_c06737 n (by omega) (by omega)
            · -- n <= 421204153425568651
              exact RamareSaouter2003.prime_interval_nat_ladder_c06736 n (by omega) (by omega)
          · -- n <= 420014963765848559
            exact RamareSaouter2003.prime_interval_nat_ladder_c06735 n (by omega) (by omega)
        · -- n <= 418829181821281199
          rcases Nat.lt_or_ge 416467582312821433 n with h10 | h10
          · -- n > 416467582312821433
            rcases Nat.lt_or_ge 417646715140922947 n with h12 | h12
            · -- n > 417646715140922947
              exact RamareSaouter2003.prime_interval_nat_ladder_c06734 n (by omega) (by omega)
            · -- n <= 417646715140922947
              exact RamareSaouter2003.prime_interval_nat_ladder_c06733 n (by omega) (by omega)
          · -- n <= 416467582312821433
            exact RamareSaouter2003.prime_interval_nat_ladder_c06732 n (by omega) (by omega)
      · -- n <= 415291803533430961
        rcases Nat.lt_or_ge 411784380843428183 n with h8 | h8
        · -- n > 411784380843428183
          rcases Nat.lt_or_ge 412950249672860267 n with h10 | h10
          · -- n > 412950249672860267
            rcases Nat.lt_or_ge 414119323860596311 n with h12 | h12
            · -- n > 414119323860596311
              exact RamareSaouter2003.prime_interval_nat_ladder_c06731 n (by omega) (by omega)
            · -- n <= 414119323860596311
              exact RamareSaouter2003.prime_interval_nat_ladder_c06730 n (by omega) (by omega)
          · -- n <= 412950249672860267
            exact RamareSaouter2003.prime_interval_nat_ladder_c06729 n (by omega) (by omega)
        · -- n <= 411784380843428183
          rcases Nat.lt_or_ge 409462574823330107 n with h10 | h10
          · -- n > 409462574823330107
            rcases Nat.lt_or_ge 410621842790988797 n with h12 | h12
            · -- n > 410621842790988797
              exact RamareSaouter2003.prime_interval_nat_ladder_c06728 n (by omega) (by omega)
            · -- n <= 410621842790988797
              exact RamareSaouter2003.prime_interval_nat_ladder_c06727 n (by omega) (by omega)
          · -- n <= 409462574823330107
            exact RamareSaouter2003.prime_interval_nat_ladder_c06726 n (by omega) (by omega)
  · -- n <= 408306544270352837
    rcases Nat.lt_or_ge 393571863333488401 n with h4 | h4
    · -- n > 393571863333488401
      rcases Nat.lt_or_ge 400305229951413461 n with h6 | h6
      · -- n > 400305229951413461
        rcases Nat.lt_or_ge 403714999367852093 n with h8 | h8
        · -- n > 403714999367852093
          rcases Nat.lt_or_ge 406004290835229721 n with h10 | h10
          · -- n > 406004290835229721
            rcases Nat.lt_or_ge 407153796752746061 n with h12 | h12
            · -- n > 407153796752746061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06725 n (by omega) (by omega)
            · -- n <= 407153796752746061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06724 n (by omega) (by omega)
          · -- n <= 406004290835229721
            rcases Nat.lt_or_ge 404858022213896579 n with h12 | h12
            · -- n > 404858022213896579
              exact RamareSaouter2003.prime_interval_nat_ladder_c06723 n (by omega) (by omega)
            · -- n <= 404858022213896579
              exact RamareSaouter2003.prime_interval_nat_ladder_c06722 n (by omega) (by omega)
        · -- n <= 403714999367852093
          rcases Nat.lt_or_ge 401438596107862909 n with h10 | h10
          · -- n > 401438596107862909
            rcases Nat.lt_or_ge 402575191242375947 n with h12 | h12
            · -- n > 402575191242375947
              exact RamareSaouter2003.prime_interval_nat_ladder_c06721 n (by omega) (by omega)
            · -- n <= 402575191242375947
              exact RamareSaouter2003.prime_interval_nat_ladder_c06720 n (by omega) (by omega)
          · -- n <= 401438596107862909
            exact RamareSaouter2003.prime_interval_nat_ladder_c06719 n (by omega) (by omega)
      · -- n <= 400305229951413461
        rcases Nat.lt_or_ge 396924270230393299 n with h8 | h8
        · -- n > 396924270230393299
          rcases Nat.lt_or_ge 398048068734540073 n with h10 | h10
          · -- n > 398048068734540073
            rcases Nat.lt_or_ge 399175059362220497 n with h12 | h12
            · -- n > 399175059362220497
              exact RamareSaouter2003.prime_interval_nat_ladder_c06718 n (by omega) (by omega)
            · -- n <= 399175059362220497
              exact RamareSaouter2003.prime_interval_nat_ladder_c06717 n (by omega) (by omega)
          · -- n <= 398048068734540073
            exact RamareSaouter2003.prime_interval_nat_ladder_c06716 n (by omega) (by omega)
        · -- n <= 396924270230393299
          rcases Nat.lt_or_ge 394686173577508523 n with h10 | h10
          · -- n > 394686173577508523
            rcases Nat.lt_or_ge 395803647090965719 n with h12 | h12
            · -- n > 395803647090965719
              exact RamareSaouter2003.prime_interval_nat_ladder_c06715 n (by omega) (by omega)
            · -- n <= 395803647090965719
              exact RamareSaouter2003.prime_interval_nat_ladder_c06714 n (by omega) (by omega)
          · -- n <= 394686173577508523
            exact RamareSaouter2003.prime_interval_nat_ladder_c06713 n (by omega) (by omega)
    · -- n <= 393571863333488401
      rcases Nat.lt_or_ge 386951760877669381 n with h6 | h6
      · -- n > 386951760877669381
        rcases Nat.lt_or_ge 390247754164011817 n with h8 | h8
        · -- n > 390247754164011817
          rcases Nat.lt_or_ge 391352661527256071 n with h10 | h10
          · -- n > 391352661527256071
            rcases Nat.lt_or_ge 392460700668110447 n with h12 | h12
            · -- n > 392460700668110447
              exact RamareSaouter2003.prime_interval_nat_ladder_c06712 n (by omega) (by omega)
            · -- n <= 392460700668110447
              exact RamareSaouter2003.prime_interval_nat_ladder_c06711 n (by omega) (by omega)
          · -- n <= 391352661527256071
            exact RamareSaouter2003.prime_interval_nat_ladder_c06710 n (by omega) (by omega)
        · -- n <= 390247754164011817
          rcases Nat.lt_or_ge 388047318656147659 n with h10 | h10
          · -- n > 388047318656147659
            rcases Nat.lt_or_ge 389145998359065421 n with h12 | h12
            · -- n > 389145998359065421
              exact RamareSaouter2003.prime_interval_nat_ladder_c06709 n (by omega) (by omega)
            · -- n <= 389145998359065421
              exact RamareSaouter2003.prime_interval_nat_ladder_c06708 n (by omega) (by omega)
          · -- n <= 388047318656147659
            exact RamareSaouter2003.prime_interval_nat_ladder_c06707 n (by omega) (by omega)
      · -- n <= 386951760877669381
        rcases Nat.lt_or_ge 383683599387581149 n with h8 | h8
        · -- n > 383683599387581149
          rcases Nat.lt_or_ge 384769904083925471 n with h10 | h10
          · -- n > 384769904083925471
            rcases Nat.lt_or_ge 385859297375747059 n with h12 | h12
            · -- n > 385859297375747059
              exact RamareSaouter2003.prime_interval_nat_ladder_c06706 n (by omega) (by omega)
            · -- n <= 385859297375747059
              exact RamareSaouter2003.prime_interval_nat_ladder_c06705 n (by omega) (by omega)
          · -- n <= 384769904083925471
            exact RamareSaouter2003.prime_interval_nat_ladder_c06704 n (by omega) (by omega)
        · -- n <= 383683599387581149
          rcases Nat.lt_or_ge 381520173771939739 n with h10 | h10
          · -- n > 381520173771939739
            rcases Nat.lt_or_ge 382600354403736797 n with h12 | h12
            · -- n > 382600354403736797
              exact RamareSaouter2003.prime_interval_nat_ladder_c06703 n (by omega) (by omega)
            · -- n <= 382600354403736797
              exact RamareSaouter2003.prime_interval_nat_ladder_c06702 n (by omega) (by omega)
          · -- n <= 381520173771939739
            exact RamareSaouter2003.prime_interval_nat_ladder_c06701 n (by omega) (by omega)
