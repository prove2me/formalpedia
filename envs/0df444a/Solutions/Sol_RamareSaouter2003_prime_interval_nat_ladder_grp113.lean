-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp113
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T17:50:11.227423+00:00
-- url     : https://prove2.me/submissions/06e790af-c532-4c46-94a8-d6a6f9aa8545

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05619
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05639
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05650

theorem solution (n : Nat)
    (hn : 16970173954204477 < n) (hupper : n <= 19546801688263991) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 18212976887651869 n with h2 | h2
  · -- n > 18212976887651869
    rcases Nat.lt_or_ge 18841477167588737 n with h4 | h4
    · -- n > 18841477167588737
      rcases Nat.lt_or_ge 19163804346198719 n with h6 | h6
      · -- n > 19163804346198719
        rcases Nat.lt_or_ge 19327024480032233 n with h8 | h8
        · -- n > 19327024480032233
          rcases Nat.lt_or_ge 19436614465920647 n with h10 | h10
          · -- n > 19436614465920647
            rcases Nat.lt_or_ge 19491642910029743 n with h12 | h12
            · -- n > 19491642910029743
              exact RamareSaouter2003.prime_interval_nat_ladder_c05650 n (by omega) (by omega)
            · -- n <= 19491642910029743
              exact RamareSaouter2003.prime_interval_nat_ladder_c05649 n (by omega) (by omega)
          · -- n <= 19436614465920647
            rcases Nat.lt_or_ge 19381741202920169 n with h12 | h12
            · -- n > 19381741202920169
              exact RamareSaouter2003.prime_interval_nat_ladder_c05648 n (by omega) (by omega)
            · -- n <= 19381741202920169
              exact RamareSaouter2003.prime_interval_nat_ladder_c05647 n (by omega) (by omega)
        · -- n <= 19327024480032233
          rcases Nat.lt_or_ge 19218062624754481 n with h10 | h10
          · -- n > 19218062624754481
            rcases Nat.lt_or_ge 19272463959908827 n with h12 | h12
            · -- n > 19272463959908827
              exact RamareSaouter2003.prime_interval_nat_ladder_c05646 n (by omega) (by omega)
            · -- n <= 19272463959908827
              exact RamareSaouter2003.prime_interval_nat_ladder_c05645 n (by omega) (by omega)
          · -- n <= 19218062624754481
            exact RamareSaouter2003.prime_interval_nat_ladder_c05644 n (by omega) (by omega)
      · -- n <= 19163804346198719
        rcases Nat.lt_or_ge 19001955100309801 n with h8 | h8
        · -- n > 19001955100309801
          rcases Nat.lt_or_ge 19055751475398733 n with h10 | h10
          · -- n > 19055751475398733
            rcases Nat.lt_or_ge 19109700745298981 n with h12 | h12
            · -- n > 19109700745298981
              exact RamareSaouter2003.prime_interval_nat_ladder_c05643 n (by omega) (by omega)
            · -- n <= 19109700745298981
              exact RamareSaouter2003.prime_interval_nat_ladder_c05642 n (by omega) (by omega)
          · -- n <= 19055751475398733
            exact RamareSaouter2003.prime_interval_nat_ladder_c05641 n (by omega) (by omega)
        · -- n <= 19001955100309801
          rcases Nat.lt_or_ge 18894820605572851 n with h10 | h10
          · -- n > 18894820605572851
            rcases Nat.lt_or_ge 18948308844756281 n with h12 | h12
            · -- n > 18948308844756281
              exact RamareSaouter2003.prime_interval_nat_ladder_c05640 n (by omega) (by omega)
            · -- n <= 18948308844756281
              exact RamareSaouter2003.prime_interval_nat_ladder_c05639 n (by omega) (by omega)
          · -- n <= 18894820605572851
            exact RamareSaouter2003.prime_interval_nat_ladder_c05638 n (by omega) (by omega)
    · -- n <= 18841477167588737
      rcases Nat.lt_or_ge 18524568706008913 n with h6 | h6
      · -- n > 18524568706008913
        rcases Nat.lt_or_ge 18682351947004927 n with h8 | h8
        · -- n > 18682351947004927
          rcases Nat.lt_or_ge 18735244525857017 n with h10 | h10
          · -- n > 18735244525857017
            rcases Nat.lt_or_ge 18788289441938141 n with h12 | h12
            · -- n > 18788289441938141
              exact RamareSaouter2003.prime_interval_nat_ladder_c05637 n (by omega) (by omega)
            · -- n <= 18788289441938141
              exact RamareSaouter2003.prime_interval_nat_ladder_c05636 n (by omega) (by omega)
          · -- n <= 18735244525857017
            exact RamareSaouter2003.prime_interval_nat_ladder_c05635 n (by omega) (by omega)
        · -- n <= 18682351947004927
          rcases Nat.lt_or_ge 18577012723278467 n with h10 | h10
          · -- n > 18577012723278467
            rcases Nat.lt_or_ge 18629607303573727 n with h12 | h12
            · -- n > 18629607303573727
              exact RamareSaouter2003.prime_interval_nat_ladder_c05634 n (by omega) (by omega)
            · -- n <= 18629607303573727
              exact RamareSaouter2003.prime_interval_nat_ladder_c05633 n (by omega) (by omega)
          · -- n <= 18577012723278467
            exact RamareSaouter2003.prime_interval_nat_ladder_c05632 n (by omega) (by omega)
      · -- n <= 18524568706008913
        rcases Nat.lt_or_ge 18368113790688133 n with h8 | h8
        · -- n > 18368113790688133
          rcases Nat.lt_or_ge 18420116427641083 n with h10 | h10
          · -- n > 18420116427641083
            rcases Nat.lt_or_ge 18472269228562243 n with h12 | h12
            · -- n > 18472269228562243
              exact RamareSaouter2003.prime_interval_nat_ladder_c05631 n (by omega) (by omega)
            · -- n <= 18472269228562243
              exact RamareSaouter2003.prime_interval_nat_ladder_c05630 n (by omega) (by omega)
          · -- n <= 18420116427641083
            exact RamareSaouter2003.prime_interval_nat_ladder_c05629 n (by omega) (by omega)
        · -- n <= 18368113790688133
          rcases Nat.lt_or_ge 18264543369218261 n with h10 | h10
          · -- n > 18264543369218261
            rcases Nat.lt_or_ge 18316255579276981 n with h12 | h12
            · -- n > 18316255579276981
              exact RamareSaouter2003.prime_interval_nat_ladder_c05628 n (by omega) (by omega)
            · -- n <= 18316255579276981
              exact RamareSaouter2003.prime_interval_nat_ladder_c05627 n (by omega) (by omega)
          · -- n <= 18264543369218261
            exact RamareSaouter2003.prime_interval_nat_ladder_c05626 n (by omega) (by omega)
  · -- n <= 18212976887651869
    rcases Nat.lt_or_ge 17555756010339007 n with h4 | h4
    · -- n > 17555756010339007
      rcases Nat.lt_or_ge 17856082871857873 n with h6 | h6
      · -- n > 17856082871857873
        rcases Nat.lt_or_ge 18008175297861299 n with h8 | h8
        · -- n > 18008175297861299
          rcases Nat.lt_or_ge 18110287084106143 n with h10 | h10
          · -- n > 18110287084106143
            rcases Nat.lt_or_ge 18161561192948111 n with h12 | h12
            · -- n > 18161561192948111
              exact RamareSaouter2003.prime_interval_nat_ladder_c05625 n (by omega) (by omega)
            · -- n <= 18161561192948111
              exact RamareSaouter2003.prime_interval_nat_ladder_c05624 n (by omega) (by omega)
          · -- n <= 18110287084106143
            rcases Nat.lt_or_ge 18059159887964729 n with h12 | h12
            · -- n > 18059159887964729
              exact RamareSaouter2003.prime_interval_nat_ladder_c05623 n (by omega) (by omega)
            · -- n <= 18059159887964729
              exact RamareSaouter2003.prime_interval_nat_ladder_c05622 n (by omega) (by omega)
        · -- n <= 18008175297861299
          rcases Nat.lt_or_ge 17906637493731893 n with h10 | h10
          · -- n > 17906637493731893
            rcases Nat.lt_or_ge 17957335134186001 n with h12 | h12
            · -- n > 17957335134186001
              exact RamareSaouter2003.prime_interval_nat_ladder_c05621 n (by omega) (by omega)
            · -- n <= 17957335134186001
              exact RamareSaouter2003.prime_interval_nat_ladder_c05620 n (by omega) (by omega)
          · -- n <= 17906637493731893
            exact RamareSaouter2003.prime_interval_nat_ladder_c05619 n (by omega) (by omega)
      · -- n <= 17856082871857873
        rcases Nat.lt_or_ge 17705286372272039 n with h8 | h8
        · -- n > 17705286372272039
          rcases Nat.lt_or_ge 17755402553968213 n with h10 | h10
          · -- n > 17755402553968213
            rcases Nat.lt_or_ge 17805672574751069 n with h12 | h12
            · -- n > 17805672574751069
              exact RamareSaouter2003.prime_interval_nat_ladder_c05618 n (by omega) (by omega)
            · -- n <= 17805672574751069
              exact RamareSaouter2003.prime_interval_nat_ladder_c05617 n (by omega) (by omega)
          · -- n <= 17755402553968213
            exact RamareSaouter2003.prime_interval_nat_ladder_c05616 n (by omega) (by omega)
        · -- n <= 17705286372272039
          rcases Nat.lt_or_ge 17605456483883053 n with h10 | h10
          · -- n > 17605456483883053
            rcases Nat.lt_or_ge 17655299203984693 n with h12 | h12
            · -- n > 17655299203984693
              exact RamareSaouter2003.prime_interval_nat_ladder_c05615 n (by omega) (by omega)
            · -- n <= 17655299203984693
              exact RamareSaouter2003.prime_interval_nat_ladder_c05614 n (by omega) (by omega)
          · -- n <= 17605456483883053
            exact RamareSaouter2003.prime_interval_nat_ladder_c05613 n (by omega) (by omega)
    · -- n <= 17555756010339007
      rcases Nat.lt_or_ge 17260491587692387 n with h6 | h6
      · -- n > 17260491587692387
        rcases Nat.lt_or_ge 17407499155163473 n with h8 | h8
        · -- n > 17407499155163473
          rcases Nat.lt_or_ge 17456783868942749 n with h10 | h10
          · -- n > 17456783868942749
            rcases Nat.lt_or_ge 17506203880486411 n with h12 | h12
            · -- n > 17506203880486411
              exact RamareSaouter2003.prime_interval_nat_ladder_c05612 n (by omega) (by omega)
            · -- n <= 17506203880486411
              exact RamareSaouter2003.prime_interval_nat_ladder_c05611 n (by omega) (by omega)
          · -- n <= 17456783868942749
            exact RamareSaouter2003.prime_interval_nat_ladder_c05610 n (by omega) (by omega)
        · -- n <= 17407499155163473
          rcases Nat.lt_or_ge 17309358187571959 n with h10 | h10
          · -- n > 17309358187571959
            rcases Nat.lt_or_ge 17358358150270177 n with h12 | h12
            · -- n > 17358358150270177
              exact RamareSaouter2003.prime_interval_nat_ladder_c05609 n (by omega) (by omega)
            · -- n <= 17358358150270177
              exact RamareSaouter2003.prime_interval_nat_ladder_c05608 n (by omega) (by omega)
          · -- n <= 17309358187571959
            exact RamareSaouter2003.prime_interval_nat_ladder_c05607 n (by omega) (by omega)
      · -- n <= 17260491587692387
        rcases Nat.lt_or_ge 17114717549666923 n with h8 | h8
        · -- n > 17114717549666923
          rcases Nat.lt_or_ge 17163173127390569 n with h10 | h10
          · -- n > 17163173127390569
            rcases Nat.lt_or_ge 17211760175061241 n with h12 | h12
            · -- n > 17211760175061241
              exact RamareSaouter2003.prime_interval_nat_ladder_c05606 n (by omega) (by omega)
            · -- n <= 17211760175061241
              exact RamareSaouter2003.prime_interval_nat_ladder_c05605 n (by omega) (by omega)
          · -- n <= 17163173127390569
            exact RamareSaouter2003.prime_interval_nat_ladder_c05604 n (by omega) (by omega)
        · -- n <= 17114717549666923
          rcases Nat.lt_or_ge 17018221643226697 n with h10 | h10
          · -- n > 17018221643226697
            rcases Nat.lt_or_ge 17066397869765599 n with h12 | h12
            · -- n > 17066397869765599
              exact RamareSaouter2003.prime_interval_nat_ladder_c05603 n (by omega) (by omega)
            · -- n <= 17066397869765599
              exact RamareSaouter2003.prime_interval_nat_ladder_c05602 n (by omega) (by omega)
          · -- n <= 17018221643226697
            exact RamareSaouter2003.prime_interval_nat_ladder_c05601 n (by omega) (by omega)
