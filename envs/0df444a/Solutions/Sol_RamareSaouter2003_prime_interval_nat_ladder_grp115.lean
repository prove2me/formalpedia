-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp115
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T18:11:56.1124+00:00
-- url     : https://prove2.me/submissions/8cb0110c-d0f5-41c3-9d76-18deeabf8cf4

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05717
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05737
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05750

theorem solution (n : Nat)
    (hn : 22514638705499333 < n) (hupper : n <= 25933117750214453) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 24163532000089451 n with h2 | h2
  · -- n > 24163532000089451
    rcases Nat.lt_or_ge 24997349999178077 n with h4 | h4
    · -- n > 24997349999178077
      rcases Nat.lt_or_ge 25424973330271393 n with h6 | h6
      · -- n > 25424973330271393
        rcases Nat.lt_or_ge 25641526417490897 n with h8 | h8
        · -- n > 25641526417490897
          rcases Nat.lt_or_ge 25786917049266031 n with h10 | h10
          · -- n > 25786917049266031
            rcases Nat.lt_or_ge 25859904140887591 n with h12 | h12
            · -- n > 25859904140887591
              exact RamareSaouter2003.prime_interval_nat_ladder_c05750 n (by omega) (by omega)
            · -- n <= 25859904140887591
              exact RamareSaouter2003.prime_interval_nat_ladder_c05749 n (by omega) (by omega)
          · -- n <= 25786917049266031
            rcases Nat.lt_or_ge 25714119031836979 n with h12 | h12
            · -- n > 25714119031836979
              exact RamareSaouter2003.prime_interval_nat_ladder_c05748 n (by omega) (by omega)
            · -- n <= 25714119031836979
              exact RamareSaouter2003.prime_interval_nat_ladder_c05747 n (by omega) (by omega)
        · -- n <= 25641526417490897
          rcases Nat.lt_or_ge 25496953994739193 n with h10 | h10
          · -- n > 25496953994739193
            rcases Nat.lt_or_ge 25569142591659313 n with h12 | h12
            · -- n > 25569142591659313
              exact RamareSaouter2003.prime_interval_nat_ladder_c05746 n (by omega) (by omega)
            · -- n <= 25569142591659313
              exact RamareSaouter2003.prime_interval_nat_ladder_c05745 n (by omega) (by omega)
          · -- n <= 25496953994739193
            exact RamareSaouter2003.prime_interval_nat_ladder_c05744 n (by omega) (by omega)
      · -- n <= 25424973330271393
        rcases Nat.lt_or_ge 25210260103122803 n with h8 | h8
        · -- n > 25210260103122803
          rcases Nat.lt_or_ge 25281625389662641 n with h10 | h10
          · -- n > 25281625389662641
            rcases Nat.lt_or_ge 25353203957943931 n with h12 | h12
            · -- n > 25353203957943931
              exact RamareSaouter2003.prime_interval_nat_ladder_c05743 n (by omega) (by omega)
            · -- n <= 25353203957943931
              exact RamareSaouter2003.prime_interval_nat_ladder_c05742 n (by omega) (by omega)
          · -- n <= 25281625389662641
            exact RamareSaouter2003.prime_interval_nat_ladder_c05741 n (by omega) (by omega)
        · -- n <= 25210260103122803
          rcases Nat.lt_or_ge 25068113303762759 n with h10 | h10
          · -- n > 25068113303762759
            rcases Nat.lt_or_ge 25139084787534527 n with h12 | h12
            · -- n > 25139084787534527
              exact RamareSaouter2003.prime_interval_nat_ladder_c05740 n (by omega) (by omega)
            · -- n <= 25139084787534527
              exact RamareSaouter2003.prime_interval_nat_ladder_c05739 n (by omega) (by omega)
          · -- n <= 25068113303762759
            exact RamareSaouter2003.prime_interval_nat_ladder_c05738 n (by omega) (by omega)
    · -- n <= 24997349999178077
      rcases Nat.lt_or_ge 24576900591616649 n with h6 | h6
      · -- n > 24576900591616649
        rcases Nat.lt_or_ge 24786237623306371 n with h8 | h8
        · -- n > 24786237623306371
          rcases Nat.lt_or_ge 24856410669360689 n with h10 | h10
          · -- n > 24856410669360689
            rcases Nat.lt_or_ge 24926775414350111 n with h12 | h12
            · -- n > 24926775414350111
              exact RamareSaouter2003.prime_interval_nat_ladder_c05737 n (by omega) (by omega)
            · -- n <= 24926775414350111
              exact RamareSaouter2003.prime_interval_nat_ladder_c05736 n (by omega) (by omega)
          · -- n <= 24856410669360689
            exact RamareSaouter2003.prime_interval_nat_ladder_c05735 n (by omega) (by omega)
        · -- n <= 24786237623306371
          rcases Nat.lt_or_ge 24646480492667921 n with h10 | h10
          · -- n > 24646480492667921
            rcases Nat.lt_or_ge 24716261559221377 n with h12 | h12
            · -- n > 24716261559221377
              exact RamareSaouter2003.prime_interval_nat_ladder_c05734 n (by omega) (by omega)
            · -- n <= 24716261559221377
              exact RamareSaouter2003.prime_interval_nat_ladder_c05733 n (by omega) (by omega)
          · -- n <= 24646480492667921
            exact RamareSaouter2003.prime_interval_nat_ladder_c05732 n (by omega) (by omega)
      · -- n <= 24576900591616649
        rcases Nat.lt_or_ge 24369338309532763 n with h8 | h8
        · -- n > 24369338309532763
          rcases Nat.lt_or_ge 24438334146457409 n with h10 | h10
          · -- n > 24438334146457409
            rcases Nat.lt_or_ge 24507523004183567 n with h12 | h12
            · -- n > 24507523004183567
              exact RamareSaouter2003.prime_interval_nat_ladder_c05731 n (by omega) (by omega)
            · -- n <= 24507523004183567
              exact RamareSaouter2003.prime_interval_nat_ladder_c05730 n (by omega) (by omega)
          · -- n <= 24438334146457409
            exact RamareSaouter2003.prime_interval_nat_ladder_c05729 n (by omega) (by omega)
        · -- n <= 24369338309532763
          rcases Nat.lt_or_ge 24231940618848383 n with h10 | h10
          · -- n > 24231940618848383
            rcases Nat.lt_or_ge 24300541632633709 n with h12 | h12
            · -- n > 24300541632633709
              exact RamareSaouter2003.prime_interval_nat_ladder_c05728 n (by omega) (by omega)
            · -- n <= 24300541632633709
              exact RamareSaouter2003.prime_interval_nat_ladder_c05727 n (by omega) (by omega)
          · -- n <= 24231940618848383
            exact RamareSaouter2003.prime_interval_nat_ladder_c05726 n (by omega) (by omega)
  · -- n <= 24163532000089451
    rcases Nat.lt_or_ge 23291587120501309 n with h4 | h4
    · -- n > 23291587120501309
      rcases Nat.lt_or_ge 23690042169235877 n with h6 | h6
      · -- n > 23690042169235877
        rcases Nat.lt_or_ge 23891825913334553 n with h8 | h8
        · -- n > 23891825913334553
          rcases Nat.lt_or_ge 24027289442569079 n with h10 | h10
          · -- n > 24027289442569079
            rcases Nat.lt_or_ge 24095313524528041 n with h12 | h12
            · -- n > 24095313524528041
              exact RamareSaouter2003.prime_interval_nat_ladder_c05725 n (by omega) (by omega)
            · -- n <= 24095313524528041
              exact RamareSaouter2003.prime_interval_nat_ladder_c05724 n (by omega) (by omega)
          · -- n <= 24027289442569079
            rcases Nat.lt_or_ge 23959461201533159 n with h12 | h12
            · -- n > 23959461201533159
              exact RamareSaouter2003.prime_interval_nat_ladder_c05723 n (by omega) (by omega)
            · -- n <= 23959461201533159
              exact RamareSaouter2003.prime_interval_nat_ladder_c05722 n (by omega) (by omega)
        · -- n <= 23891825913334553
          rcases Nat.lt_or_ge 23757115861789381 n with h10 | h10
          · -- n > 23757115861789381
            rcases Nat.lt_or_ge 23824372960775903 n with h12 | h12
            · -- n > 23824372960775903
              exact RamareSaouter2003.prime_interval_nat_ladder_c05721 n (by omega) (by omega)
            · -- n <= 23824372960775903
              exact RamareSaouter2003.prime_interval_nat_ladder_c05720 n (by omega) (by omega)
          · -- n <= 23757115861789381
            exact RamareSaouter2003.prime_interval_nat_ladder_c05719 n (by omega) (by omega)
      · -- n <= 23690042169235877
        rcases Nat.lt_or_ge 23489967527699891 n with h8 | h8
        · -- n > 23489967527699891
          rcases Nat.lt_or_ge 23556467490959057 n with h10 | h10
          · -- n > 23556467490959057
            rcases Nat.lt_or_ge 23623159210801387 n with h12 | h12
            · -- n > 23623159210801387
              exact RamareSaouter2003.prime_interval_nat_ladder_c05718 n (by omega) (by omega)
            · -- n <= 23623159210801387
              exact RamareSaouter2003.prime_interval_nat_ladder_c05717 n (by omega) (by omega)
          · -- n <= 23556467490959057
            exact RamareSaouter2003.prime_interval_nat_ladder_c05716 n (by omega) (by omega)
        · -- n <= 23489967527699891
          rcases Nat.lt_or_ge 23357523746515711 n with h10 | h10
          · -- n > 23357523746515711
            rcases Nat.lt_or_ge 23423648789513891 n with h12 | h12
            · -- n > 23423648789513891
              exact RamareSaouter2003.prime_interval_nat_ladder_c05715 n (by omega) (by omega)
            · -- n <= 23423648789513891
              exact RamareSaouter2003.prime_interval_nat_ladder_c05714 n (by omega) (by omega)
          · -- n <= 23357523746515711
            exact RamareSaouter2003.prime_interval_nat_ladder_c05713 n (by omega) (by omega)
    · -- n <= 23291587120501309
      rcases Nat.lt_or_ge 22899810554871247 n with h6 | h6
      · -- n > 22899810554871247
        rcases Nat.lt_or_ge 23094868899080939 n with h8 | h8
        · -- n > 23094868899080939
          rcases Nat.lt_or_ge 23160256111447811 n with h10 | h10
          · -- n > 23160256111447811
            rcases Nat.lt_or_ge 23225829023010829 n with h12 | h12
            · -- n > 23225829023010829
              exact RamareSaouter2003.prime_interval_nat_ladder_c05712 n (by omega) (by omega)
            · -- n <= 23225829023010829
              exact RamareSaouter2003.prime_interval_nat_ladder_c05711 n (by omega) (by omega)
          · -- n <= 23160256111447811
            exact RamareSaouter2003.prime_interval_nat_ladder_c05710 n (by omega) (by omega)
        · -- n <= 23094868899080939
          rcases Nat.lt_or_ge 22964646364015781 n with h10 | h10
          · -- n > 22964646364015781
            rcases Nat.lt_or_ge 23029665472602049 n with h12 | h12
            · -- n > 23029665472602049
              exact RamareSaouter2003.prime_interval_nat_ladder_c05709 n (by omega) (by omega)
            · -- n <= 23029665472602049
              exact RamareSaouter2003.prime_interval_nat_ladder_c05708 n (by omega) (by omega)
          · -- n <= 22964646364015781
            exact RamareSaouter2003.prime_interval_nat_ladder_c05707 n (by omega) (by omega)
      · -- n <= 22899810554871247
        rcases Nat.lt_or_ge 22706407313780987 n with h8 | h8
        · -- n > 22706407313780987
          rcases Nat.lt_or_ge 22770692794370999 n with h10 | h10
          · -- n > 22770692794370999
            rcases Nat.lt_or_ge 22835162226846833 n with h12 | h12
            · -- n > 22835162226846833
              exact RamareSaouter2003.prime_interval_nat_ladder_c05706 n (by omega) (by omega)
            · -- n <= 22835162226846833
              exact RamareSaouter2003.prime_interval_nat_ladder_c05705 n (by omega) (by omega)
          · -- n <= 22770692794370999
            exact RamareSaouter2003.prime_interval_nat_ladder_c05704 n (by omega) (by omega)
        · -- n <= 22706407313780987
          rcases Nat.lt_or_ge 22578374948523467 n with h10 | h10
          · -- n > 22578374948523467
            rcases Nat.lt_or_ge 22642300884651737 n with h12 | h12
            · -- n > 22642300884651737
              exact RamareSaouter2003.prime_interval_nat_ladder_c05703 n (by omega) (by omega)
            · -- n <= 22642300884651737
              exact RamareSaouter2003.prime_interval_nat_ladder_c05702 n (by omega) (by omega)
          · -- n <= 22578374948523467
            exact RamareSaouter2003.prime_interval_nat_ladder_c05701 n (by omega) (by omega)
