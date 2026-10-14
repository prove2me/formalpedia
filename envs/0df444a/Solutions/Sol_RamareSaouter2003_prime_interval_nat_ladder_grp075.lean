-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp075
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T06:53:58.092436+00:00
-- url     : https://prove2.me/submissions/3b16b171-f668-41dc-94b4-d3c80959d6bc

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03717
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03737
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03750

theorem solution (n : Nat)
    (hn : 85608001936621 < n) (hupper : n <= 96869306228069) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 91064744852701 n with h2 | h2
  · -- n > 91064744852701
    rcases Nat.lt_or_ge 93806193625769 n with h4 | h4
    · -- n > 93806193625769
      rcases Nat.lt_or_ge 95207713075949 n with h6 | h6
      · -- n > 95207713075949
        rcases Nat.lt_or_ge 95916305677081 n with h8 | h8
        · -- n > 95916305677081
          rcases Nat.lt_or_ge 96391628199077 n with h10 | h10
          · -- n > 96391628199077
            rcases Nat.lt_or_ge 96630172047049 n with h12 | h12
            · -- n > 96630172047049
              exact RamareSaouter2003.prime_interval_nat_ladder_c03750 n (by omega) (by omega)
            · -- n <= 96630172047049
              exact RamareSaouter2003.prime_interval_nat_ladder_c03749 n (by omega) (by omega)
          · -- n <= 96391628199077
            rcases Nat.lt_or_ge 96153673226911 n with h12 | h12
            · -- n > 96153673226911
              exact RamareSaouter2003.prime_interval_nat_ladder_c03748 n (by omega) (by omega)
            · -- n <= 96153673226911
              exact RamareSaouter2003.prime_interval_nat_ladder_c03747 n (by omega) (by omega)
        · -- n <= 95916305677081
          rcases Nat.lt_or_ge 95443327046311 n with h10 | h10
          · -- n > 95443327046311
            rcases Nat.lt_or_ge 95679524099041 n with h12 | h12
            · -- n > 95679524099041
              exact RamareSaouter2003.prime_interval_nat_ladder_c03746 n (by omega) (by omega)
            · -- n <= 95679524099041
              exact RamareSaouter2003.prime_interval_nat_ladder_c03745 n (by omega) (by omega)
          · -- n <= 95443327046311
            exact RamareSaouter2003.prime_interval_nat_ladder_c03744 n (by omega) (by omega)
      · -- n <= 95207713075949
        rcases Nat.lt_or_ge 94504355283007 n with h8 | h8
        · -- n > 94504355283007
          rcases Nat.lt_or_ge 94738228628357 n with h10 | h10
          · -- n > 94738228628357
            rcases Nat.lt_or_ge 94972680748549 n with h12 | h12
            · -- n > 94972680748549
              exact RamareSaouter2003.prime_interval_nat_ladder_c03743 n (by omega) (by omega)
            · -- n <= 94972680748549
              exact RamareSaouter2003.prime_interval_nat_ladder_c03742 n (by omega) (by omega)
          · -- n <= 94738228628357
            exact RamareSaouter2003.prime_interval_nat_ladder_c03741 n (by omega) (by omega)
        · -- n <= 94504355283007
          rcases Nat.lt_or_ge 94038339205219 n with h10 | h10
          · -- n > 94038339205219
            rcases Nat.lt_or_ge 94271059283689 n with h12 | h12
            · -- n > 94271059283689
              exact RamareSaouter2003.prime_interval_nat_ladder_c03740 n (by omega) (by omega)
            · -- n <= 94271059283689
              exact RamareSaouter2003.prime_interval_nat_ladder_c03739 n (by omega) (by omega)
          · -- n <= 94038339205219
            exact RamareSaouter2003.prime_interval_nat_ladder_c03738 n (by omega) (by omega)
    · -- n <= 93806193625769
      rcases Nat.lt_or_ge 92425305453301 n with h6 | h6
      · -- n > 92425305453301
        rcases Nat.lt_or_ge 93113189717113 n with h8 | h8
        · -- n > 93113189717113
          rcases Nat.lt_or_ge 93343620294493 n with h10 | h10
          · -- n > 93343620294493
            rcases Nat.lt_or_ge 93574621127069 n with h12 | h12
            · -- n > 93574621127069
              exact RamareSaouter2003.prime_interval_nat_ladder_c03737 n (by omega) (by omega)
            · -- n <= 93574621127069
              exact RamareSaouter2003.prime_interval_nat_ladder_c03736 n (by omega) (by omega)
          · -- n <= 93343620294493
            exact RamareSaouter2003.prime_interval_nat_ladder_c03735 n (by omega) (by omega)
        · -- n <= 93113189717113
          rcases Nat.lt_or_ge 92654033698879 n with h10 | h10
          · -- n > 92654033698879
            rcases Nat.lt_or_ge 92883327986569 n with h12 | h12
            · -- n > 92883327986569
              exact RamareSaouter2003.prime_interval_nat_ladder_c03734 n (by omega) (by omega)
            · -- n <= 92883327986569
              exact RamareSaouter2003.prime_interval_nat_ladder_c03733 n (by omega) (by omega)
          · -- n <= 92654033698879
            exact RamareSaouter2003.prime_interval_nat_ladder_c03732 n (by omega) (by omega)
      · -- n <= 92425305453301
        rcases Nat.lt_or_ge 91742503012807 n with h8 | h8
        · -- n > 91742503012807
          rcases Nat.lt_or_ge 91969541502361 n with h10 | h10
          · -- n > 91969541502361
            rcases Nat.lt_or_ge 92197141852411 n with h12 | h12
            · -- n > 92197141852411
              exact RamareSaouter2003.prime_interval_nat_ladder_c03731 n (by omega) (by omega)
            · -- n <= 92197141852411
              exact RamareSaouter2003.prime_interval_nat_ladder_c03730 n (by omega) (by omega)
          · -- n <= 91969541502361
            exact RamareSaouter2003.prime_interval_nat_ladder_c03729 n (by omega) (by omega)
        · -- n <= 91742503012807
          rcases Nat.lt_or_ge 91290106069819 n with h10 | h10
          · -- n > 91290106069819
            rcases Nat.lt_or_ge 91516024996453 n with h12 | h12
            · -- n > 91516024996453
              exact RamareSaouter2003.prime_interval_nat_ladder_c03728 n (by omega) (by omega)
            · -- n <= 91516024996453
              exact RamareSaouter2003.prime_interval_nat_ladder_c03727 n (by omega) (by omega)
          · -- n <= 91290106069819
            exact RamareSaouter2003.prime_interval_nat_ladder_c03726 n (by omega) (by omega)
  · -- n <= 91064744852701
    rcases Nat.lt_or_ge 88185178781671 n with h4 | h4
    · -- n > 88185178781671
      rcases Nat.lt_or_ge 89502716978929 n with h6 | h6
      · -- n > 89502716978929
        rcases Nat.lt_or_ge 90168849595523 n with h8 | h8
        · -- n > 90168849595523
          rcases Nat.lt_or_ge 90615690043477 n with h10 | h10
          · -- n > 90615690043477
            rcases Nat.lt_or_ge 90839939968397 n with h12 | h12
            · -- n > 90839939968397
              exact RamareSaouter2003.prime_interval_nat_ladder_c03725 n (by omega) (by omega)
            · -- n <= 90839939968397
              exact RamareSaouter2003.prime_interval_nat_ladder_c03724 n (by omega) (by omega)
          · -- n <= 90615690043477
            rcases Nat.lt_or_ge 90391993708097 n with h12 | h12
            · -- n > 90391993708097
              exact RamareSaouter2003.prime_interval_nat_ladder_c03723 n (by omega) (by omega)
            · -- n <= 90391993708097
              exact RamareSaouter2003.prime_interval_nat_ladder_c03722 n (by omega) (by omega)
        · -- n <= 90168849595523
          rcases Nat.lt_or_ge 89724212589061 n with h10 | h10
          · -- n > 89724212589061
            rcases Nat.lt_or_ge 89946256342451 n with h12 | h12
            · -- n > 89946256342451
              exact RamareSaouter2003.prime_interval_nat_ladder_c03721 n (by omega) (by omega)
            · -- n <= 89946256342451
              exact RamareSaouter2003.prime_interval_nat_ladder_c03720 n (by omega) (by omega)
          · -- n <= 89724212589061
            exact RamareSaouter2003.prime_interval_nat_ladder_c03719 n (by omega) (by omega)
      · -- n <= 89502716978929
        rcases Nat.lt_or_ge 88841505492721 n with h8 | h8
        · -- n > 88841505492721
          rcases Nat.lt_or_ge 89061364778977 n with h10 | h10
          · -- n > 89061364778977
            rcases Nat.lt_or_ge 89281768158839 n with h12 | h12
            · -- n > 89281768158839
              exact RamareSaouter2003.prime_interval_nat_ladder_c03718 n (by omega) (by omega)
            · -- n <= 89281768158839
              exact RamareSaouter2003.prime_interval_nat_ladder_c03717 n (by omega) (by omega)
          · -- n <= 89061364778977
            exact RamareSaouter2003.prime_interval_nat_ladder_c03716 n (by omega) (by omega)
        · -- n <= 88841505492721
          rcases Nat.lt_or_ge 88403413832483 n with h10 | h10
          · -- n > 88403413832483
            rcases Nat.lt_or_ge 88622188957387 n with h12 | h12
            · -- n > 88622188957387
              exact RamareSaouter2003.prime_interval_nat_ladder_c03715 n (by omega) (by omega)
            · -- n <= 88622188957387
              exact RamareSaouter2003.prime_interval_nat_ladder_c03714 n (by omega) (by omega)
          · -- n <= 88403413832483
            exact RamareSaouter2003.prime_interval_nat_ladder_c03713 n (by omega) (by omega)
    · -- n <= 88185178781671
      rcases Nat.lt_or_ge 86887035603551 n with h6 | h6
      · -- n > 86887035603551
        rcases Nat.lt_or_ge 87533700758459 n with h8 | h8
        · -- n > 87533700758459
          rcases Nat.lt_or_ge 87750323573069 n with h10 | h10
          · -- n > 87750323573069
            rcases Nat.lt_or_ge 87967482471839 n with h12 | h12
            · -- n > 87967482471839
              exact RamareSaouter2003.prime_interval_nat_ladder_c03712 n (by omega) (by omega)
            · -- n <= 87967482471839
              exact RamareSaouter2003.prime_interval_nat_ladder_c03711 n (by omega) (by omega)
          · -- n <= 87750323573069
            exact RamareSaouter2003.prime_interval_nat_ladder_c03710 n (by omega) (by omega)
        · -- n <= 87533700758459
          rcases Nat.lt_or_ge 87102058092359 n with h10 | h10
          · -- n > 87102058092359
            rcases Nat.lt_or_ge 87317612704877 n with h12 | h12
            · -- n > 87317612704877
              exact RamareSaouter2003.prime_interval_nat_ladder_c03709 n (by omega) (by omega)
            · -- n <= 87317612704877
              exact RamareSaouter2003.prime_interval_nat_ladder_c03708 n (by omega) (by omega)
          · -- n <= 87102058092359
            exact RamareSaouter2003.prime_interval_nat_ladder_c03707 n (by omega) (by omega)
      · -- n <= 86887035603551
        rcases Nat.lt_or_ge 86245147760423 n with h8 | h8
        · -- n > 86245147760423
          rcases Nat.lt_or_ge 86458581746279 n with h10 | h10
          · -- n > 86458581746279
            rcases Nat.lt_or_ge 86672543924909 n with h12 | h12
            · -- n > 86672543924909
              exact RamareSaouter2003.prime_interval_nat_ladder_c03706 n (by omega) (by omega)
            · -- n <= 86672543924909
              exact RamareSaouter2003.prime_interval_nat_ladder_c03705 n (by omega) (by omega)
          · -- n <= 86458581746279
            exact RamareSaouter2003.prime_interval_nat_ladder_c03704 n (by omega) (by omega)
        · -- n <= 86245147760423
          rcases Nat.lt_or_ge 85819859154719 n with h10 | h10
          · -- n > 85819859154719
            rcases Nat.lt_or_ge 86032240663507 n with h12 | h12
            · -- n > 86032240663507
              exact RamareSaouter2003.prime_interval_nat_ladder_c03703 n (by omega) (by omega)
            · -- n <= 86032240663507
              exact RamareSaouter2003.prime_interval_nat_ladder_c03702 n (by omega) (by omega)
          · -- n <= 85819859154719
            exact RamareSaouter2003.prime_interval_nat_ladder_c03701 n (by omega) (by omega)
