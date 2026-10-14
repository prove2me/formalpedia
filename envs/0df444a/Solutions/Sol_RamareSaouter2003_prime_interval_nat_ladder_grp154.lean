-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp154
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T08:49:52.750201+00:00
-- url     : https://prove2.me/submissions/b9871156-295d-460e-bc62-df162537354d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07650
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07668
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07688

theorem solution (n : Nat)
    (hn : 5410770793340726459 < n) (hupper : n <= 6214769977508183639) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 5790661989956173823 n with h2 | h2
  · -- n > 5790661989956173823
    rcases Nat.lt_or_ge 5990494422654211727 n with h4 | h4
    · -- n > 5990494422654211727
      rcases Nat.lt_or_ge 6092982654733328491 n with h6 | h6
      · -- n > 6092982654733328491
        rcases Nat.lt_or_ge 6144882290382218521 n with h8 | h8
        · -- n > 6144882290382218521
          rcases Nat.lt_or_ge 6179727253866713303 n with h10 | h10
          · -- n > 6179727253866713303
            rcases Nat.lt_or_ge 6197223804011033149 n with h12 | h12
            · -- n > 6197223804011033149
              exact RamareSaouter2003.prime_interval_nat_ladder_c07688 n (by omega) (by omega)
            · -- n <= 6197223804011033149
              exact RamareSaouter2003.prime_interval_nat_ladder_c07687 n (by omega) (by omega)
          · -- n <= 6179727253866713303
            rcases Nat.lt_or_ge 6162280027951160611 n with h12 | h12
            · -- n > 6162280027951160611
              exact RamareSaouter2003.prime_interval_nat_ladder_c07686 n (by omega) (by omega)
            · -- n <= 6162280027951160611
              exact RamareSaouter2003.prime_interval_nat_ladder_c07685 n (by omega) (by omega)
        · -- n <= 6144882290382218521
          rcases Nat.lt_or_ge 6110233615516364977 n with h10 | h10
          · -- n > 6110233615516364977
            rcases Nat.lt_or_ge 6127533444551862997 n with h12 | h12
            · -- n > 6127533444551862997
              exact RamareSaouter2003.prime_interval_nat_ladder_c07684 n (by omega) (by omega)
            · -- n <= 6127533444551862997
              exact RamareSaouter2003.prime_interval_nat_ladder_c07683 n (by omega) (by omega)
          · -- n <= 6110233615516364977
            exact RamareSaouter2003.prime_interval_nat_ladder_c07682 n (by omega) (by omega)
      · -- n <= 6092982654733328491
        rcases Nat.lt_or_ge 6041521287476029909 n with h8 | h8
        · -- n > 6041521287476029909
          rcases Nat.lt_or_ge 6058626519678060037 n with h10 | h10
          · -- n > 6058626519678060037
            rcases Nat.lt_or_ge 6075780330358634219 n with h12 | h12
            · -- n > 6075780330358634219
              exact RamareSaouter2003.prime_interval_nat_ladder_c07681 n (by omega) (by omega)
            · -- n <= 6075780330358634219
              exact RamareSaouter2003.prime_interval_nat_ladder_c07680 n (by omega) (by omega)
          · -- n <= 6058626519678060037
            exact RamareSaouter2003.prime_interval_nat_ladder_c07679 n (by omega) (by omega)
        · -- n <= 6041521287476029909
          rcases Nat.lt_or_ge 6007455350594932937 n with h10 | h10
          · -- n > 6007455350594932937
            rcases Nat.lt_or_ge 6024464205932116069 n with h12 | h12
            · -- n > 6024464205932116069
              exact RamareSaouter2003.prime_interval_nat_ladder_c07678 n (by omega) (by omega)
            · -- n <= 6024464205932116069
              exact RamareSaouter2003.prime_interval_nat_ladder_c07677 n (by omega) (by omega)
          · -- n <= 6007455350594932937
            exact RamareSaouter2003.prime_interval_nat_ladder_c07676 n (by omega) (by omega)
    · -- n <= 5990494422654211727
      rcases Nat.lt_or_ge 5889731169477472817 n with h6 | h6
      · -- n > 5889731169477472817
        rcases Nat.lt_or_ge 5939899142126539229 n with h8 | h8
        · -- n > 5939899142126539229
          rcases Nat.lt_or_ge 5956716696091583927 n with h10 | h10
          · -- n > 5956716696091583927
            rcases Nat.lt_or_ge 5973581584821129857 n with h12 | h12
            · -- n > 5973581584821129857
              exact RamareSaouter2003.prime_interval_nat_ladder_c07675 n (by omega) (by omega)
            · -- n <= 5973581584821129857
              exact RamareSaouter2003.prime_interval_nat_ladder_c07674 n (by omega) (by omega)
          · -- n <= 5956716696091583927
            exact RamareSaouter2003.prime_interval_nat_ladder_c07673 n (by omega) (by omega)
        · -- n <= 5939899142126539229
          rcases Nat.lt_or_ge 5906406584103858421 n with h10 | h10
          · -- n > 5906406584103858421
            rcases Nat.lt_or_ge 5923129437320587693 n with h12 | h12
            · -- n > 5923129437320587693
              exact RamareSaouter2003.prime_interval_nat_ladder_c07672 n (by omega) (by omega)
            · -- n <= 5923129437320587693
              exact RamareSaouter2003.prime_interval_nat_ladder_c07671 n (by omega) (by omega)
          · -- n <= 5906406584103858421
            exact RamareSaouter2003.prime_interval_nat_ladder_c07670 n (by omega) (by omega)
      · -- n <= 5889731169477472817
        rcases Nat.lt_or_ge 5839986563494344067 n with h8 | h8
        · -- n > 5839986563494344067
          rcases Nat.lt_or_ge 5856521088664858219 n with h10 | h10
          · -- n > 5856521088664858219
            rcases Nat.lt_or_ge 5873102640938620289 n with h12 | h12
            · -- n > 5873102640938620289
              exact RamareSaouter2003.prime_interval_nat_ladder_c07669 n (by omega) (by omega)
            · -- n <= 5873102640938620289
              exact RamareSaouter2003.prime_interval_nat_ladder_c07668 n (by omega) (by omega)
          · -- n <= 5856521088664858219
            exact RamareSaouter2003.prime_interval_nat_ladder_c07667 n (by omega) (by omega)
        · -- n <= 5839986563494344067
          rcases Nat.lt_or_ge 5807056933924632637 n with h10 | h10
          · -- n > 5807056933924632637
            rcases Nat.lt_or_ge 5823498486697978451 n with h12 | h12
            · -- n > 5823498486697978451
              exact RamareSaouter2003.prime_interval_nat_ladder_c07666 n (by omega) (by omega)
            · -- n <= 5823498486697978451
              exact RamareSaouter2003.prime_interval_nat_ladder_c07665 n (by omega) (by omega)
          · -- n <= 5807056933924632637
            exact RamareSaouter2003.prime_interval_nat_ladder_c07664 n (by omega) (by omega)
  · -- n <= 5790661989956173823
    rcases Nat.lt_or_ge 5597494635027639439 n with h4 | h4
    · -- n > 5597494635027639439
      rcases Nat.lt_or_ge 5693259052390635073 n with h6 | h6
      · -- n > 5693259052390635073
        rcases Nat.lt_or_ge 5741753848356002297 n with h8 | h8
        · -- n > 5741753848356002297
          rcases Nat.lt_or_ge 5758010470240049663 n with h10 | h10
          · -- n > 5758010470240049663
            rcases Nat.lt_or_ge 5774313151418744533 n with h12 | h12
            · -- n > 5774313151418744533
              exact RamareSaouter2003.prime_interval_nat_ladder_c07663 n (by omega) (by omega)
            · -- n <= 5774313151418744533
              exact RamareSaouter2003.prime_interval_nat_ladder_c07662 n (by omega) (by omega)
          · -- n <= 5758010470240049663
            exact RamareSaouter2003.prime_interval_nat_ladder_c07661 n (by omega) (by omega)
        · -- n <= 5741753848356002297
          rcases Nat.lt_or_ge 5709378229111569787 n with h10 | h10
          · -- n > 5709378229111569787
            rcases Nat.lt_or_ge 5725543116213469181 n with h12 | h12
            · -- n > 5725543116213469181
              exact RamareSaouter2003.prime_interval_nat_ladder_c07660 n (by omega) (by omega)
            · -- n <= 5725543116213469181
              exact RamareSaouter2003.prime_interval_nat_ladder_c07659 n (by omega) (by omega)
          · -- n <= 5709378229111569787
            exact RamareSaouter2003.prime_interval_nat_ladder_c07658 n (by omega) (by omega)
      · -- n <= 5693259052390635073
        rcases Nat.lt_or_ge 5645173779471458621 n with h8 | h8
        · -- n > 5645173779471458621
          rcases Nat.lt_or_ge 5661156873509832251 n with h10 | h10
          · -- n > 5661156873509832251
            rcases Nat.lt_or_ge 5677185269036510611 n with h12 | h12
            · -- n > 5677185269036510611
              exact RamareSaouter2003.prime_interval_nat_ladder_c07657 n (by omega) (by omega)
            · -- n <= 5677185269036510611
              exact RamareSaouter2003.prime_interval_nat_ladder_c07656 n (by omega) (by omega)
          · -- n <= 5661156873509832251
            exact RamareSaouter2003.prime_interval_nat_ladder_c07655 n (by omega) (by omega)
        · -- n <= 5645173779471458621
          rcases Nat.lt_or_ge 5613342750797070847 n with h10 | h10
          · -- n > 5613342750797070847
            rcases Nat.lt_or_ge 5629235705471458243 n with h12 | h12
            · -- n > 5629235705471458243
              exact RamareSaouter2003.prime_interval_nat_ladder_c07654 n (by omega) (by omega)
            · -- n <= 5629235705471458243
              exact RamareSaouter2003.prime_interval_nat_ladder_c07653 n (by omega) (by omega)
          · -- n <= 5613342750797070847
            exact RamareSaouter2003.prime_interval_nat_ladder_c07652 n (by omega) (by omega)
    · -- n <= 5597494635027639439
      rcases Nat.lt_or_ge 5503340860079090953 n with h6 | h6
      · -- n > 5503340860079090953
        rcases Nat.lt_or_ge 5550218032737953017 n with h8 | h8
        · -- n > 5550218032737953017
          rcases Nat.lt_or_ge 5565932374913754817 n with h10 | h10
          · -- n > 5565932374913754817
            rcases Nat.lt_or_ge 5581691168592740059 n with h12 | h12
            · -- n > 5581691168592740059
              exact RamareSaouter2003.prime_interval_nat_ladder_c07651 n (by omega) (by omega)
            · -- n <= 5581691168592740059
              exact RamareSaouter2003.prime_interval_nat_ladder_c07650 n (by omega) (by omega)
          · -- n <= 5565932374913754817
            exact RamareSaouter2003.prime_interval_nat_ladder_c07649 n (by omega) (by omega)
        · -- n <= 5550218032737953017
          rcases Nat.lt_or_ge 5518922451220987859 n with h10 | h10
          · -- n > 5518922451220987859
            rcases Nat.lt_or_ge 5534548075343490037 n with h12 | h12
            · -- n > 5534548075343490037
              exact RamareSaouter2003.prime_interval_nat_ladder_c07648 n (by omega) (by omega)
            · -- n <= 5534548075343490037
              exact RamareSaouter2003.prime_interval_nat_ladder_c07647 n (by omega) (by omega)
          · -- n <= 5518922451220987859
            exact RamareSaouter2003.prime_interval_nat_ladder_c07646 n (by omega) (by omega)
      · -- n <= 5503340860079090953
        rcases Nat.lt_or_ge 5456859529383472241 n with h8 | h8
        · -- n > 5456859529383472241
          rcases Nat.lt_or_ge 5472309487397741971 n with h10 | h10
          · -- n > 5472309487397741971
            rcases Nat.lt_or_ge 5487803217648719371 n with h12 | h12
            · -- n > 5487803217648719371
              exact RamareSaouter2003.prime_interval_nat_ladder_c07645 n (by omega) (by omega)
            · -- n <= 5487803217648719371
              exact RamareSaouter2003.prime_interval_nat_ladder_c07644 n (by omega) (by omega)
          · -- n <= 5472309487397741971
            exact RamareSaouter2003.prime_interval_nat_ladder_c07643 n (by omega) (by omega)
        · -- n <= 5456859529383472241
          rcases Nat.lt_or_ge 5426090321226919237 n with h10 | h10
          · -- n > 5426090321226919237
            rcases Nat.lt_or_ge 5441453208783374407 n with h12 | h12
            · -- n > 5441453208783374407
              exact RamareSaouter2003.prime_interval_nat_ladder_c07642 n (by omega) (by omega)
            · -- n <= 5441453208783374407
              exact RamareSaouter2003.prime_interval_nat_ladder_c07641 n (by omega) (by omega)
          · -- n <= 5426090321226919237
            exact RamareSaouter2003.prime_interval_nat_ladder_c07640 n (by omega) (by omega)
