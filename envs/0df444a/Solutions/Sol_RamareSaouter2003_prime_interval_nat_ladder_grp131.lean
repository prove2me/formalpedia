-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp131
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T23:58:37.383904+00:00
-- url     : https://prove2.me/submissions/79c66a17-8e38-489c-8257-ffb8d221070a

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06521
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06541
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06550

theorem solution (n : Nat)
    (hn : 216131755642320989 < n) (hupper : n <= 248949425222306737) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 231961012107470141 n with h2 | h2
  · -- n > 231961012107470141
    rcases Nat.lt_or_ge 239965737512003821 n with h4 | h4
    · -- n > 239965737512003821
      rcases Nat.lt_or_ge 244070996002807937 n with h6 | h6
      · -- n > 244070996002807937
        rcases Nat.lt_or_ge 246149885144134567 n with h8 | h8
        · -- n > 246149885144134567
          rcases Nat.lt_or_ge 247545689747448011 n with h10 | h10
          · -- n > 247545689747448011
            rcases Nat.lt_or_ge 248246565621778667 n with h12 | h12
            · -- n > 248246565621778667
              exact RamareSaouter2003.prime_interval_nat_ladder_c06550 n (by omega) (by omega)
            · -- n <= 248246565621778667
              exact RamareSaouter2003.prime_interval_nat_ladder_c06549 n (by omega) (by omega)
          · -- n <= 247545689747448011
            rcases Nat.lt_or_ge 246846795335925793 n with h12 | h12
            · -- n > 246846795335925793
              exact RamareSaouter2003.prime_interval_nat_ladder_c06548 n (by omega) (by omega)
            · -- n <= 246846795335925793
              exact RamareSaouter2003.prime_interval_nat_ladder_c06547 n (by omega) (by omega)
        · -- n <= 246149885144134567
          rcases Nat.lt_or_ge 244761989678110397 n with h10 | h10
          · -- n > 244761989678110397
            rcases Nat.lt_or_ge 245454950983694159 n with h12 | h12
            · -- n > 245454950983694159
              exact RamareSaouter2003.prime_interval_nat_ladder_c06546 n (by omega) (by omega)
            · -- n <= 245454950983694159
              exact RamareSaouter2003.prime_interval_nat_ladder_c06545 n (by omega) (by omega)
          · -- n <= 244761989678110397
            exact RamareSaouter2003.prime_interval_nat_ladder_c06544 n (by omega) (by omega)
      · -- n <= 244070996002807937
        rcases Nat.lt_or_ge 242009629217204131 n with h8 | h8
        · -- n > 242009629217204131
          rcases Nat.lt_or_ge 242694823801063619 n with h10 | h10
          · -- n > 242694823801063619
            rcases Nat.lt_or_ge 243381939105257177 n with h12 | h12
            · -- n > 243381939105257177
              exact RamareSaouter2003.prime_interval_nat_ladder_c06543 n (by omega) (by omega)
            · -- n <= 243381939105257177
              exact RamareSaouter2003.prime_interval_nat_ladder_c06542 n (by omega) (by omega)
          · -- n <= 242694823801063619
            exact RamareSaouter2003.prime_interval_nat_ladder_c06541 n (by omega) (by omega)
        · -- n <= 242009629217204131
          rcases Nat.lt_or_ge 240645132427479653 n with h10 | h10
          · -- n > 240645132427479653
            rcases Nat.lt_or_ge 241326410316653143 n with h12 | h12
            · -- n > 241326410316653143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06540 n (by omega) (by omega)
            · -- n <= 241326410316653143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06539 n (by omega) (by omega)
          · -- n <= 240645132427479653
            exact RamareSaouter2003.prime_interval_nat_ladder_c06538 n (by omega) (by omega)
    · -- n <= 239965737512003821
      rcases Nat.lt_or_ge 235929473928997001 n with h6 | h6
      · -- n > 235929473928997001
        rcases Nat.lt_or_ge 237939052466322211 n with h8 | h8
        · -- n > 237939052466322211
          rcases Nat.lt_or_ge 238612689356525761 n with h10 | h10
          · -- n > 238612689356525761
            rcases Nat.lt_or_ge 239288257834851691 n with h12 | h12
            · -- n > 239288257834851691
              exact RamareSaouter2003.prime_interval_nat_ladder_c06537 n (by omega) (by omega)
            · -- n <= 239288257834851691
              exact RamareSaouter2003.prime_interval_nat_ladder_c06536 n (by omega) (by omega)
          · -- n <= 238612689356525761
            exact RamareSaouter2003.prime_interval_nat_ladder_c06535 n (by omega) (by omega)
        · -- n <= 237939052466322211
          rcases Nat.lt_or_ge 236597429208606707 n with h10 | h10
          · -- n > 236597429208606707
            rcases Nat.lt_or_ge 237267287413905383 n with h12 | h12
            · -- n > 237267287413905383
              exact RamareSaouter2003.prime_interval_nat_ladder_c06534 n (by omega) (by omega)
            · -- n <= 237267287413905383
              exact RamareSaouter2003.prime_interval_nat_ladder_c06533 n (by omega) (by omega)
          · -- n <= 236597429208606707
            exact RamareSaouter2003.prime_interval_nat_ladder_c06532 n (by omega) (by omega)
      · -- n <= 235929473928997001
        rcases Nat.lt_or_ge 233936807253843857 n with h8 | h8
        · -- n > 233936807253843857
          rcases Nat.lt_or_ge 234599153813307707 n with h10 | h10
          · -- n > 234599153813307707
            rcases Nat.lt_or_ge 235263375651831071 n with h12 | h12
            · -- n > 235263375651831071
              exact RamareSaouter2003.prime_interval_nat_ladder_c06531 n (by omega) (by omega)
            · -- n <= 235263375651831071
              exact RamareSaouter2003.prime_interval_nat_ladder_c06530 n (by omega) (by omega)
          · -- n <= 234599153813307707
            exact RamareSaouter2003.prime_interval_nat_ladder_c06529 n (by omega) (by omega)
        · -- n <= 233936807253843857
          rcases Nat.lt_or_ge 232617761193593641 n with h10 | h10
          · -- n > 232617761193593641
            rcases Nat.lt_or_ge 233276349581477681 n with h12 | h12
            · -- n > 233276349581477681
              exact RamareSaouter2003.prime_interval_nat_ladder_c06528 n (by omega) (by omega)
            · -- n <= 233276349581477681
              exact RamareSaouter2003.prime_interval_nat_ladder_c06527 n (by omega) (by omega)
          · -- n <= 232617761193593641
            exact RamareSaouter2003.prime_interval_nat_ladder_c06526 n (by omega) (by omega)
  · -- n <= 231961012107470141
    rcases Nat.lt_or_ge 223590204921809623 n with h4 | h4
    · -- n > 223590204921809623
      rcases Nat.lt_or_ge 227415438508497797 n with h6 | h6
      · -- n > 227415438508497797
        rcases Nat.lt_or_ge 229352536910246119 n with h8 | h8
        · -- n > 229352536910246119
          rcases Nat.lt_or_ge 230653071220162133 n with h10 | h10
          · -- n > 230653071220162133
            rcases Nat.lt_or_ge 231306119638400141 n with h12 | h12
            · -- n > 231306119638400141
              exact RamareSaouter2003.prime_interval_nat_ladder_c06525 n (by omega) (by omega)
            · -- n <= 231306119638400141
              exact RamareSaouter2003.prime_interval_nat_ladder_c06524 n (by omega) (by omega)
          · -- n <= 230653071220162133
            rcases Nat.lt_or_ge 230001902274457871 n with h12 | h12
            · -- n > 230001902274457871
              exact RamareSaouter2003.prime_interval_nat_ladder_c06523 n (by omega) (by omega)
            · -- n <= 230001902274457871
              exact RamareSaouter2003.prime_interval_nat_ladder_c06522 n (by omega) (by omega)
        · -- n <= 229352536910246119
          rcases Nat.lt_or_ge 228059319398096233 n with h10 | h10
          · -- n > 228059319398096233
            rcases Nat.lt_or_ge 228705012499418563 n with h12 | h12
            · -- n > 228705012499418563
              exact RamareSaouter2003.prime_interval_nat_ladder_c06521 n (by omega) (by omega)
            · -- n <= 228705012499418563
              exact RamareSaouter2003.prime_interval_nat_ladder_c06520 n (by omega) (by omega)
          · -- n <= 228059319398096233
            exact RamareSaouter2003.prime_interval_nat_ladder_c06519 n (by omega) (by omega)
      · -- n <= 227415438508497797
        rcases Nat.lt_or_ge 225494708448248761 n with h8 | h8
        · -- n > 225494708448248761
          rcases Nat.lt_or_ge 226133150176411151 n with h10 | h10
          · -- n > 226133150176411151
            rcases Nat.lt_or_ge 226773384946509997 n with h12 | h12
            · -- n > 226773384946509997
              exact RamareSaouter2003.prime_interval_nat_ladder_c06518 n (by omega) (by omega)
            · -- n <= 226773384946509997
              exact RamareSaouter2003.prime_interval_nat_ladder_c06517 n (by omega) (by omega)
          · -- n <= 226133150176411151
            exact RamareSaouter2003.prime_interval_nat_ladder_c06516 n (by omega) (by omega)
        · -- n <= 225494708448248761
          rcases Nat.lt_or_ge 224223254335445077 n with h10 | h10
          · -- n > 224223254335445077
            rcases Nat.lt_or_ge 224858079652297577 n with h12 | h12
            · -- n > 224858079652297577
              exact RamareSaouter2003.prime_interval_nat_ladder_c06515 n (by omega) (by omega)
            · -- n <= 224858079652297577
              exact RamareSaouter2003.prime_interval_nat_ladder_c06514 n (by omega) (by omega)
          · -- n <= 224223254335445077
            exact RamareSaouter2003.prime_interval_nat_ladder_c06513 n (by omega) (by omega)
    · -- n <= 223590204921809623
      rcases Nat.lt_or_ge 219829369463796203 n with h6 | h6
      · -- n > 219829369463796203
        rcases Nat.lt_or_ge 221701785469823101 n with h8 | h8
        · -- n > 221701785469823101
          rcases Nat.lt_or_ge 222329471941780193 n with h10 | h10
          · -- n > 222329471941780193
            rcases Nat.lt_or_ge 222958943870011549 n with h12 | h12
            · -- n > 222958943870011549
              exact RamareSaouter2003.prime_interval_nat_ladder_c06512 n (by omega) (by omega)
            · -- n <= 222958943870011549
              exact RamareSaouter2003.prime_interval_nat_ladder_c06511 n (by omega) (by omega)
          · -- n <= 222329471941780193
            exact RamareSaouter2003.prime_interval_nat_ladder_c06510 n (by omega) (by omega)
        · -- n <= 221701785469823101
          rcases Nat.lt_or_ge 220451726223629111 n with h10 | h10
          · -- n > 220451726223629111
            rcases Nat.lt_or_ge 221075867412841039 n with h12 | h12
            · -- n > 221075867412841039
              exact RamareSaouter2003.prime_interval_nat_ladder_c06509 n (by omega) (by omega)
            · -- n <= 221075867412841039
              exact RamareSaouter2003.prime_interval_nat_ladder_c06508 n (by omega) (by omega)
          · -- n <= 220451726223629111
            exact RamareSaouter2003.prime_interval_nat_ladder_c06507 n (by omega) (by omega)
      · -- n <= 219829369463796203
        rcases Nat.lt_or_ge 217972710258471169 n with h8 | h8
        · -- n > 217972710258471169
          rcases Nat.lt_or_ge 218589850604445323 n with h10 | h10
          · -- n > 218589850604445323
            rcases Nat.lt_or_ge 219208742650702271 n with h12 | h12
            · -- n > 219208742650702271
              exact RamareSaouter2003.prime_interval_nat_ladder_c06506 n (by omega) (by omega)
            · -- n <= 219208742650702271
              exact RamareSaouter2003.prime_interval_nat_ladder_c06505 n (by omega) (by omega)
          · -- n <= 218589850604445323
            exact RamareSaouter2003.prime_interval_nat_ladder_c06504 n (by omega) (by omega)
        · -- n <= 217972710258471169
          rcases Nat.lt_or_ge 216743652966812189 n with h10 | h10
          · -- n > 216743652966812189
            rcases Nat.lt_or_ge 217357319753759261 n with h12 | h12
            · -- n > 217357319753759261
              exact RamareSaouter2003.prime_interval_nat_ladder_c06503 n (by omega) (by omega)
            · -- n <= 217357319753759261
              exact RamareSaouter2003.prime_interval_nat_ladder_c06502 n (by omega) (by omega)
          · -- n <= 216743652966812189
            exact RamareSaouter2003.prime_interval_nat_ladder_c06501 n (by omega) (by omega)
