-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp134
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T00:40:00.661174+00:00
-- url     : https://prove2.me/submissions/416469a3-bf1f-441c-a815-3874b08f6089

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06668
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06688
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06700

theorem solution (n : Nat)
    (hn : 330290864187526579 < n) (hupper : n <= 380443069540112779) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 354481160936760631 n with h2 | h2
  · -- n > 354481160936760631
    rcases Nat.lt_or_ge 366714043719068429 n with h4 | h4
    · -- n > 366714043719068429
      rcases Nat.lt_or_ge 372987809570218949 n with h6 | h6
      · -- n > 372987809570218949
        rcases Nat.lt_or_ge 376164871600714333 n with h8 | h8
        · -- n > 376164871600714333
          rcases Nat.lt_or_ge 378297919971067703 n with h10 | h10
          · -- n > 378297919971067703
            rcases Nat.lt_or_ge 379368983378744077 n with h12 | h12
            · -- n > 379368983378744077
              exact RamareSaouter2003.prime_interval_nat_ladder_c06700 n (by omega) (by omega)
            · -- n <= 379368983378744077
              exact RamareSaouter2003.prime_interval_nat_ladder_c06699 n (by omega) (by omega)
          · -- n <= 378297919971067703
            rcases Nat.lt_or_ge 377229902457888853 n with h12 | h12
            · -- n > 377229902457888853
              exact RamareSaouter2003.prime_interval_nat_ladder_c06698 n (by omega) (by omega)
            · -- n <= 377229902457888853
              exact RamareSaouter2003.prime_interval_nat_ladder_c06697 n (by omega) (by omega)
        · -- n <= 376164871600714333
          rcases Nat.lt_or_ge 374043836413522619 n with h10 | h10
          · -- n > 374043836413522619
            rcases Nat.lt_or_ge 375102857831310899 n with h12 | h12
            · -- n > 375102857831310899
              exact RamareSaouter2003.prime_interval_nat_ladder_c06696 n (by omega) (by omega)
            · -- n <= 375102857831310899
              exact RamareSaouter2003.prime_interval_nat_ladder_c06695 n (by omega) (by omega)
          · -- n <= 374043836413522619
            exact RamareSaouter2003.prime_interval_nat_ladder_c06694 n (by omega) (by omega)
      · -- n <= 372987809570218949
        rcases Nat.lt_or_ge 369837668266121383 n with h8 | h8
        · -- n > 369837668266121383
          rcases Nat.lt_or_ge 370884770252613413 n with h10 | h10
          · -- n > 370884770252613413
            rcases Nat.lt_or_ge 371934781888962233 n with h12 | h12
            · -- n > 371934781888962233
              exact RamareSaouter2003.prime_interval_nat_ladder_c06693 n (by omega) (by omega)
            · -- n <= 371934781888962233
              exact RamareSaouter2003.prime_interval_nat_ladder_c06692 n (by omega) (by omega)
          · -- n <= 370884770252613413
            exact RamareSaouter2003.prime_interval_nat_ladder_c06691 n (by omega) (by omega)
        · -- n <= 369837668266121383
          rcases Nat.lt_or_ge 367752318476620751 n with h10 | h10
          · -- n > 367752318476620751
            rcases Nat.lt_or_ge 368793524660235397 n with h12 | h12
            · -- n > 368793524660235397
              exact RamareSaouter2003.prime_interval_nat_ladder_c06690 n (by omega) (by omega)
            · -- n <= 368793524660235397
              exact RamareSaouter2003.prime_interval_nat_ladder_c06689 n (by omega) (by omega)
          · -- n <= 367752318476620751
            exact RamareSaouter2003.prime_interval_nat_ladder_c06688 n (by omega) (by omega)
    · -- n <= 366714043719068429
      rcases Nat.lt_or_ge 360545718861934387 n with h6 | h6
      · -- n > 360545718861934387
        rcases Nat.lt_or_ge 363616828403474293 n with h8 | h8
        · -- n > 363616828403474293
          rcases Nat.lt_or_ge 364646298239846057 n with h10 | h10
          · -- n > 364646298239846057
            rcases Nat.lt_or_ge 365678715782913107 n with h12 | h12
            · -- n > 365678715782913107
              exact RamareSaouter2003.prime_interval_nat_ladder_c06687 n (by omega) (by omega)
            · -- n <= 365678715782913107
              exact RamareSaouter2003.prime_interval_nat_ladder_c06686 n (by omega) (by omega)
          · -- n <= 364646298239846057
            exact RamareSaouter2003.prime_interval_nat_ladder_c06685 n (by omega) (by omega)
        · -- n <= 363616828403474293
          rcases Nat.lt_or_ge 361566533374365797 n with h10 | h10
          · -- n > 361566533374365797
            rcases Nat.lt_or_ge 362590238538837553 n with h12 | h12
            · -- n > 362590238538837553
              exact RamareSaouter2003.prime_interval_nat_ladder_c06684 n (by omega) (by omega)
            · -- n <= 362590238538837553
              exact RamareSaouter2003.prime_interval_nat_ladder_c06683 n (by omega) (by omega)
          · -- n <= 361566533374365797
            exact RamareSaouter2003.prime_interval_nat_ladder_c06682 n (by omega) (by omega)
      · -- n <= 360545718861934387
        rcases Nat.lt_or_ge 357500567590544177 n with h8 | h8
        · -- n > 357500567590544177
          rcases Nat.lt_or_ge 358512749300149693 n with h10 | h10
          · -- n > 358512749300149693
            rcases Nat.lt_or_ge 359527785286787203 n with h12 | h12
            · -- n > 359527785286787203
              exact RamareSaouter2003.prime_interval_nat_ladder_c06681 n (by omega) (by omega)
            · -- n <= 359527785286787203
              exact RamareSaouter2003.prime_interval_nat_ladder_c06680 n (by omega) (by omega)
          · -- n <= 358512749300149693
            exact RamareSaouter2003.prime_interval_nat_ladder_c06679 n (by omega) (by omega)
        · -- n <= 357500567590544177
          rcases Nat.lt_or_ge 355484788440936689 n with h10 | h10
          · -- n > 355484788440936689
            rcases Nat.lt_or_ge 356491241378960411 n with h12 | h12
            · -- n > 356491241378960411
              exact RamareSaouter2003.prime_interval_nat_ladder_c06678 n (by omega) (by omega)
            · -- n <= 356491241378960411
              exact RamareSaouter2003.prime_interval_nat_ladder_c06677 n (by omega) (by omega)
          · -- n <= 355484788440936689
            exact RamareSaouter2003.prime_interval_nat_ladder_c06676 n (by omega) (by omega)
  · -- n <= 354481160936760631
    rcases Nat.lt_or_ge 341689010116495267 n with h4 | h4
    · -- n > 341689010116495267
      rcases Nat.lt_or_ge 347534660303554727 n with h6 | h6
      · -- n > 347534660303554727
        rcases Nat.lt_or_ge 350494939267038481 n with h8 | h8
        · -- n > 350494939267038481
          rcases Nat.lt_or_ge 352482384617126243 n with h10 | h10
          · -- n > 352482384617126243
            rcases Nat.lt_or_ge 353480355341597123 n with h12 | h12
            · -- n > 353480355341597123
              exact RamareSaouter2003.prime_interval_nat_ladder_c06675 n (by omega) (by omega)
            · -- n <= 353480355341597123
              exact RamareSaouter2003.prime_interval_nat_ladder_c06674 n (by omega) (by omega)
          · -- n <= 352482384617126243
            rcases Nat.lt_or_ge 351487242772197211 n with h12 | h12
            · -- n > 351487242772197211
              exact RamareSaouter2003.prime_interval_nat_ladder_c06673 n (by omega) (by omega)
            · -- n <= 351487242772197211
              exact RamareSaouter2003.prime_interval_nat_ladder_c06672 n (by omega) (by omega)
        · -- n <= 350494939267038481
          rcases Nat.lt_or_ge 348518637308304091 n with h10 | h10
          · -- n > 348518637308304091
            rcases Nat.lt_or_ge 349505393412913909 n with h12 | h12
            · -- n > 349505393412913909
              exact RamareSaouter2003.prime_interval_nat_ladder_c06671 n (by omega) (by omega)
            · -- n <= 349505393412913909
              exact RamareSaouter2003.prime_interval_nat_ladder_c06670 n (by omega) (by omega)
          · -- n <= 348518637308304091
            exact RamareSaouter2003.prime_interval_nat_ladder_c06669 n (by omega) (by omega)
      · -- n <= 347534660303554727
        rcases Nat.lt_or_ge 344599413368805671 n with h8 | h8
        · -- n > 344599413368805671
          rcases Nat.lt_or_ge 345575063541587137 n with h10 | h10
          · -- n > 345575063541587137
            rcases Nat.lt_or_ge 346553462397606859 n with h12 | h12
            · -- n > 346553462397606859
              exact RamareSaouter2003.prime_interval_nat_ladder_c06668 n (by omega) (by omega)
            · -- n <= 346553462397606859
              exact RamareSaouter2003.prime_interval_nat_ladder_c06667 n (by omega) (by omega)
          · -- n <= 345575063541587137
            exact RamareSaouter2003.prime_interval_nat_ladder_c06666 n (by omega) (by omega)
        · -- n <= 344599413368805671
          rcases Nat.lt_or_ge 342656351461826483 n with h10 | h10
          · -- n > 342656351461826483
            rcases Nat.lt_or_ge 343626502254193049 n with h12 | h12
            · -- n > 343626502254193049
              exact RamareSaouter2003.prime_interval_nat_ladder_c06665 n (by omega) (by omega)
            · -- n <= 343626502254193049
              exact RamareSaouter2003.prime_interval_nat_ladder_c06664 n (by omega) (by omega)
          · -- n <= 342656351461826483
            exact RamareSaouter2003.prime_interval_nat_ladder_c06663 n (by omega) (by omega)
    · -- n <= 341689010116495267
      rcases Nat.lt_or_ge 335941587521895731 n with h6 | h6
      · -- n > 335941587521895731
        rcases Nat.lt_or_ge 338803122630926087 n with h8 | h8
        · -- n > 338803122630926087
          rcases Nat.lt_or_ge 339762374515825159 n with h10 | h10
          · -- n > 339762374515825159
            rcases Nat.lt_or_ge 340724333112657587 n with h12 | h12
            · -- n > 340724333112657587
              exact RamareSaouter2003.prime_interval_nat_ladder_c06662 n (by omega) (by omega)
            · -- n <= 340724333112657587
              exact RamareSaouter2003.prime_interval_nat_ladder_c06661 n (by omega) (by omega)
          · -- n <= 339762374515825159
            exact RamareSaouter2003.prime_interval_nat_ladder_c06660 n (by omega) (by omega)
        · -- n <= 338803122630926087
          rcases Nat.lt_or_ge 336892740676131971 n with h10 | h10
          · -- n > 336892740676131971
            rcases Nat.lt_or_ge 337846582253798161 n with h12 | h12
            · -- n > 337846582253798161
              exact RamareSaouter2003.prime_interval_nat_ladder_c06659 n (by omega) (by omega)
            · -- n <= 337846582253798161
              exact RamareSaouter2003.prime_interval_nat_ladder_c06658 n (by omega) (by omega)
          · -- n <= 336892740676131971
            exact RamareSaouter2003.prime_interval_nat_ladder_c06657 n (by omega) (by omega)
      · -- n <= 335941587521895731
        rcases Nat.lt_or_ge 333104244493161469 n with h8 | h8
        · -- n > 333104244493161469
          rcases Nat.lt_or_ge 334047363103219903 n with h10 | h10
          · -- n > 334047363103219903
            rcases Nat.lt_or_ge 334993147202083217 n with h12 | h12
            · -- n > 334993147202083217
              exact RamareSaouter2003.prime_interval_nat_ladder_c06656 n (by omega) (by omega)
            · -- n <= 334993147202083217
              exact RamareSaouter2003.prime_interval_nat_ladder_c06655 n (by omega) (by omega)
          · -- n <= 334047363103219903
            exact RamareSaouter2003.prime_interval_nat_ladder_c06654 n (by omega) (by omega)
        · -- n <= 333104244493161469
          rcases Nat.lt_or_ge 331226002529764409 n with h10 | h10
          · -- n > 331226002529764409
            rcases Nat.lt_or_ge 332163787160264119 n with h12 | h12
            · -- n > 332163787160264119
              exact RamareSaouter2003.prime_interval_nat_ladder_c06653 n (by omega) (by omega)
            · -- n <= 332163787160264119
              exact RamareSaouter2003.prime_interval_nat_ladder_c06652 n (by omega) (by omega)
          · -- n <= 331226002529764409
            exact RamareSaouter2003.prime_interval_nat_ladder_c06651 n (by omega) (by omega)
