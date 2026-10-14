-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp051
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T22:22:14.935988+00:00
-- url     : https://prove2.me/submissions/b93897eb-8532-4eeb-ac41-59872620c8cc

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02521
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02541
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02550

theorem solution (n : Nat)
    (hn : 4409511496801 < n) (hupper : n <= 4989560667149) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 4690578336071 n with h2 | h2
  · -- n > 4690578336071
    rcases Nat.lt_or_ge 4831785344003 n with h4 | h4
    · -- n > 4831785344003
      rcases Nat.lt_or_ge 4903975045553 n with h6 | h6
      · -- n > 4903975045553
        rcases Nat.lt_or_ge 4940473353089 n with h8 | h8
        · -- n > 4940473353089
          rcases Nat.lt_or_ge 4964956346219 n with h10 | h10
          · -- n > 4964956346219
            rcases Nat.lt_or_ge 4977243303163 n with h12 | h12
            · -- n > 4977243303163
              exact RamareSaouter2003.prime_interval_nat_ladder_c02550 n (by omega) (by omega)
            · -- n <= 4977243303163
              exact RamareSaouter2003.prime_interval_nat_ladder_c02549 n (by omega) (by omega)
          · -- n <= 4964956346219
            rcases Nat.lt_or_ge 4952699721139 n with h12 | h12
            · -- n > 4952699721139
              exact RamareSaouter2003.prime_interval_nat_ladder_c02548 n (by omega) (by omega)
            · -- n <= 4952699721139
              exact RamareSaouter2003.prime_interval_nat_ladder_c02547 n (by omega) (by omega)
        · -- n <= 4940473353089
          rcases Nat.lt_or_ge 4916111089807 n with h10 | h10
          · -- n > 4916111089807
            rcases Nat.lt_or_ge 4928277167663 n with h12 | h12
            · -- n > 4928277167663
              exact RamareSaouter2003.prime_interval_nat_ladder_c02546 n (by omega) (by omega)
            · -- n <= 4928277167663
              exact RamareSaouter2003.prime_interval_nat_ladder_c02545 n (by omega) (by omega)
          · -- n <= 4916111089807
            exact RamareSaouter2003.prime_interval_nat_ladder_c02544 n (by omega) (by omega)
      · -- n <= 4903975045553
        rcases Nat.lt_or_ge 4867746373027 n with h8 | h8
        · -- n > 4867746373027
          rcases Nat.lt_or_ge 4879792760977 n with h10 | h10
          · -- n > 4879792760977
            rcases Nat.lt_or_ge 4891868960579 n with h12 | h12
            · -- n > 4891868960579
              exact RamareSaouter2003.prime_interval_nat_ladder_c02543 n (by omega) (by omega)
            · -- n <= 4891868960579
              exact RamareSaouter2003.prime_interval_nat_ladder_c02542 n (by omega) (by omega)
          · -- n <= 4879792760977
            exact RamareSaouter2003.prime_interval_nat_ladder_c02541 n (by omega) (by omega)
        · -- n <= 4867746373027
          rcases Nat.lt_or_ge 4843742737831 n with h10 | h10
          · -- n > 4843742737831
            rcases Nat.lt_or_ge 4855729723123 n with h12 | h12
            · -- n > 4855729723123
              exact RamareSaouter2003.prime_interval_nat_ladder_c02540 n (by omega) (by omega)
            · -- n <= 4855729723123
              exact RamareSaouter2003.prime_interval_nat_ladder_c02539 n (by omega) (by omega)
          · -- n <= 4843742737831
            exact RamareSaouter2003.prime_interval_nat_ladder_c02538 n (by omega) (by omega)
    · -- n <= 4831785344003
      rcases Nat.lt_or_ge 4760658321803 n with h6 | h6
      · -- n > 4760658321803
        rcases Nat.lt_or_ge 4796089981069 n with h8 | h8
        · -- n > 4796089981069
          rcases Nat.lt_or_ge 4807959038353 n with h10 | h10
          · -- n > 4807959038353
            rcases Nat.lt_or_ge 4819857468443 n with h12 | h12
            · -- n > 4819857468443
              exact RamareSaouter2003.prime_interval_nat_ladder_c02537 n (by omega) (by omega)
            · -- n <= 4819857468443
              exact RamareSaouter2003.prime_interval_nat_ladder_c02536 n (by omega) (by omega)
          · -- n <= 4807959038353
            exact RamareSaouter2003.prime_interval_nat_ladder_c02535 n (by omega) (by omega)
        · -- n <= 4796089981069
          rcases Nat.lt_or_ge 4772439695057 n with h10 | h10
          · -- n > 4772439695057
            rcases Nat.lt_or_ge 4784250224077 n with h12 | h12
            · -- n > 4784250224077
              exact RamareSaouter2003.prime_interval_nat_ladder_c02534 n (by omega) (by omega)
            · -- n <= 4784250224077
              exact RamareSaouter2003.prime_interval_nat_ladder_c02533 n (by omega) (by omega)
          · -- n <= 4772439695057
            exact RamareSaouter2003.prime_interval_nat_ladder_c02532 n (by omega) (by omega)
      · -- n <= 4760658321803
        rcases Nat.lt_or_ge 4725488418263 n with h8 | h8
        · -- n > 4725488418263
          rcases Nat.lt_or_ge 4737182755111 n with h10 | h10
          · -- n > 4737182755111
            rcases Nat.lt_or_ge 4748906032469 n with h12 | h12
            · -- n > 4748906032469
              exact RamareSaouter2003.prime_interval_nat_ladder_c02531 n (by omega) (by omega)
            · -- n <= 4748906032469
              exact RamareSaouter2003.prime_interval_nat_ladder_c02530 n (by omega) (by omega)
          · -- n <= 4737182755111
            exact RamareSaouter2003.prime_interval_nat_ladder_c02529 n (by omega) (by omega)
        · -- n <= 4725488418263
          rcases Nat.lt_or_ge 4702186279867 n with h10 | h10
          · -- n > 4702186279867
            rcases Nat.lt_or_ge 4713822950191 n with h12 | h12
            · -- n > 4713822950191
              exact RamareSaouter2003.prime_interval_nat_ladder_c02528 n (by omega) (by omega)
            · -- n <= 4713822950191
              exact RamareSaouter2003.prime_interval_nat_ladder_c02527 n (by omega) (by omega)
          · -- n <= 4702186279867
            exact RamareSaouter2003.prime_interval_nat_ladder_c02526 n (by omega) (by omega)
  · -- n <= 4690578336071
    rcases Nat.lt_or_ge 4542257158783 n with h4 | h4
    · -- n > 4542257158783
      rcases Nat.lt_or_ge 4610121139751 n with h6 | h6
      · -- n > 4610121139751
        rcases Nat.lt_or_ge 4644432411371 n with h8 | h8
        · -- n > 4644432411371
          rcases Nat.lt_or_ge 4667448344957 n with h10 | h10
          · -- n > 4667448344957
            rcases Nat.lt_or_ge 4678999048033 n with h12 | h12
            · -- n > 4678999048033
              exact RamareSaouter2003.prime_interval_nat_ladder_c02525 n (by omega) (by omega)
            · -- n <= 4678999048033
              exact RamareSaouter2003.prime_interval_nat_ladder_c02524 n (by omega) (by omega)
          · -- n <= 4667448344957
            rcases Nat.lt_or_ge 4655926156151 n with h12 | h12
            · -- n > 4655926156151
              exact RamareSaouter2003.prime_interval_nat_ladder_c02523 n (by omega) (by omega)
            · -- n <= 4655926156151
              exact RamareSaouter2003.prime_interval_nat_ladder_c02522 n (by omega) (by omega)
        · -- n <= 4644432411371
          rcases Nat.lt_or_ge 4621529973187 n with h10 | h10
          · -- n > 4621529973187
            rcases Nat.lt_or_ge 4632967040467 n with h12 | h12
            · -- n > 4632967040467
              exact RamareSaouter2003.prime_interval_nat_ladder_c02521 n (by omega) (by omega)
            · -- n <= 4632967040467
              exact RamareSaouter2003.prime_interval_nat_ladder_c02520 n (by omega) (by omega)
          · -- n <= 4621529973187
            exact RamareSaouter2003.prime_interval_nat_ladder_c02519 n (by omega) (by omega)
      · -- n <= 4610121139751
        rcases Nat.lt_or_ge 4576063346431 n with h8 | h8
        · -- n > 4576063346431
          rcases Nat.lt_or_ge 4587387895759 n with h10 | h10
          · -- n > 4587387895759
            rcases Nat.lt_or_ge 4598740470437 n with h12 | h12
            · -- n > 4598740470437
              exact RamareSaouter2003.prime_interval_nat_ladder_c02518 n (by omega) (by omega)
            · -- n <= 4598740470437
              exact RamareSaouter2003.prime_interval_nat_ladder_c02517 n (by omega) (by omega)
          · -- n <= 4587387895759
            exact RamareSaouter2003.prime_interval_nat_ladder_c02516 n (by omega) (by omega)
        · -- n <= 4576063346431
          rcases Nat.lt_or_ge 4553498046809 n with h10 | h10
          · -- n > 4553498046809
            rcases Nat.lt_or_ge 4564766753083 n with h12 | h12
            · -- n > 4564766753083
              exact RamareSaouter2003.prime_interval_nat_ladder_c02515 n (by omega) (by omega)
            · -- n <= 4564766753083
              exact RamareSaouter2003.prime_interval_nat_ladder_c02514 n (by omega) (by omega)
          · -- n <= 4553498046809
            exact RamareSaouter2003.prime_interval_nat_ladder_c02513 n (by omega) (by omega)
    · -- n <= 4542257158783
      rcases Nat.lt_or_ge 4475392179901 n with h6 | h6
      · -- n > 4475392179901
        rcases Nat.lt_or_ge 4508700718273 n with h8 | h8
        · -- n > 4508700718273
          rcases Nat.lt_or_ge 4519858562951 n with h10 | h10
          · -- n > 4519858562951
            rcases Nat.lt_or_ge 4531044020353 n with h12 | h12
            · -- n > 4531044020353
              exact RamareSaouter2003.prime_interval_nat_ladder_c02512 n (by omega) (by omega)
            · -- n <= 4531044020353
              exact RamareSaouter2003.prime_interval_nat_ladder_c02511 n (by omega) (by omega)
          · -- n <= 4519858562951
            exact RamareSaouter2003.prime_interval_nat_ladder_c02510 n (by omega) (by omega)
        · -- n <= 4508700718273
          rcases Nat.lt_or_ge 4486467594599 n with h10 | h10
          · -- n > 4486467594599
            rcases Nat.lt_or_ge 4497570418193 n with h12 | h12
            · -- n > 4497570418193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02509 n (by omega) (by omega)
            · -- n <= 4497570418193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02508 n (by omega) (by omega)
          · -- n <= 4486467594599
            exact RamareSaouter2003.prime_interval_nat_ladder_c02507 n (by omega) (by omega)
      · -- n <= 4475392179901
        rcases Nat.lt_or_ge 4442329711957 n with h8 | h8
        · -- n > 4442329711957
          rcases Nat.lt_or_ge 4453323305923 n with h10 | h10
          · -- n > 4453323305923
            rcases Nat.lt_or_ge 4464344106113 n with h12 | h12
            · -- n > 4464344106113
              exact RamareSaouter2003.prime_interval_nat_ladder_c02506 n (by omega) (by omega)
            · -- n <= 4464344106113
              exact RamareSaouter2003.prime_interval_nat_ladder_c02505 n (by omega) (by omega)
          · -- n <= 4453323305923
            exact RamareSaouter2003.prime_interval_nat_ladder_c02504 n (by omega) (by omega)
        · -- n <= 4442329711957
          rcases Nat.lt_or_ge 4420423874353 n with h10 | h10
          · -- n > 4420423874353
            rcases Nat.lt_or_ge 4431363257063 n with h12 | h12
            · -- n > 4431363257063
              exact RamareSaouter2003.prime_interval_nat_ladder_c02503 n (by omega) (by omega)
            · -- n <= 4431363257063
              exact RamareSaouter2003.prime_interval_nat_ladder_c02502 n (by omega) (by omega)
          · -- n <= 4420423874353
            exact RamareSaouter2003.prime_interval_nat_ladder_c02501 n (by omega) (by omega)
