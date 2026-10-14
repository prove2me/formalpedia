-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp081
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T08:41:14.558739+00:00
-- url     : https://prove2.me/submissions/51a9c710-e6eb-4c16-8f52-03d1334be183

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04050

theorem solution (n : Nat)
    (hn : 184372641394199 < n) (hupper : n <= 212343815514223) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 197862475075933 n with h2 | h2
  · -- n > 197862475075933
    rcases Nat.lt_or_ge 204686148866263 n with h4 | h4
    · -- n > 204686148866263
      rcases Nat.lt_or_ge 208184921881771 n with h6 | h6
      · -- n > 208184921881771
        rcases Nat.lt_or_ge 209956641858127 n with h8 | h8
        · -- n > 209956641858127
          rcases Nat.lt_or_ge 211146783636827 n with h10 | h10
          · -- n > 211146783636827
            rcases Nat.lt_or_ge 211744337771269 n with h12 | h12
            · -- n > 211744337771269
              exact RamareSaouter2003.prime_interval_nat_ladder_c04050 n (by omega) (by omega)
            · -- n <= 211744337771269
              exact RamareSaouter2003.prime_interval_nat_ladder_c04049 n (by omega) (by omega)
          · -- n <= 211146783636827
            rcases Nat.lt_or_ge 210550885914361 n with h12 | h12
            · -- n > 210550885914361
              exact RamareSaouter2003.prime_interval_nat_ladder_c04048 n (by omega) (by omega)
            · -- n <= 210550885914361
              exact RamareSaouter2003.prime_interval_nat_ladder_c04047 n (by omega) (by omega)
        · -- n <= 209956641858127
          rcases Nat.lt_or_ge 208773967073759 n with h10 | h10
          · -- n > 208773967073759
            rcases Nat.lt_or_ge 209363960844793 n with h12 | h12
            · -- n > 209363960844793
              exact RamareSaouter2003.prime_interval_nat_ladder_c04046 n (by omega) (by omega)
            · -- n <= 209363960844793
              exact RamareSaouter2003.prime_interval_nat_ladder_c04045 n (by omega) (by omega)
          · -- n <= 208773967073759
            exact RamareSaouter2003.prime_interval_nat_ladder_c04044 n (by omega) (by omega)
      · -- n <= 208184921881771
        rcases Nat.lt_or_ge 206426915140613 n with h8 | h8
        · -- n > 206426915140613
          rcases Nat.lt_or_ge 207011368999217 n with h10 | h10
          · -- n > 207011368999217
            rcases Nat.lt_or_ge 207597457638139 n with h12 | h12
            · -- n > 207597457638139
              exact RamareSaouter2003.prime_interval_nat_ladder_c04043 n (by omega) (by omega)
            · -- n <= 207597457638139
              exact RamareSaouter2003.prime_interval_nat_ladder_c04042 n (by omega) (by omega)
          · -- n <= 207011368999217
            exact RamareSaouter2003.prime_interval_nat_ladder_c04041 n (by omega) (by omega)
        · -- n <= 206426915140613
          rcases Nat.lt_or_ge 205264008366269 n with h10 | h10
          · -- n > 205264008366269
            rcases Nat.lt_or_ge 205844262209461 n with h12 | h12
            · -- n > 205844262209461
              exact RamareSaouter2003.prime_interval_nat_ladder_c04040 n (by omega) (by omega)
            · -- n <= 205844262209461
              exact RamareSaouter2003.prime_interval_nat_ladder_c04039 n (by omega) (by omega)
          · -- n <= 205264008366269
            exact RamareSaouter2003.prime_interval_nat_ladder_c04038 n (by omega) (by omega)
    · -- n <= 204686148866263
      rcases Nat.lt_or_ge 201246077798729 n with h6 | h6
      · -- n > 201246077798729
        rcases Nat.lt_or_ge 202958252204633 n with h8 | h8
        · -- n > 202958252204633
          rcases Nat.lt_or_ge 203532728432491 n with h10 | h10
          · -- n > 203532728432491
            rcases Nat.lt_or_ge 204108331150429 n with h12 | h12
            · -- n > 204108331150429
              exact RamareSaouter2003.prime_interval_nat_ladder_c04037 n (by omega) (by omega)
            · -- n <= 204108331150429
              exact RamareSaouter2003.prime_interval_nat_ladder_c04036 n (by omega) (by omega)
          · -- n <= 203532728432491
            exact RamareSaouter2003.prime_interval_nat_ladder_c04035 n (by omega) (by omega)
        · -- n <= 202958252204633
          rcases Nat.lt_or_ge 201814689354197 n with h10 | h10
          · -- n > 201814689354197
            rcases Nat.lt_or_ge 202385412337531 n with h12 | h12
            · -- n > 202385412337531
              exact RamareSaouter2003.prime_interval_nat_ladder_c04034 n (by omega) (by omega)
            · -- n <= 202385412337531
              exact RamareSaouter2003.prime_interval_nat_ladder_c04033 n (by omega) (by omega)
          · -- n <= 201814689354197
            exact RamareSaouter2003.prime_interval_nat_ladder_c04032 n (by omega) (by omega)
      · -- n <= 201246077798729
        rcases Nat.lt_or_ge 199547173912351 n with h8 | h8
        · -- n > 199547173912351
          rcases Nat.lt_or_ge 200112137585603 n with h10 | h10
          · -- n > 200112137585603
            rcases Nat.lt_or_ge 200678324442019 n with h12 | h12
            · -- n > 200678324442019
              exact RamareSaouter2003.prime_interval_nat_ladder_c04031 n (by omega) (by omega)
            · -- n <= 200678324442019
              exact RamareSaouter2003.prime_interval_nat_ladder_c04030 n (by omega) (by omega)
          · -- n <= 200112137585603
            exact RamareSaouter2003.prime_interval_nat_ladder_c04029 n (by omega) (by omega)
        · -- n <= 199547173912351
          rcases Nat.lt_or_ge 198422262393239 n with h10 | h10
          · -- n > 198422262393239
            rcases Nat.lt_or_ge 198983939475203 n with h12 | h12
            · -- n > 198983939475203
              exact RamareSaouter2003.prime_interval_nat_ladder_c04028 n (by omega) (by omega)
            · -- n <= 198983939475203
              exact RamareSaouter2003.prime_interval_nat_ladder_c04027 n (by omega) (by omega)
          · -- n <= 198422262393239
            exact RamareSaouter2003.prime_interval_nat_ladder_c04026 n (by omega) (by omega)
  · -- n <= 197862475075933
    rcases Nat.lt_or_ge 190731505407491 n with h4 | h4
    · -- n > 190731505407491
      rcases Nat.lt_or_ge 193990012667783 n with h6 | h6
      · -- n > 193990012667783
        rcases Nat.lt_or_ge 195639854497811 n with h8 | h8
        · -- n > 195639854497811
          rcases Nat.lt_or_ge 196748558191469 n with h10 | h10
          · -- n > 196748558191469
            rcases Nat.lt_or_ge 197304210342857 n with h12 | h12
            · -- n > 197304210342857
              exact RamareSaouter2003.prime_interval_nat_ladder_c04025 n (by omega) (by omega)
            · -- n <= 197304210342857
              exact RamareSaouter2003.prime_interval_nat_ladder_c04024 n (by omega) (by omega)
          · -- n <= 196748558191469
            rcases Nat.lt_or_ge 196193212048261 n with h12 | h12
            · -- n > 196193212048261
              exact RamareSaouter2003.prime_interval_nat_ladder_c04023 n (by omega) (by omega)
            · -- n <= 196193212048261
              exact RamareSaouter2003.prime_interval_nat_ladder_c04022 n (by omega) (by omega)
        · -- n <= 195639854497811
          rcases Nat.lt_or_ge 194537406253963 n with h10 | h10
          · -- n > 194537406253963
            rcases Nat.lt_or_ge 195087808404149 n with h12 | h12
            · -- n > 195087808404149
              exact RamareSaouter2003.prime_interval_nat_ladder_c04021 n (by omega) (by omega)
            · -- n <= 195087808404149
              exact RamareSaouter2003.prime_interval_nat_ladder_c04020 n (by omega) (by omega)
          · -- n <= 194537406253963
            exact RamareSaouter2003.prime_interval_nat_ladder_c04019 n (by omega) (by omega)
      · -- n <= 193990012667783
        rcases Nat.lt_or_ge 192354535159621 n with h8 | h8
        · -- n > 192354535159621
          rcases Nat.lt_or_ge 192897285749143 n with h10 | h10
          · -- n > 192897285749143
            rcases Nat.lt_or_ge 193442582000519 n with h12 | h12
            · -- n > 193442582000519
              exact RamareSaouter2003.prime_interval_nat_ladder_c04018 n (by omega) (by omega)
            · -- n <= 193442582000519
              exact RamareSaouter2003.prime_interval_nat_ladder_c04017 n (by omega) (by omega)
          · -- n <= 192897285749143
            exact RamareSaouter2003.prime_interval_nat_ladder_c04016 n (by omega) (by omega)
        · -- n <= 192354535159621
          rcases Nat.lt_or_ge 191270441376277 n with h10 | h10
          · -- n > 191270441376277
            rcases Nat.lt_or_ge 191811856238707 n with h12 | h12
            · -- n > 191811856238707
              exact RamareSaouter2003.prime_interval_nat_ladder_c04015 n (by omega) (by omega)
            · -- n <= 191811856238707
              exact RamareSaouter2003.prime_interval_nat_ladder_c04014 n (by omega) (by omega)
          · -- n <= 191270441376277
            exact RamareSaouter2003.prime_interval_nat_ladder_c04013 n (by omega) (by omega)
    · -- n <= 190731505407491
      rcases Nat.lt_or_ge 187524698425847 n with h6 | h6
      · -- n > 187524698425847
        rcases Nat.lt_or_ge 189121238546407 n with h8 | h8
        · -- n > 189121238546407
          rcases Nat.lt_or_ge 189656490941179 n with h10 | h10
          · -- n > 189656490941179
            rcases Nat.lt_or_ge 190193301710549 n with h12 | h12
            · -- n > 190193301710549
              exact RamareSaouter2003.prime_interval_nat_ladder_c04012 n (by omega) (by omega)
            · -- n <= 190193301710549
              exact RamareSaouter2003.prime_interval_nat_ladder_c04011 n (by omega) (by omega)
          · -- n <= 189656490941179
            exact RamareSaouter2003.prime_interval_nat_ladder_c04010 n (by omega) (by omega)
        · -- n <= 189121238546407
          rcases Nat.lt_or_ge 188055276299263 n with h10 | h10
          · -- n > 188055276299263
            rcases Nat.lt_or_ge 188587290225379 n with h12 | h12
            · -- n > 188587290225379
              exact RamareSaouter2003.prime_interval_nat_ladder_c04009 n (by omega) (by omega)
            · -- n <= 188587290225379
              exact RamareSaouter2003.prime_interval_nat_ladder_c04008 n (by omega) (by omega)
          · -- n <= 188055276299263
            exact RamareSaouter2003.prime_interval_nat_ladder_c04007 n (by omega) (by omega)
      · -- n <= 187524698425847
        rcases Nat.lt_or_ge 185941990024013 n with h8 | h8
        · -- n > 185941990024013
          rcases Nat.lt_or_ge 186467430185749 n with h10 | h10
          · -- n > 186467430185749
            rcases Nat.lt_or_ge 186995363094697 n with h12 | h12
            · -- n > 186995363094697
              exact RamareSaouter2003.prime_interval_nat_ladder_c04006 n (by omega) (by omega)
            · -- n <= 186995363094697
              exact RamareSaouter2003.prime_interval_nat_ladder_c04005 n (by omega) (by omega)
          · -- n <= 186467430185749
            exact RamareSaouter2003.prime_interval_nat_ladder_c04004 n (by omega) (by omega)
        · -- n <= 185941990024013
          rcases Nat.lt_or_ge 184894584275593 n with h10 | h10
          · -- n > 184894584275593
            rcases Nat.lt_or_ge 185417754010001 n with h12 | h12
            · -- n > 185417754010001
              exact RamareSaouter2003.prime_interval_nat_ladder_c04003 n (by omega) (by omega)
            · -- n <= 185417754010001
              exact RamareSaouter2003.prime_interval_nat_ladder_c04002 n (by omega) (by omega)
          · -- n <= 184894584275593
            exact RamareSaouter2003.prime_interval_nat_ladder_c04001 n (by omega) (by omega)
