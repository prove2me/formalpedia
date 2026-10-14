-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp123
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T21:00:29.048898+00:00
-- url     : https://prove2.me/submissions/0e762a9b-31d3-4470-8e43-708b0b240c12

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06150

theorem solution (n : Nat)
    (hn : 69756529594900877 < n) (hupper : n <= 80348244495624299) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 74865292066841971 n with h2 | h2
  · -- n > 74865292066841971
    rcases Nat.lt_or_ge 77448740822715347 n with h4 | h4
    · -- n > 77448740822715347
      rcases Nat.lt_or_ge 78773737232624129 n with h6 | h6
      · -- n > 78773737232624129
        rcases Nat.lt_or_ge 79444702927524017 n with h8 | h8
        · -- n > 79444702927524017
          rcases Nat.lt_or_ge 79895198514379657 n with h10 | h10
          · -- n > 79895198514379657
            rcases Nat.lt_or_ge 80121404594853143 n with h12 | h12
            · -- n > 80121404594853143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06150 n (by omega) (by omega)
            · -- n <= 80121404594853143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06149 n (by omega) (by omega)
          · -- n <= 79895198514379657
            rcases Nat.lt_or_ge 79669631768234941 n with h12 | h12
            · -- n > 79669631768234941
              exact RamareSaouter2003.prime_interval_nat_ladder_c06148 n (by omega) (by omega)
            · -- n <= 79669631768234941
              exact RamareSaouter2003.prime_interval_nat_ladder_c06147 n (by omega) (by omega)
        · -- n <= 79444702927524017
          rcases Nat.lt_or_ge 78996763197683677 n with h10 | h10
          · -- n > 78996763197683677
            rcases Nat.lt_or_ge 79220412923187551 n with h12 | h12
            · -- n > 79220412923187551
              exact RamareSaouter2003.prime_interval_nat_ladder_c06146 n (by omega) (by omega)
            · -- n <= 79220412923187551
              exact RamareSaouter2003.prime_interval_nat_ladder_c06145 n (by omega) (by omega)
          · -- n <= 78996763197683677
            exact RamareSaouter2003.prime_interval_nat_ladder_c06144 n (by omega) (by omega)
      · -- n <= 78773737232624129
        rcases Nat.lt_or_ge 78108436861549141 n with h8 | h8
        · -- n > 78108436861549141
          rcases Nat.lt_or_ge 78329581564398821 n with h10 | h10
          · -- n > 78329581564398821
            rcases Nat.lt_or_ge 78551350521927221 n with h12 | h12
            · -- n > 78551350521927221
              exact RamareSaouter2003.prime_interval_nat_ladder_c06143 n (by omega) (by omega)
            · -- n <= 78551350521927221
              exact RamareSaouter2003.prime_interval_nat_ladder_c06142 n (by omega) (by omega)
          · -- n <= 78329581564398821
            exact RamareSaouter2003.prime_interval_nat_ladder_c06141 n (by omega) (by omega)
        · -- n <= 78108436861549141
          rcases Nat.lt_or_ge 77668021727500189 n with h10 | h10
          · -- n > 77668021727500189
            rcases Nat.lt_or_ge 77887921278766331 n with h12 | h12
            · -- n > 77887921278766331
              exact RamareSaouter2003.prime_interval_nat_ladder_c06140 n (by omega) (by omega)
            · -- n <= 77887921278766331
              exact RamareSaouter2003.prime_interval_nat_ladder_c06139 n (by omega) (by omega)
          · -- n <= 77668021727500189
            exact RamareSaouter2003.prime_interval_nat_ladder_c06138 n (by omega) (by omega)
    · -- n <= 77448740822715347
      rcases Nat.lt_or_ge 76146055298132987 n with h6 | h6
      · -- n > 76146055298132987
        rcases Nat.lt_or_ge 76794655218950311 n with h8 | h8
        · -- n > 76794655218950311
          rcases Nat.lt_or_ge 77012073076039831 n with h10 | h10
          · -- n > 77012073076039831
            rcases Nat.lt_or_ge 77230113975275389 n with h12 | h12
            · -- n > 77230113975275389
              exact RamareSaouter2003.prime_interval_nat_ladder_c06137 n (by omega) (by omega)
            · -- n <= 77230113975275389
              exact RamareSaouter2003.prime_interval_nat_ladder_c06136 n (by omega) (by omega)
          · -- n <= 77012073076039831
            exact RamareSaouter2003.prime_interval_nat_ladder_c06135 n (by omega) (by omega)
        · -- n <= 76794655218950311
          rcases Nat.lt_or_ge 76361642358846001 n with h10 | h10
          · -- n > 76361642358846001
            rcases Nat.lt_or_ge 76577842454436847 n with h12 | h12
            · -- n > 76577842454436847
              exact RamareSaouter2003.prime_interval_nat_ladder_c06134 n (by omega) (by omega)
            · -- n <= 76577842454436847
              exact RamareSaouter2003.prime_interval_nat_ladder_c06133 n (by omega) (by omega)
          · -- n <= 76361642358846001
            exact RamareSaouter2003.prime_interval_nat_ladder_c06132 n (by omega) (by omega)
      · -- n <= 76146055298132987
        rcases Nat.lt_or_ge 75502946084483231 n with h8 | h8
        · -- n > 75502946084483231
          rcases Nat.lt_or_ge 75716711203977941 n with h10 | h10
          · -- n > 75716711203977941
            rcases Nat.lt_or_ge 75931082176562861 n with h12 | h12
            · -- n > 75931082176562861
              exact RamareSaouter2003.prime_interval_nat_ladder_c06131 n (by omega) (by omega)
            · -- n <= 75931082176562861
              exact RamareSaouter2003.prime_interval_nat_ladder_c06130 n (by omega) (by omega)
          · -- n <= 75716711203977941
            exact RamareSaouter2003.prime_interval_nat_ladder_c06129 n (by omega) (by omega)
        · -- n <= 75502946084483231
          rcases Nat.lt_or_ge 75077250129950539 n with h10 | h10
          · -- n > 75077250129950539
            rcases Nat.lt_or_ge 75289782187071091 n with h12 | h12
            · -- n > 75289782187071091
              exact RamareSaouter2003.prime_interval_nat_ladder_c06128 n (by omega) (by omega)
            · -- n <= 75289782187071091
              exact RamareSaouter2003.prime_interval_nat_ladder_c06127 n (by omega) (by omega)
          · -- n <= 75077250129950539
            exact RamareSaouter2003.prime_interval_nat_ladder_c06126 n (by omega) (by omega)
  · -- n <= 74865292066841971
    rcases Nat.lt_or_ge 72163727869604401 n with h4 | h4
    · -- n > 72163727869604401
      rcases Nat.lt_or_ge 73398249828067327 n with h6 | h6
      · -- n > 73398249828067327
        rcases Nat.lt_or_ge 74023433021317477 n with h8 | h8
        · -- n > 74023433021317477
          rcases Nat.lt_or_ge 74443163171229907 n with h10 | h10
          · -- n > 74443163171229907
            rcases Nat.lt_or_ge 74653933091212957 n with h12 | h12
            · -- n > 74653933091212957
              exact RamareSaouter2003.prime_interval_nat_ladder_c06125 n (by omega) (by omega)
            · -- n <= 74653933091212957
              exact RamareSaouter2003.prime_interval_nat_ladder_c06124 n (by omega) (by omega)
          · -- n <= 74443163171229907
            rcases Nat.lt_or_ge 74233009450297267 n with h12 | h12
            · -- n > 74233009450297267
              exact RamareSaouter2003.prime_interval_nat_ladder_c06123 n (by omega) (by omega)
            · -- n <= 74233009450297267
              exact RamareSaouter2003.prime_interval_nat_ladder_c06122 n (by omega) (by omega)
        · -- n <= 74023433021317477
          rcases Nat.lt_or_ge 73606050642981949 n with h10 | h10
          · -- n > 73606050642981949
            rcases Nat.lt_or_ge 73814450610939061 n with h12 | h12
            · -- n > 73814450610939061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06121 n (by omega) (by omega)
            · -- n <= 73814450610939061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06120 n (by omega) (by omega)
          · -- n <= 73606050642981949
            exact RamareSaouter2003.prime_interval_nat_ladder_c06119 n (by omega) (by omega)
      · -- n <= 73398249828067327
        rcases Nat.lt_or_ge 72778374079267237 n with h8 | h8
        · -- n > 72778374079267237
          rcases Nat.lt_or_ge 72984390040308091 n with h10 | h10
          · -- n > 72984390040308091
            rcases Nat.lt_or_ge 73191027880628227 n with h12 | h12
            · -- n > 73191027880628227
              exact RamareSaouter2003.prime_interval_nat_ladder_c06118 n (by omega) (by omega)
            · -- n <= 73191027880628227
              exact RamareSaouter2003.prime_interval_nat_ladder_c06117 n (by omega) (by omega)
          · -- n <= 72984390040308091
            exact RamareSaouter2003.prime_interval_nat_ladder_c06116 n (by omega) (by omega)
        · -- n <= 72778374079267237
          rcases Nat.lt_or_ge 72368038752739567 n with h10 | h10
          · -- n > 72368038752739567
            rcases Nat.lt_or_ge 72572905699447807 n with h12 | h12
            · -- n > 72572905699447807
              exact RamareSaouter2003.prime_interval_nat_ladder_c06115 n (by omega) (by omega)
            · -- n <= 72572905699447807
              exact RamareSaouter2003.prime_interval_nat_ladder_c06114 n (by omega) (by omega)
          · -- n <= 72368038752739567
            exact RamareSaouter2003.prime_interval_nat_ladder_c06113 n (by omega) (by omega)
    · -- n <= 72163727869604401
      rcases Nat.lt_or_ge 70949920701705407 n with h6 | h6
      · -- n > 70949920701705407
        rcases Nat.lt_or_ge 71554261463640031 n with h8 | h8
        · -- n > 71554261463640031
          rcases Nat.lt_or_ge 71756837237013959 n with h10 | h10
          · -- n > 71756837237013959
            rcases Nat.lt_or_ge 71959997111053939 n with h12 | h12
            · -- n > 71959997111053939
              exact RamareSaouter2003.prime_interval_nat_ladder_c06112 n (by omega) (by omega)
            · -- n <= 71959997111053939
              exact RamareSaouter2003.prime_interval_nat_ladder_c06111 n (by omega) (by omega)
          · -- n <= 71756837237013959
            exact RamareSaouter2003.prime_interval_nat_ladder_c06110 n (by omega) (by omega)
        · -- n <= 71554261463640031
          rcases Nat.lt_or_ge 71150799587673181 n with h10 | h10
          · -- n > 71150799587673181
            rcases Nat.lt_or_ge 71352245022393743 n with h12 | h12
            · -- n > 71352245022393743
              exact RamareSaouter2003.prime_interval_nat_ladder_c06109 n (by omega) (by omega)
            · -- n <= 71352245022393743
              exact RamareSaouter2003.prime_interval_nat_ladder_c06108 n (by omega) (by omega)
          · -- n <= 71150799587673181
            exact RamareSaouter2003.prime_interval_nat_ladder_c06107 n (by omega) (by omega)
      · -- n <= 70949920701705407
        rcases Nat.lt_or_ge 70350703493094203 n with h8 | h8
        · -- n > 70350703493094203
          rcases Nat.lt_or_ge 70549885565107357 n with h10 | h10
          · -- n > 70549885565107357
            rcases Nat.lt_or_ge 70749612026905051 n with h12 | h12
            · -- n > 70749612026905051
              exact RamareSaouter2003.prime_interval_nat_ladder_c06106 n (by omega) (by omega)
            · -- n <= 70749612026905051
              exact RamareSaouter2003.prime_interval_nat_ladder_c06105 n (by omega) (by omega)
          · -- n <= 70549885565107357
            exact RamareSaouter2003.prime_interval_nat_ladder_c06104 n (by omega) (by omega)
        · -- n <= 70350703493094203
          rcases Nat.lt_or_ge 69954021933458609 n with h10 | h10
          · -- n > 69954021933458609
            rcases Nat.lt_or_ge 70152082148563633 n with h12 | h12
            · -- n > 70152082148563633
              exact RamareSaouter2003.prime_interval_nat_ladder_c06103 n (by omega) (by omega)
            · -- n <= 70152082148563633
              exact RamareSaouter2003.prime_interval_nat_ladder_c06102 n (by omega) (by omega)
          · -- n <= 69954021933458609
            exact RamareSaouter2003.prime_interval_nat_ladder_c06101 n (by omega) (by omega)
