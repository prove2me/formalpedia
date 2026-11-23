-- Prove2me | solution 1 for SparsestCutOracle.Main.balanced_sparsest_cut_oracle
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:21:30.603238+00:00
-- url     : https://prove2.me/submissions/ce98dc29-931a-43d4-b4bc-ff9cb7629ffa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SparsestCutOracle_Main_Guarantees
import Theorems.Thm_SparsestCutOracle_Main_zero_weights_reduction
import Theorems.Thm_SparsestCutOracle_Main_balanced_sparsest_cut_oracle_positive

open SparsestCutOracle.Main

theorem solution : BalancedOracle false :=
  zero_weights_reduction balanced_sparsest_cut_oracle_positive
