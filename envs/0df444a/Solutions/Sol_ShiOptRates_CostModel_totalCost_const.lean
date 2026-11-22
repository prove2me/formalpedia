-- Prove2me | solution 1 for ShiOptRates.CostModel.totalCost_const
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:39:03.064882+00:00
-- url     : https://prove2.me/submissions/6daf5cef-dba6-4f68-8c8c-ac5f85902e18

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Cost.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; the enclosing `namespace` is replaced by `section`+`open` and the target
theorem is renamed to `solution`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic



/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L0 — Cost accounting

The piece of the library with no analogue in Mathlib or in the existing Lean
optimization formalizations: an oracle's *price list*.

A `CostModel` is a map from requested accuracy to number of queries.  A classical
minibatch mean estimator and a quantum multivariate mean estimator are two terms of this
one type, and — see `minibatch_eq_powerCost` and `quantumMean_eq_powerCost` — two members
of the same one-parameter family `PowerCost a p : cost δ = a / δ ^ p`, differing only in
the exponent `p` (`2` classical, `1` quantum).  Every rate separation proved in this
library is downstream of that single numeral.

## Main definitions

* `CostModel` — accuracy `↦` queries, nonnegative on positive accuracies.
* `CostModel.powerCost a p`, `CostModel.exact`, `CostModel.minibatch`,
  `CostModel.quantumMean` — the instances.
* `CostModel.totalCost C δ K` — `∑_{k<K} cost (δ k)`, the price of an accuracy schedule.

## Main results

* `totalCost_const` — constant schedule: `K * cost δ`.
* `totalCost_geometric` — geometric schedule against a power-law cost, in closed form.
* `totalCost_powerCost_const` — the form the rate theorems consume.
-/

section
open ShiOptRates

open Finset

section
open ShiOptRates
open ShiOptRates.CostModel

theorem solution (C : CostModel) (d : ℝ) (K : ℕ) :
    C.totalCost (fun _ => d) K = K * C.cost d := by
  simp [totalCost]

end

end
