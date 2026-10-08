-- Prove2me | solution 1 for ThreeSumApsp.Spec.ctrAt_succ
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:01.154262+00:00
-- url     : https://prove2.me/submissions/774410ce-be07-4ae9-b125-82bc32ae316c

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Counters
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Mathlib.Algebra.Order.Ring.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/











/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/

































/-! ## The next index -/

/-- The next index, if it is in the same row. -/
theorem succ_div_mod_of_lt {n i : ℕ} (h : i % n + 1 < n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by
  have hsucc : i + 1 = i / n * n + (i % n + 1) := by rw [← Nat.add_assoc, Nat.div_add_mod']
  exact ⟨by rw [hsucc, mul_add_div_of_lt h], by rw [hsucc, Nat.mul_add_mod_of_lt h]⟩






/-- After the last index of a row comes the first index of the next row. -/
theorem succ_div_mod_of_eq {n i : ℕ} (h : i % n + 1 = n) :
    (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0 := by
  have hn : 0 < n := h ▸ Nat.succ_pos _
  have hsucc : i + 1 = (i / n + 1) * n + 0 := by
    have hdivmod := Nat.div_add_mod' i n
    rw [Nat.succ_mul]
    -- `i = i / n * n + i % n` and `i % n + 1 = n`
    omega
  exact ⟨by rw [hsucc, mul_add_div_of_lt hn], by rw [hsucc, Nat.mul_add_mod_of_lt hn]⟩

end Nat

namespace Int

/-! ## Residues as natural numbers -/










end Int

end



/-!
# Quotients and remainders by counters

The word RAM has no division.  A program that runs through the rows `I = 0, 1, …, N - 1` of a matrix
can still know, for each row, its band, its block within the band and its offset within the block
(Section 2.3.4), that is `I / (K₀ N₀)`, `I / N₀ % K₀` and `I % N₀`: it keeps three counters and
steps them (`stepCtr`, `ctrAt_succ`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec




















/-- Stepping the counters of row `I` gives the counters of row `I + 1`. -/
theorem ctrAt_succ_sourceProof {k₀ n₀ : ℕ} (hk : 0 < k₀) (hn : 0 < n₀) (I : ℕ) :
    ctrAt k₀ n₀ (I + 1) = stepCtr k₀ n₀ (ctrAt k₀ n₀ I) := by
  have hoff_lt : I % n₀ < n₀ := Nat.mod_lt I hn
  have hblock_lt : I / n₀ % k₀ < k₀ := Nat.mod_lt _ hk
  simp only [ctrAt, stepCtr, Nat.mul_comm k₀ n₀, ← Nat.div_div_eq_div_mul]
  split_ifs with hoff hlt
  · -- The next row of the same block.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_lt hoff
    rw [hdiv, hmod]
  · -- The first row of the next block of the same band.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_eq (show I % n₀ + 1 = n₀ by omega)
    obtain ⟨hband, hblock⟩ := Nat.succ_div_mod_of_lt hlt
    rw [hdiv, hmod, hband, hblock]
  · -- The first row of the first block of the next band.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_eq (show I % n₀ + 1 = n₀ by omega)
    obtain ⟨hband, hblock⟩ := Nat.succ_div_mod_of_eq (show I / n₀ % k₀ + 1 = k₀ by omega)
    rw [hdiv, hmod, hband, hblock]

end ThreeSumApsp.Spec

end


theorem solution : ∀ {k₀ n₀ : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k₀ →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n₀ →
      ∀ (I : Nat),
        @Eq.{1} ThreeSumApsp.Spec.Ctr
          (ThreeSumApsp.Spec.ctrAt k₀ n₀
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) I
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (ThreeSumApsp.Spec.stepCtr k₀ n₀ (ThreeSumApsp.Spec.ctrAt k₀ n₀ I)) := by
  exact @ThreeSumApsp.Spec.ctrAt_succ_sourceProof

#print axioms solution
