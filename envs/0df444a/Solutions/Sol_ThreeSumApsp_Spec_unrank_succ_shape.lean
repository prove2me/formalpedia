-- Prove2me | solution 1 for ThreeSumApsp.Spec.unrank_succ_shape
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:03:58.717986+00:00
-- url     : https://prove2.me/submissions/3d7f043c-4c9c-45f1-b8d2-9e23e9f7bf03

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# The subsets of size `m` of `{1, …, L}`, enumerated

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  A subset is a *mask*: the list of `L` truth values saying
which levels belong to it, level 1 first (`maskSet`, `maskOf`).  The subsets of size `m` are
enumerated with those containing level 1 first, and so on recursively: `unrank L m r` is number `r`
in this order.

* The masks `unrank L m r` with `r < (L choose m)` have length `L` and `m` entries `true`, and they
  are distinct, because `rank` recovers `r` (`length_unrank`, `count_unrank`, `rank_unrank`).  So
  their sets of levels are distinct subsets of size `m` (`card_maskSet_unrank`,
  `eq_of_maskSet_unrank_eq`).
* A program lists them in a table without arithmetic, each mask from the one before it: the first
  mask is `true^m false^{L-m}` (`unrank_zero`), and two consecutive masks are
  `pre true false false^a true^b` and `pre false true true^b false^a` (`unrank_succ_shape`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The enumeration -/

























































/-! ## Masks and sets of levels -/


















































/-! ## From one mask to the next -/

/-- The first mask: `m` times `true`, then `L - m` times `false`. -/
theorem unrank_zero {L m : ℕ} (hm : m ≤ L) :
    unrank L m 0 = List.replicate m true ++ List.replicate (L - m) false := by
  induction L generalizing m with
  | zero => simp [unrank, Nat.le_zero.mp hm]
  | succ L ih =>
    cases m with
    | zero => simpa [unrank, List.replicate_succ] using ih (Nat.zero_le L)
    | succ m =>
      have hm' : m ≤ L := Nat.le_of_succ_le_succ hm
      simp [unrank, Nat.choose_pos hm', ih hm', List.replicate_succ]

/-- The last mask: `L - m` times `false`, then `m` times `true`. -/
private theorem unrank_last {L m : ℕ} (hm : m ≤ L) :
    unrank L m (L.choose m - 1) = List.replicate (L - m) false ++ List.replicate m true := by
  induction L generalizing m with
  | zero => simp [unrank, Nat.le_zero.mp hm]
  | succ L ih =>
    cases m with
    | zero => simpa [unrank, List.replicate_succ] using ih (Nat.zero_le L)
    | succ m =>
      rcases Nat.lt_or_ge m L with hlt | hge
      · have hpos : 0 < L.choose (m + 1) := Nat.choose_pos hlt
        have hnot : ¬ (L + 1).choose (m + 1) - 1 < L.choose m := by
          rw [Nat.choose_succ_succ']
          omega
        have hrank : (L + 1).choose (m + 1) - 1 - L.choose m = L.choose (m + 1) - 1 := by
          rw [Nat.choose_succ_succ']
          omega
        rw [unrank, if_neg hnot, hrank, ih hlt, show L + 1 - (m + 1) = L - (m + 1) + 1 by omega]
        -- `replicate (a + 1) false` is `false :: replicate a false`.
        rfl
      · obtain rfl : m = L := by omega
        simpa [unrank, List.replicate_succ] using ih le_rfl

/-- Two consecutive masks of the enumeration: write the first one as
`pre ++ [true, false] ++ false^a ++ true^b`, with the last occurrence of `true, false`; then the
next one is `pre ++ [false, true] ++ true^b ++ false^a`. -/
theorem unrank_succ_shape_sourceProof {L m r : ℕ} (hr : r + 1 < L.choose m) :
    ∃ (pre : List Bool) (a b : ℕ), L = pre.length + 2 + a + b ∧
      unrank L m r = pre ++ true :: false :: (List.replicate a false ++ List.replicate b true) ∧
      unrank L m (r + 1)
        = pre ++ false :: true :: (List.replicate b true ++ List.replicate a false) := by
  induction L generalizing m r with
  | zero => cases m <;> simp at hr
  | succ L ih =>
    cases m with
    | zero => simp at hr
    | succ m =>
      rw [Nat.choose_succ_succ'] at hr
      rcases Nat.lt_trichotomy (r + 1) (L.choose m) with hboth | hlast | hneither
      · -- Both masks contain the first level.
        obtain ⟨pre, a, b, hlen, hthis, hnext⟩ := ih hboth
        refine ⟨true :: pre, a, b, by rw [List.length_cons]; omega, ?_, ?_⟩
        · rw [unrank, if_pos (by omega), hthis, List.cons_append]
        · rw [unrank, if_pos hboth, hnext, List.cons_append]
      · -- The last mask with the first level, and the first one without it.
        have hmL : m + 1 ≤ L := by
          by_contra hcon
          rw [Nat.choose_eq_zero_of_lt (by omega : L < m + 1)] at hr
          omega
        refine ⟨[], L - m - 1, m, by rw [List.length_nil]; omega, ?_, ?_⟩
        · rw [unrank, if_pos (by omega), show r = L.choose m - 1 by omega, unrank_last (by omega),
            show L - m = L - m - 1 + 1 by omega]
          rfl
        · rw [unrank, if_neg (by omega), hlast, Nat.sub_self, unrank_zero hmL, Nat.sub_sub]
          rfl
      · -- Neither mask contains the first level.
        obtain ⟨pre, a, b, hlen, hthis, hnext⟩ := ih (m := m + 1) (r := r - L.choose m) (by omega)
        refine ⟨false :: pre, a, b, by rw [List.length_cons]; omega, ?_, ?_⟩
        · rw [unrank, if_neg (by omega), hthis, List.cons_append]
        · rw [unrank, if_neg (by omega), show r + 1 - L.choose m = r - L.choose m + 1 by omega,
            hnext, List.cons_append]

end ThreeSumApsp.Spec

end


theorem solution : ∀ {L m r : Nat},
  @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (L.choose m) →
    ∃ (pre : List.{0} Bool) (a : Nat) (b : Nat),
      And
        (@Eq.{1} Nat L
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool pre)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              a)
            b))
        (And
          (@Eq.{1} (List.{0} Bool) (ThreeSumApsp.Spec.unrank L m r)
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
              (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) pre
              (@List.cons.{0} Bool Bool.true
                (@List.cons.{0} Bool Bool.false
                  (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
                    (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool))
                    (@List.replicate.{0} Bool a Bool.false) (@List.replicate.{0} Bool b Bool.true))))))
          (@Eq.{1} (List.{0} Bool)
            (ThreeSumApsp.Spec.unrank L m
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
              (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) pre
              (@List.cons.{0} Bool Bool.false
                (@List.cons.{0} Bool Bool.true
                  (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
                    (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool))
                    (@List.replicate.{0} Bool b Bool.true) (@List.replicate.{0} Bool a Bool.false))))))) := by
  exact @ThreeSumApsp.Spec.unrank_succ_shape_sourceProof

#print axioms solution
