-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedHistogram.count_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:37:19.335146+00:00
-- url     : https://prove2.me/submissions/21564838-36fd-4a61-ac7d-6f5f347a2595

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_succ
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_abs_le
import Theorems.Thm_Light_Ends_forMem
import Theorems.Thm_Light_Ends_storeLast
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryWeightedHistogram
theorem _root_.solution {μ : ℕ → ℤ} {loc : ℕ → ℤ} {keys pairs source n dst bank sourceCount U : ℕ}
    (key position : ℕ → ℕ) (weight : ℕ → ℤ)
    (hloc : loc 0 = keys ∧ loc 1 = pairs ∧ loc 2 = source ∧ loc 3 = n ∧ loc 4 = dst) (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys + n ≤ dst) (hpairs : pairs + 2 * n ≤ dst) (hsource : source + sourceCount ≤ dst)
    (hdst : dst + bank ≤ lim.space) (hkeyRead : ∀ i < n, μ (keys + i) = (key i : ℤ))
    (hposRead : ∀ i < n, μ (pairs + 2 * i) = (position i : ℤ))
    (hsourceRead : ∀ i < n, μ (source + position i) = weight i) (hkeyLt : ∀ i < n, key i < bank)
    (hposLt : ∀ i < n, position i < sourceCount) (hzero : ∀ r < bank, μ (dst + r) = 0)
    (hweights : ∀ i < n, |weight i| ≤ U) (hword : ((n + 1 : ℕ) : ℤ) * U ≤ lim.word) :
    Ends lim P d countBody ⟨loc, μ⟩ (countTime n)
      (fun σ' => (∀ r < bank, σ'.mem (dst + r) = total key weight r n) ∧ SameOutside μ σ'.mem dst bank) :=
  by
  rcases hloc with ⟨hl0, hl1, hl2, hl3, hl4⟩
  let Inv := fun i (ν : ℕ → ℤ) => (∀ r < bank, ν (dst + r) = total key weight r i) ∧ SameOutside μ ν dst bank
  unfold countBody
  apply
    Ends.forMem Inv n 30 (hn := by omega) (hT := by
      unfold countTime
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  · exact ⟨by simpa only [total_zero] using hzero, fun _ _ => rfl⟩
  · intro i ν hi hI
    rcases hI with ⟨hcounts, hkeep⟩
    have hkeyi := hkeyLt i hi
    have hposi := hposLt i hi
    have hkread : ν (keys + i) = (key i : ℤ) := (hkeep _ (Or.inl (by omega))).trans (hkeyRead i hi)
    have hpread : ν (pairs + 2 * i) = (position i : ℤ) := (hkeep _ (Or.inl (by omega))).trans (hposRead i hi)
    have hsread : ν (source + position i) = weight i := (hkeep _ (Or.inl (by omega))).trans (hsourceRead i hi)
    have hcell := hcounts (key i) hkeyi
    have hsum := total_abs_le key weight (key i) i U (fun j hj => hweights j (by omega))
    have hwi := hweights i hi
    have hval : |total key weight (key i) i + weight i| ≤ lim.word :=
      by
      have hh : |total key weight (key i) i + weight i| ≤ (i : ℤ) * U + U :=
        (abs_add_le _ _).trans (add_le_add hsum hwi)
      have hnword : (i : ℤ) * U + U ≤ ((n + 1 : ℕ) : ℤ) * U :=
        by
        have hii : (i : ℤ) + 1 ≤ ((n + 1 : ℕ) : ℤ) := by omega
        nlinarith [Int.natCast_nonneg U]
      exact hh.trans (hnword.trans hword)
    have hvalbounds := abs_le.mp hval
    have hwiWord : |weight i| ≤ lim.word :=
      by
      have hU : (U : ℤ) ≤ ((n + 1 : ℕ) : ℤ) * U :=
        by
        have hh := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) by omega) (Int.natCast_nonneg U)
        simpa using hh
      exact hwi.trans (hU.trans hword)
    have hwiBounds := abs_le.mp hwiWord
    have hpairAddr : ((pairs : ℤ) + 2 * (i : ℤ)).toNat = pairs + 2 * i := by norm_cast
    have hsourceAddr : ((source : ℤ) + (position i : ℤ)).toNat = source + position i := by norm_cast
    have hkeyAddr : ((dst : ℤ) + (key i : ℤ)).toNat = dst + key i := by norm_cast
    have ha :
      ((_root_.Light.Expr.op _root_.Light.Op.add) (v 4)
              (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 7)))).val
          ⟨Function.update loc 7 (i : ℤ), ν⟩ =
        ((dst + key i : ℕ) : ℤ) :=
      by simp [Expr.val, v, k, M, hl0, hl4, hkread]
    have hv :
      ((_root_.Light.Expr.op _root_.Light.Op.add)
              (M
                ((_root_.Light.Expr.op _root_.Light.Op.add) (v 4)
                  (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 7)))))
              (M
                ((_root_.Light.Expr.op _root_.Light.Op.add) (v 2)
                  (M
                    ((_root_.Light.Expr.op _root_.Light.Op.add) (v 1)
                      ((_root_.Light.Expr.op _root_.Light.Op.mul) (k 2) (v 7))))))).val
          ⟨Function.update loc 7 (i : ℤ), ν⟩ =
        total key weight (key i) i + weight i :=
      by simp [Expr.val, v, k, M, hl0, hl1, hl2, hl4, hkread, hpread, hsread, hcell, hpairAddr, hsourceAddr, hkeyAddr]
    refine
      Ends.storeLast ?_
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl0, hl1, hl2, hl4, hkread, hpread, hsread,
                hcell, hpairAddr, hsourceAddr, hkeyAddr, ha, hv] <;>
              omega))
        (by
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | (ring_nf; omega)))
    change
      Function.update loc 7 (i : ℤ) = Function.update loc 7 (i : ℤ) ∧
        Inv (i + 1)
          (Function.update ν
            (((_root_.Light.Expr.op _root_.Light.Op.add) (v 4)
                    (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 7)))).val
                ⟨Function.update loc 7 (i : ℤ), ν⟩).toNat
            (((_root_.Light.Expr.op _root_.Light.Op.add)
                  (M
                    ((_root_.Light.Expr.op _root_.Light.Op.add) (v 4)
                      (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 7)))))
                  (M
                    ((_root_.Light.Expr.op _root_.Light.Op.add) (v 2)
                      (M
                        ((_root_.Light.Expr.op _root_.Light.Op.add) (v 1)
                          ((_root_.Light.Expr.op _root_.Light.Op.mul) (k 2) (v 7))))))).val
              ⟨Function.update loc 7 (i : ℤ), ν⟩))
    rw [ha, hv, Int.toNat_natCast]
    refine ⟨rfl, ?_, ?_⟩
    · intro r hr
      rw [total_succ]
      by_cases he : key i = r
      · subst r
        simp
      · rw [Function.update_of_ne (by omega), hcounts r hr]
        simp [he]
    · intro a hx
      rw [Function.update_of_ne (by omega)]
      exact hkeep a hx
  · intro ν hI
    exact hI
  · intro i ν hi hI
    simp [hl3]
end ThreeSum.LightTernaryWeightedHistogram
