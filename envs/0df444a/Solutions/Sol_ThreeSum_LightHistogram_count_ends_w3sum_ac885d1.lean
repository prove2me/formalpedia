-- Prove2me | solution 1 for ThreeSum.LightHistogram.count_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:00.849255+00:00
-- url     : https://prove2.me/submissions/5f03e410-0ea1-4ab9-af76-7651d8ecdc89

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_succ
import Theorems.Thm_Light_Ends_forMem
import Theorems.Thm_Light_Ends_storeLast
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightHistogram
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightHistogram
theorem _root_.solution {μ : ℕ → ℤ} {loc : ℕ → ℤ} {src dst n p : ℕ} (key : ℕ → ℕ) (hsrc : loc 0 = src)
    (hdst : loc 1 = dst) (hlen : loc 2 = n) (hw : (lim.space : ℤ) ≤ lim.word) (hS : src + n ≤ lim.space)
    (hD : dst + p ≤ lim.space) (hsep : Apart src n dst p) (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p) (hzero : ∀ r < p, μ (dst + r) = 0) :
    Ends lim P d countBody ⟨loc, μ⟩ (countTime n) fun σ' =>
      (∀ r < p, σ'.mem (dst + r) = count key r n) ∧ SameOutside μ σ'.mem dst p :=
  by
  let Inv := fun i (μ' : ℕ → ℤ) => (∀ r < p, μ' (dst + r) = count key r i) ∧ SameOutside μ μ' dst p
  unfold countBody
  apply
    Ends.forMem Inv n 16 (hn := by omega) (hT := by
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
  · exact ⟨by simpa only [count_zero, Nat.cast_zero] using hzero, fun _ _ => rfl⟩
  · intro i μ' hi hI
    obtain ⟨hcnt, hsame⟩ := hI
    have hki := hkeyLt i hi
    have hread : μ' (src + i) = key i := (hsame _ (by omega)).trans (hkeys i hi)
    have hcell := hcnt (key i) hki
    have hcount := count_le key (key i) i
    have hq0 : (0 : ℤ) ≤ count key (key i) i := Int.natCast_nonneg _
    have hqle : (count key (key i) i : ℤ) < n := by exact_mod_cast hcount.trans_lt hi
    have ha :
      ((_root_.Light.Expr.op _root_.Light.Op.add) (v 1)
              (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 4)))).val
          ⟨Function.update loc 4 (i : ℤ), μ'⟩ =
        ((dst + key i : ℕ) : ℤ) :=
      by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsrc, hdst, hread] <;> omega)
    have hv :
      ((_root_.Light.Expr.op _root_.Light.Op.add)
              (M
                ((_root_.Light.Expr.op _root_.Light.Op.add) (v 1)
                  (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 4)))))
              (k 1)).val
          ⟨Function.update loc 4 (i : ℤ), μ'⟩ =
        ((count key (key i) i + 1 : ℕ) : ℤ) :=
      by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsrc, hdst, hread, hcell] <;> omega)
    refine
      Ends.storeLast ?_
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsrc, hdst, hread, hcell] <;> omega))
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
      Function.update loc 4 (i : ℤ) = Function.update loc 4 (i : ℤ) ∧
        Inv (i + 1)
          (Function.update μ'
            (((_root_.Light.Expr.op _root_.Light.Op.add) (v 1)
                    (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 4)))).val
                ⟨Function.update loc 4 (i : ℤ), μ'⟩).toNat
            (((_root_.Light.Expr.op _root_.Light.Op.add)
                  (M
                    ((_root_.Light.Expr.op _root_.Light.Op.add) (v 1)
                      (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 4)))))
                  (k 1)).val
              ⟨Function.update loc 4 (i : ℤ), μ'⟩))
    rw [ha, hv, Int.toNat_natCast]
    refine ⟨rfl, ?_, ?_⟩
    · intro r hr
      rw [count_succ]
      by_cases heq : key i = r
      · subst r
        simp [Function.update_self]
      · rw [Function.update_of_ne (by omega), hcnt r hr]
        simp [heq]
    · intro a ha
      rw [Function.update_of_ne (by omega)]
      exact hsame a ha
  · intro μ' hI
    exact hI
  · intro i μ' hi hI
    simp [hlen]
end ThreeSum.LightHistogram
