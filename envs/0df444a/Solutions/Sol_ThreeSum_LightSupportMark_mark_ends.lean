-- Prove2me | solution 1 for ThreeSum.LightSupportMark.mark_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:08.271365+00:00
-- url     : https://prove2.me/submissions/d3128b0e-b905-44fc-84bc-10561dabdae5

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Theorems.Thm_ThreeSum_LightSupportMark_bit_zero
import Theorems.Thm_ThreeSum_LightSupportMark_bit_succ_of_hit
import Theorems.Thm_ThreeSum_LightSupportMark_bit_succ_of_not
import Theorems.Thm_Light_Ends_forMem
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_storeLast
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightSupportMark
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSupportMark
theorem _root_.solution {μ : ℕ → ℤ} {loc : ℕ → ℤ} {keys flags dst n p : ℕ} (key valid : ℕ → ℕ) (hkeysLoc : loc 0 = keys)
    (hflagsLoc : loc 1 = flags) (hdstLoc : loc 2 = dst) (hlen : loc 3 = n) (hw : (lim.space : ℤ) ≤ lim.word)
    (hK : keys + n ≤ lim.space) (hF : flags + n ≤ lim.space) (hD : dst + p ≤ lim.space) (hsepK : Apart keys n dst p)
    (hsepF : Apart flags n dst p) (hkeys : ∀ i < n, μ (keys + i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags + i) = (valid i : ℤ)) (hkeyLt : ∀ i < n, key i < p) (hzero : ∀ r < p, μ (dst + r) = 0)
    (hword : (1 : ℤ) ≤ lim.word) :
    Ends lim P d markBody ⟨loc, μ⟩ (markTime n)
      (fun σ' => (∀ r < p, σ'.mem (dst + r) = (bit key valid r n : ℤ)) ∧ SameOutside μ σ'.mem dst p) :=
  by
  let Inv := fun i (μ' : ℕ → ℤ) => (∀ r < p, μ' (dst + r) = (bit key valid r i : ℤ)) ∧ SameOutside μ μ' dst p
  unfold markBody
  apply
    Ends.forMem Inv n 32 (hn := by omega) (hT := by
      unfold markTime
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
  · exact ⟨by simpa only [bit_zero, Nat.cast_zero] using hzero, SameOutside.refl⟩
  · intro i μ' hi hI
    obtain ⟨hbits, hsame⟩ := hI
    have hk := hkeyLt i hi
    have hkr : μ' (keys + i) = (key i : ℤ) := (hsame _ (by omega)).trans (hkeys i hi)
    have hfr : μ' (flags + i) = (valid i : ℤ) := (hsame _ (by omega)).trans (hflags i hi)
    refine
      Ends.iteLast (fun hc => ?_) (fun hc => ?_)
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflagsLoc, hfr] <;> omega))
    · have hv : valid i = 1 := by simpa [hflagsLoc, hfr] using hc
      have ha :
        ((_root_.Light.Expr.op _root_.Light.Op.add) (v 2)
                (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 5)))).val
            ⟨Function.update loc 5 (i : ℤ), μ'⟩ =
          ((dst + key i : ℕ) : ℤ) :=
        by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkeysLoc, hdstLoc, hkr] <;> omega)
      refine
        Ends.storeLast ?_
          (by (
              (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkeysLoc, hdstLoc, hkr] <;> omega))
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
        Function.update loc 5 (i : ℤ) = Function.update loc 5 (i : ℤ) ∧
          Inv (i + 1)
            (Function.update μ'
              (((_root_.Light.Expr.op _root_.Light.Op.add) (v 2)
                      (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 5)))).val
                  ⟨Function.update loc 5 (i : ℤ), μ'⟩).toNat
              1)
      rw [ha, Int.toNat_natCast]
      refine ⟨rfl, ?_, hsame.update ⟨by omega, by omega⟩ 1⟩
      intro r hr
      by_cases he : key i = r
      · subst r
        rw [bit_succ_of_hit key valid (key i) i hv rfl]
        simp
      · rw [Function.update_of_ne (by omega), hbits r hr]
        rw [bit_succ_of_not key valid r i (by tauto)]
    · have hv : valid i ≠ 1 := by simpa [hflagsLoc, hfr] using hc
      apply Ends.skip
      refine ⟨rfl, ?_, hsame⟩
      intro r hr
      rw [bit_succ_of_not key valid r i (by tauto)]
      exact hbits r hr
  · intro μ' hI
    exact hI
  · intro i μ' hi hI
    simp [hlen]
end ThreeSum.LightSupportMark
