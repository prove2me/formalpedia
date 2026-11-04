-- Prove2me | solution 1 for ThreeSum.LightSupportMark.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:37.443809+00:00
-- url     : https://prove2.me/submissions/b701fb72-da5d-482e-95ba-ed6f217599d0

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Theorems.Thm_ThreeSum_LightSupportMark_mark_ends
import Theorems.Thm_Light_Ends_pieceLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_fill_meets
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
theorem _root_.solution {pMain pFill : ℕ} (hmain : P[pMain]? = some (body pFill)) (hfill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {keys flags dst n p : ℕ} (key valid : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hK : keys + n ≤ lim.space) (hF : flags + n ≤ lim.space) (hD : dst + p ≤ lim.space) (hsepK : Apart keys n dst p)
    (hsepF : Apart flags n dst p) (hkeys : ∀ i < n, μ (keys + i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags + i) = (valid i : ℤ)) (hkeyLt : ∀ i < n, key i < p) (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [keys, flags, dst, n, p] μ (time n p)
      (fun _ μ' => (∀ r < p, μ' (dst + r) = (bit key valid r n : ℤ)) ∧ SameOutside μ μ' dst p) :=
  by
  apply Meets.of_body hmain
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((fill_meets (d := d + 1) (μ := μ) (dst := dst) (n := p) (x := 0) hfill hw hD) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (fill_meets (d := d + 1) (μ := μ) (dst := dst) (n := p) (x := 0) hfill hw hD) ?_ ?_
          ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, markTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [markTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, markTime] <;> omega)
    on_goal -1 => (rintro v μ₁ ⟨hfilled, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkr : ∀ i < n, μ₁ (keys + i) = (key i : ℤ) := by
    intro i hi
    exact (hkept _ (by omega)).trans (hkeys i hi)
  have hfr : ∀ i < n, μ₁ (flags + i) = (valid i : ℤ) :=
    by
    intro i hi
    exact (hkept _ (by omega)).trans (hflags i hi)
  have hzero : ∀ r < p, μ₁ (dst + r) = 0 := by
    intro r hr
    exact (hfilled r (by simpa using hr)).trans (List.getElem_replicate ..)
  apply
    Ends.pieceLast
      (mark_ends key valid (by simp) (by simp) (by simp) (by simp) hw hK hF hD hsepK hsepF hkr hfr hkeyLt hzero hword)
  · intro σ' hpost
    exact ⟨hpost.1, fun a ha => (hpost.2 a ha).trans (hkept a ha)⟩
end ThreeSum.LightSupportMark
