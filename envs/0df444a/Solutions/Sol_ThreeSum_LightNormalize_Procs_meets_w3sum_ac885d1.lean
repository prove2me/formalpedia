-- Prove2me | solution 1 for ThreeSum.LightNormalize.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:30.485499+00:00
-- url     : https://prove2.me/submissions/b027e2e4-fcbd-40bf-8a82-1662c062061e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
import Theorems.Thm_ThreeSum_LightNormalize_dedup_strict
import Definitions.Def_WeightedCache3SUM_Alias_76109bf9209ef378
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_4b8a865cc96bc21c
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightNormalize
namespace Procs
theorem _root_.solution {pMain src dst work d : ℕ} {L : List ℤ} {μ : ℕ → ℤ} (C : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) (hseg : Seg μ src L) (hsep : src + L.length ≤ dst)
    (hwork : dst + L.length ≤ work) (hspace : space work L.length ≤ lim.space)
    (hd : d + L.length + Nat.clog 2 L.length + 2 ≤ lim.depth) :
    Meets lim P pMain d [src, L.length, dst, work] μ (time L.length)
      (fun r μ' =>
        ∃ out : List ℤ,
          r = (out.length : ℤ) ∧
            Seg μ' dst out ∧
              out.Pairwise (· < ·) ∧
                out.length ≤ L.length ∧
                  (∀ z, z ∈ out ↔ z ∈ L) ∧
                    ∀ a, a < work → (a < src ∨ src + L.length ≤ a) → (a < dst ∨ dst + L.length ≤ a) → μ' a = μ a) :=
  by
  apply Meets.of_body C.main
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
          ((sort_meets (d := d + 1) (a := src) (fr := work) C.sort hw h1 hseg (by omega) (by exact hspace) (by omega)) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (sort_meets (d := d + 1) (a := src) (fr := work) C.sort hw h1 hseg (by omega) (by exact hspace) (by omega)) ?_
          ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, sortTime, dedupTime, space]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [sortTime, dedupTime, space] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, sortTime, dedupTime, space] <;> omega)
    on_goal -1 =>
      (rintro unused μ₁ ⟨⟨sorted, hsortedSeg, hperm, hsorted⟩, hkeep₁⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hlen := hperm.length_eq
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
          ((dedup_meets C.dedup hw h1 sorted μ₁ src dst (d + 1) hsorted hsortedSeg (by omega)
              (by unfold space at hspace; omega) (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (dedup_meets C.dedup hw h1 sorted μ₁ src dst (d + 1) hsorted hsortedSeg (by omega)
            (by unfold space at hspace; omega) (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlen, sortTime, dedupTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hlen, sortTime, dedupTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlen, sortTime, dedupTime] <;> omega)
    on_goal -1 => (rintro count μ₂ ⟨hcount, hout, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨sorted.dedup, hcount, hout, dedup_strict hsorted, ?_, ?_, ?_⟩
  · exact (List.dedup_sublist sorted).length_le.trans hlen.le
  · intro z
    exact List.mem_dedup.trans hperm.mem_iff
  · intro a ha hsrc hdst
    change μ₂ a = μ a
    rw [hkeep₂ a (by simpa [hlen] using hdst)]
    exact hkeep₁ a ⟨ha, hsrc⟩
end Procs
end ThreeSum.LightNormalize
