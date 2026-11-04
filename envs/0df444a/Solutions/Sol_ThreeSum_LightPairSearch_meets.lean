-- Prove2me | solution 1 for ThreeSum.LightPairSearch.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:46.829963+00:00
-- url     : https://prove2.me/submissions/5a19132b-fc6d-40c6-ae5e-e67d5f4112e2

import Definitions.Def_Submission_ThreeSum_LightPairSearch
import Definitions.Def_Submission_ThreeSum_LightPairSearchMain
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightPairSearch_first_le
import Theorems.Thm_ThreeSum_LightPairSearch_row_meets
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightPairSearch
theorem _root_.solution {pMain pRow pPred q ctx T d : ℕ} (hmain : P[pMain]? = some (body pRow))
    (hrow : P[pRow]? = some (rowBody pPred)) (good : ℕ → ℕ → Prop) [DecidableRel good] (I : (ℕ → ℤ) → Prop) (hq : 0 < q)
    (μ : ℕ → ℤ) (hI : I μ) (hword : ((q * q + q + ctx + 20 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hpred :
      ∀ u < q,
        ∀ v < q,
          ∀ ν, I ν → Meets lim P pPred (d + 2) [u, v, ctx] ν T (fun r ξ => r = (if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim P pMain d [q, ctx] μ (time q T) (fun r ν => r = (first (goodCode q good) (q * q) : ℤ) ∧ I ν) :=
  by
  have hqW : (q : ℤ) ≤ lim.word := by omega
  have hctxW : (ctx : ℤ) ≤ lim.word := by omega
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rowTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [rowTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rowTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := q * (rowTime q T + 60) + 10) (Q := Inv I q ctx good q) (Inv I q ctx good) q (rowTime q T + 40) ?_
        ?_ ?_ ?_ (hT := by
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
              | (ring_nf; omega))))
      ?_ (hT := by
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
  · exact ⟨μ, by simp [Inv, first, update_frame_setLocal], hI⟩
  · rintro i _ hi _ ⟨ν, rfl, hν⟩
    have hcode : i * q ≤ q * q := Nat.mul_le_mul_right q (by omega)
    have hpref := first_le (goodCode q good) (i * q)
    have hiW : (i : ℤ) ≤ lim.word := by omega
    have hcall := row_meets (d := d + 1) hrow good I hq hi ν hν hword (by omega) (fun v hv ξ hξ => hpred i hi v hv ξ hξ)
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
      | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      on_goal -1 => (rintro result ξ ⟨hr, hξ⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, ξ, ?_, hξ⟩
    simp [setLocal, hr, update_frame_setLocal]
  · intro σ _ hshape; exact hshape
  · rintro i _ hi _ ⟨ν, rfl, hν⟩; simp
  · rintro σ ⟨ν, rfl, hν⟩
    have hpref := first_le (goodCode q good) (q * q)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (first (goodCode q good) (q * q) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, hν⟩
end ThreeSum.LightPairSearch
