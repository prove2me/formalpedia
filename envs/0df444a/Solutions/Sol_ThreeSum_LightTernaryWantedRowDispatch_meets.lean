-- Prove2me | solution 1 for ThreeSum.LightTernaryWantedRowDispatch.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:51:29.307002+00:00
-- url     : https://prove2.me/submissions/171dc233-e2fa-47fa-b7cc-de87e8c69374

import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRowDispatch
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedRowDispatch
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryWantedRowDispatch
theorem _root_.solution {pMain pPrepare N out bankValues caps record dst fbase gbase hbase stride tail group d t : ℕ}
    (hmain : P[pMain]? = some (body pPrepare)) (f g : Config) (Qstar Q : TritWord N) (μ : ℕ → ℤ) (value : ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hrecord : record + 3 ≤ lim.space) (hdst : dst < lim.space)
    (hreadGroup : μ (record + 2) = (group : ℤ)) (hreadQ : μ (record + 1) = (address Q : ℤ))
    (hgroupWord : (group : ℤ) ≤ lim.word) (hcodeWord : (address Q : ℤ) ≤ lim.word)
    (hstrideWord : (stride : ℤ) ≤ lim.word) (htailWord : (tail : ℤ) ≤ lim.word)
    (hmulWord : (group : ℤ) * (stride : ℤ) ≤ lim.word)
    (hfWord : (fbase : ℤ) + (group : ℤ) * (stride : ℤ) + (tail : ℤ) ≤ lim.word)
    (hgWord : (gbase : ℤ) + (group : ℤ) * (stride : ℤ) + (tail : ℤ) ≤ lim.word)
    (hhWord : (hbase : ℤ) + (group : ℤ) * (stride : ℤ) ≤ lim.word)
    (hD : LightTernaryPreparedWanted.D Q f.T = LightTernaryPreparedWanted.D Qstar f.T) (hvalue : |value| ≤ lim.word)
    (hd : d < lim.depth)
    (hquery :
      Meets lim P pPrepare (d + 1)
        (LightTernaryPreparedWanted.args out (hbase + group * stride) caps (sourceConfig f fbase stride tail group)
          (sourceConfig g gbase stride tail group) Q)
        μ t (fun v ν => v = value ∧ Kept μ ν f.a)) :
    Meets lim P pMain d (args f g Qstar out bankValues caps record dst fbase gbase hbase stride tail) μ (time t)
      (fun _ ν => ∃ μ', Kept μ μ' f.a ∧ ν = Function.update μ' dst value) :=
  by
  have ha2 : ((record : ℤ) + 2).toNat = record + 2 := by omega
  have ha1 : ((record : ℤ) + 1).toNat = record + 1 := by omega
  have hmulNonneg : 0 ≤ (group : ℤ) * (stride : ℤ) := by positivity
  apply Meets.of_body hmain
  unfold body args time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen group ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryPreparedWanted.args,
            LightTernaryWantedQuery.args, LightTernaryNearPair.args, ha2, hreadGroup]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryPreparedWanted.args, LightTernaryWantedQuery.args, LightTernaryNearPair.args, ha2,
              hreadGroup] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryPreparedWanted.args,
            LightTernaryWantedQuery.args, LightTernaryNearPair.args, ha2, hreadGroup] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (address Q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryPreparedWanted.args,
            LightTernaryWantedQuery.args, LightTernaryNearPair.args, ha1, hreadQ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryPreparedWanted.args, LightTernaryWantedQuery.args, LightTernaryNearPair.args, ha1,
              hreadQ] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryPreparedWanted.args,
            LightTernaryWantedQuery.args, LightTernaryNearPair.args, ha1, hreadQ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hquery _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hquery ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryPreparedWanted.args,
            LightTernaryWantedQuery.args, LightTernaryNearPair.args, sourceConfig, hD]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryPreparedWanted.args, LightTernaryWantedQuery.args, LightTernaryNearPair.args, sourceConfig,
              hD] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryPreparedWanted.args,
            LightTernaryWantedQuery.args, LightTernaryNearPair.args, sourceConfig, hD] <;> omega)
    on_goal -1 => (rintro result ν ⟨hout, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen dst value ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout, LightTernaryPreparedWanted.args,
            LightTernaryWantedQuery.args, LightTernaryNearPair.args]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hout, LightTernaryPreparedWanted.args, LightTernaryWantedQuery.args, LightTernaryNearPair.args] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, LightTernaryPreparedWanted.args,
            LightTernaryWantedQuery.args, LightTernaryNearPair.args] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨ν, hkeep, rfl⟩
end ThreeSum.LightTernaryWantedRowDispatch
