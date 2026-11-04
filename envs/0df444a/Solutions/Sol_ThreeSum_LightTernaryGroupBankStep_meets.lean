-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupBankStep.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:30:24.155284+00:00
-- url     : https://prove2.me/submissions/b8d702d0-c5bd-437f-a3a1-4d5b873bacdf

import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankStep
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_copy_meets
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}
namespace ThreeSum.LightTernaryGroupBankStep
theorem _root_.solution {tail : Program}
    {pMain pCopy N T n a powers L keyBase fsource gsource fbase gbase hbase d V : ℕ}
    (hmain : (LightTernaryBankAssembly.program ++ tail)[pMain]? = some (body pCopy))
    (hcopy : (LightTernaryBankAssembly.program ++ tail)[pCopy]? = some copyBody) (E : Enumeration N T n)
    (F G : TritWord N → ℤ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ keyBase)
    (hfs : fsource + n ≤ keyBase) (hgs : gsource + n ≤ keyBase) (hmeta : keyBase + 4 * n ≤ powers)
    (hpows : powers + (2 * N + 1) ≤ fbase) (hfg : fbase + (N + 1) * n ≤ gbase) (hgh : gbase + (N + 1) * n ≤ hbase)
    (hspace : hbase + (N + 1) * n ≤ lim.space) (hword : ((n + 2 ^ (2 * N + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hNword : 2 * (N : ℤ) + 3 ≤ lim.word) (hcodes : ∀ j < n, μ (a + j) = (address (E.word j) : ℤ))
    (hsourceF : ∀ j < n, μ (fsource + j) = F (E.word j)) (hsourceG : ∀ j < n, μ (gsource + j) = G (E.word j))
    (hpowers : Powers μ powers (2 * N)) (hsorted : ∀ j k, j < k → k < n → address (E.word j) < address (E.word k))
    (hF : ∀ R, |F R| ≤ (V : ℤ)) (hG : ∀ R, |G R| ≤ (V : ℤ)) (hforwardWord : 4 * ((4 ^ N * V : ℕ) : ℤ) + 3 ≤ lim.word)
    (hproductWord : (LightTernaryBankAssembly.valueBound N V : ℤ) ≤ lim.word)
    (hinverseWord : 4 * ((4 ^ N * LightTernaryBankAssembly.valueBound N V : ℕ) : ℤ) + 3 ≤ lim.word) (hL : L ≤ 2 * N)
    (hn : n < 2 ^ L) (hd : d + 2 * N + L + 7 ≤ lim.depth) :
    Meets lim (LightTernaryBankAssembly.program ++ tail) pMain d
      [N, a, n, powers, L, keyBase, fsource, gsource, fbase, gbase, hbase] μ (time N L n)
      (fun _ μ' =>
        Stages E (fun s => forwardStage s F) fbase N μ' ∧
          Stages E (fun s => forwardStage s G) gbase N μ' ∧
            Stages E (fun s => stageValue s (LightTernaryBankAssembly.product F G)) hbase N μ' ∧
              Preserved μ μ' keyBase n fbase gbase hbase N ∧ Powers μ' powers (2 * N)) :=
  by
  have hstep : (N + 1) * n = N * n + n := by ring
  have hfn : fbase + n ≤ gbase := by omega
  have hgn : gbase + n ≤ hbase := by omega
  have hhn : hbase + n ≤ lim.space := by omega
  apply Meets.of_body hmain
  unfold body time
  have hcf :=
    copy_meets (d := d + 1) (μ := μ) (src := fsource) (dst := fbase) (n := n) hcopy hw (by omega) (by omega)
      (Or.inl (by omega))
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
    | refine _root_.Light.Ends.callToThen (hcf _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcf ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, copyTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [copyTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, copyTime] <;> omega)
    on_goal -1 => (rintro rf μf ⟨houtF, hkeepF⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcg :=
    copy_meets (d := d + 1) (μ := μf) (src := gsource) (dst := gbase) (n := n) hcopy hw (by omega) (by omega)
      (Or.inl (by omega))
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
    | refine _root_.Light.Ends.callToThen (hcg _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcg ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, copyTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [copyTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, copyTime] <;> omega)
    on_goal -1 => (rintro rg μg ⟨houtG, hkeepG⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcodesG : ∀ j < n, μg (a + j) = (address (E.word j) : ℤ) :=
    by
    intro j hj
    exact (hkeepG _ (Or.inl (by omega))).trans ((hkeepF _ (Or.inl (by omega))).trans (hcodes j hj))
  have hpowG : Powers μg powers (2 * N) := by
    intro j hj
    exact (hkeepG _ (Or.inl (by omega))).trans ((hkeepF _ (Or.inl (by omega))).trans (hpowers j hj))
  have hsF : ∀ j < n, μg (fbase + j) = F (E.word j) := by
    intro j hj
    exact (hkeepG _ (Or.inl (by omega))).trans ((houtF j hj).trans (hsourceF j hj))
  have hsG : ∀ j < n, μg (gbase + j) = G (E.word j) := by
    intro j hj
    exact (houtG j hj).trans ((hkeepF _ (Or.inl (by omega))).trans (hsourceG j hj))
  have hc :=
    (LightTernaryBankAssembly.meets (d := d + 1) E F G μg hw ha hmeta hpows hfg hgh hspace hword hNword hcodesG hsF hsG
          hpowG hsorted hF hG hforwardWord hproductWord hinverseWord hL hn (by omega)).append
      tail
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
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryBankAssembly.time, copyTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryBankAssembly.time, copyTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryBankAssembly.time, copyTime] <;>
          omega)
    on_goal -1 => (rintro r μ' ⟨hF', hG', hH', hkeep, hpow⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hF', hG', hH', ?_, hpow⟩
  intro x hm hf hg hh
  have hf' : x < fbase + n ∨ fbase + (N + 1) * n ≤ x := by omega
  have hg' : x < gbase + n ∨ gbase + (N + 1) * n ≤ x := by omega
  have hfc : x < fbase ∨ fbase + n ≤ x := by omega
  have hgc : x < gbase ∨ gbase + n ≤ x := by omega
  exact (hkeep x hm hf' hg' hh).trans ((hkeepG x hgc).trans (hkeepF x hfc))
end ThreeSum.LightTernaryGroupBankStep
