-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixSetup.core_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:06:38.733022+00:00
-- url     : https://prove2.me/submissions/170ab0ae-2981-4b03-ba24-a2a7f8d84f0d

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_small_space
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_small_word
import Definitions.Def_WeightedCache3SUM_Alias_dc0a334da481a327
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_ReportingHostSuffix_leafWeight_abs_le
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_card
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}
namespace ThreeSum.LightReportingSuffixSetup
theorem _root_.solution {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (hfit : offset + V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V) (hstage : stage ≤ W)
    (hdataL : baseL + (W + 1) * downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR + (W + 1) * downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase + (V + 1) * downsetCap V boxCut ≤ maskBase) (hmasks : maskBase + downsetCap V boxCut ≤ work)
    (hspace : work + 1 + tableSize W + (W + 1) ≤ lim.space) (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card + boxCut ≤ sourceCut) (hpreR : preR.card + boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B) (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W) (hd : d + W + 10 ≤ lim.depth) :
    Meets lim program 28 d
      [W, sourceCut, boxCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, baseL, baseR,
        boxBase, maskBase, work]
      μ (coreTime W V boxCut)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (leafWeight hfit f g stage preL preR) V ∧
          LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
            LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
              KeptBut μ μ' maskBase boxBase ((V + 1) * downsetCap V boxCut)) :=
  by
  have hV : V ≤ W := by omega
  have hcap : downsetCap V boxCut ≤ (V + 1) * downsetCap V boxCut := Nat.le_mul_of_pos_left _ (by omega)
  have hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ stage * B) * (2 ^ stage * D) ≤ 2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D)) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    exact
      (by exact_mod_cast hh :
            (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤
              ((2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ)).trans
        hvalueWord
  have hleafBound :
    ∀ S, S.card ≤ boxCut → |leafWeight hfit f g stage preL preR S| ≤ (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
    by
    intro S hS
    apply leafWeight_abs_le (sourceCut := sourceCut) hfit f g preL preR S hstage
    · have he := Finset.card_union_le preL (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreL)
    · have he := Finset.card_union_le preR (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreR)
    · exact hf
    · exact hg
  apply Meets.of_body (p := 28) (by rfl : program[28]? = some (coreBody 27 2))
  unfold coreBody coreTime
  have hl :=
    LightReportingSuffixTable.meets (P := program) (pMain := 27) (pEnumSetup := 3) (pEnum := 20) (pBatch := 26)
      (pCell := 25) (d := d + 1) (μ := μ) rfl procs rfl rfl rfl rfl hfit preL preR f g hw hcut hboxCut hstage (by omega)
      (by omega) (by omega) hmasks (Or.inl hdataL) (Or.inl hdataR) hspace hword hproductWord hpreL hpreR hf hg hstoredL
      hstoredR (by omega)
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
    | refine _root_.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingSuffixTable.time,
            LightBoxStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingSuffixTable.time, LightBoxStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingSuffixTable.time,
            LightBoxStages.time] <;> omega)
    on_goal -1 => (rintro leafRet μ₁ ⟨hleaves, hkeepLeaf⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hb :=
    LightBoxStages.meets (P := program) (pMain := 2) (pSize := 9) (pPass := 21) (pEnumSetup := 3) (pEnum := 20)
      (pBatch := 22) (pCell := 23) (d := d + 1) (μ := μ₁) rfl procs.size rfl rfl rfl rfl rfl procs.setup procs.offset
      procs.erase (leafWeight hfit f g stage preL preR) hw hboxCut hbox hmasks
      (LightReportingSuffixCell.small_space hV hspace) (LightReportingSuffixCell.small_word hV hword) hvalueWord hleaves
      hleafBound (by omega)
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
    | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingSuffixTable.time,
            LightBoxStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingSuffixTable.time, LightBoxStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingSuffixTable.time,
            LightBoxStages.time] <;> omega)
    on_goal -1 => (rintro boxRet μ₂ ⟨hboxes, hkeepBox⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkept : KeptBut μ μ₂ maskBase boxBase ((V + 1) * downsetCap V boxCut) :=
    by
    intro i hi
    exact (hkeepBox i hi).trans (hkeepLeaf i ⟨hi.1, by omega⟩)
  refine ⟨hboxes, ?_, ?_, hkept⟩
  · apply LightSignedLeafBatch.storedThrough_of_on hstoredL
    intro i hi₀ hi₁
    exact hkept i ⟨by omega, Or.inl (by omega)⟩
  · apply LightSignedLeafBatch.storedThrough_of_on hstoredR
    intro i hi₀ hi₁
    exact hkept i ⟨by omega, Or.inl (by omega)⟩
end ThreeSum.LightReportingSuffixSetup
