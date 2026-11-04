-- Prove2me | solution 1 for ThreeSum.LightSignedBoxSetup.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:35:10.722793+00:00
-- url     : https://prove2.me/submissions/b101c616-9549-4465-9a1f-fd0c66f39dc2

import Definitions.Def_Submission_ThreeSum_LightSignedLeafTable
import Definitions.Def_Submission_ThreeSum_LightSignedBoxSetup
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
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
import Theorems.Thm_ThreeSum_SignedLeaf_abs_value_le
set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedBoxSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedBoxSetup
theorem _root_.solution
    {pMain pLeafTable pBoxStages pEnumSetup pEnum pLeafBatch pLeafCell pLeaf pAddress pZetaPass pZetaBatch pZetaCell :
      ℕ}
    (hmain : P[pMain]? = some (body pLeafTable pBoxStages)) (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    (hTable : P[pLeafTable]? = some (LightSignedLeafTable.body pEnumSetup pLeafBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body C.pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hLeafBatch : P[pLeafBatch]? = some (LightSignedLeafBatch.body pLeafCell))
    (hLeafCell : P[pLeafCell]? = some (LightSignedLeafCell.body pLeaf pAddress))
    (hBoxStages : P[pBoxStages]? = some (LightBoxStages.body C.pSize pZetaPass))
    (hZetaPass : P[pZetaPass]? = some (LightZetaPass.body pEnumSetup pZetaBatch))
    (hZetaBatch : P[pZetaBatch]? = some (LightZetaBatch.body pZetaCell))
    (hZetaCell : P[pZetaCell]? = some (LightZetaCell.body C.pSetup C.pOffset C.pErase C.pRank)) {μ : ℕ → ℤ}
    {W sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ} (preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ W)
    (hstage : stage ≤ W) (hdataL : baseL + (W + 1) * downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR + (W + 1) * downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase + (W + 1) * downsetCap W boxCut ≤ maskBase) (hmasks : maskBase + downsetCap W boxCut ≤ work)
    (hspace : work + 1 + tableSize W + (W + 1) ≤ lim.space) (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2 ^ W * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card + boxCut ≤ sourceCut) (hpreR : preR.card + boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B) (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W) (hd : d + W + 10 ≤ lim.depth) :
    Meets lim P pMain d
      [W, sourceCut, boxCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, baseL, baseR, boxBase,
        maskBase, work]
      μ (time W boxCut)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (SignedLeaf.value f g stage preL preR) W ∧
          LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
            LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
              KeptBut μ μ' maskBase boxBase ((W + 1) * downsetCap W boxCut)) :=
  by
  have hcap : downsetCap W boxCut ≤ (W + 1) * downsetCap W boxCut := Nat.le_mul_of_pos_left _ (by omega)
  have hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ stage * B) * (2 ^ stage * D) ≤ 2 ^ W * ((2 ^ stage * B) * (2 ^ stage * D)) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    exact
      (by exact_mod_cast hh :
            (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤
              ((2 ^ W * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ)).trans
        hvalueWord
  have hleafBound :
    ∀ S, S.card ≤ boxCut → |SignedLeaf.value f g stage preL preR S| ≤ (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
    by
    intro S hS
    apply SignedLeaf.abs_value_le (cut := sourceCut) f g stage preL preR S hstage
    · exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hS _).trans hpreL)
    · exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hS _).trans hpreR)
    · exact hf
    · exact hg
  apply Meets.of_body hmain
  unfold body time
  have hl :=
    LightSignedLeafTable.meets (d := d + 1) (μ := μ) hTable C hEnumSetup hEnum hLeafBatch hLeafCell preL preR f g hw
      hcut hboxCut hstage (by omega) (by omega) (by omega) hmasks (Or.inl hdataL) (Or.inl hdataR) hspace hword
      hproductWord hpreL hpreR hf hg hstoredL hstoredR (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSignedLeafTable.time,
            LightBoxStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSignedLeafTable.time, LightBoxStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSignedLeafTable.time,
            LightBoxStages.time] <;> omega)
    on_goal -1 => (rintro leafRet μ₁ ⟨hleaves, hkeepLeaf⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hb :=
    LightBoxStages.meets (d := d + 1) (μ := μ₁) hBoxStages C.size hZetaPass hEnumSetup hEnum hZetaBatch hZetaCell
      C.setup C.offset C.erase (SignedLeaf.value f g stage preL preR) hw hboxCut hbox hmasks (by omega) hword hvalueWord
      hleaves hleafBound (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSignedLeafTable.time,
            LightBoxStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSignedLeafTable.time, LightBoxStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSignedLeafTable.time,
            LightBoxStages.time] <;> omega)
    on_goal -1 => (rintro boxRet μ₂ ⟨hboxes, hkeepBox⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkept : KeptBut μ μ₂ maskBase boxBase ((W + 1) * downsetCap W boxCut) :=
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
end ThreeSum.LightSignedBoxSetup
