-- Prove2me | solution 1 for ThreeSum.LightSpanCatalogTest.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:06:11.637801+00:00
-- url     : https://prove2.me/submissions/e776fc2c-39c3-4af2-bd7b-b74811e9f142

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Theorems.Thm_ThreeSum_LightSpanRowEqual_flag_le_one
import Theorems.Thm_ThreeSum_LightSpanRowEqual_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogTest_present_succ
import Theorems.Thm_ThreeSum_LightSpanCatalogTest_flag_le_one
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogBlock_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogStep_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightSpanCatalogTest
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSpanCatalogTest
theorem _root_.solution {pMain pEq catalog n J candidate d : ℕ} (hmain : P[pMain]? = some (body pEq))
    (heq : P[pEq]? = some LightSpanRowEqual.body) (μ : ℕ → ℤ) (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcat : catalog + J * n ≤ lim.space) (hrow : candidate + J ≤ lim.space)
    (hone : (1 : ℤ) ≤ lim.word) (hcontrols : ((n + J + 16 : ℕ) : ℤ) ≤ lim.word)
    (hf : ∀ k < n, ∀ i < J, |f k i| ≤ lim.word) (hr : ∀ i < J, |row i| ≤ lim.word)
    (hread : ∀ k < n, ∀ i < J, μ (catalog + J * k + i) = f k i) (hreadRow : ∀ i < J, μ (candidate + i) = row i)
    (hd : d + 1 ≤ lim.depth) :
    Meets lim P pMain d [catalog, n, J, candidate] μ (time J n) (fun r ν => r = (flag f row J n : ℤ) ∧ ν = μ) :=
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
    refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSpanRowEqual.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSpanRowEqual.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSpanRowEqual.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := n * (LightSpanRowEqual.time J + 150) + 20) (Q := Inv μ catalog n J candidate f row n)
        (Inv μ catalog n J candidate f row) n (LightSpanRowEqual.time J + 100) ?start ?round ?done ?bound (hT := by
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
      ?after (hT := by
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
  case start =>
    refine ⟨0, ?_⟩
    simp [update_frame_setLocal, flag, Present]
    change frame [(catalog : ℤ), n, J, candidate, 1, 0] = frame ([(catalog : ℤ), n, J, candidate, 1, 0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro k _ hk _ ⟨result, rfl⟩
    have hkn : J * k + J ≤ J * n :=
      by
      have hh := Nat.mul_le_mul_left J (show k + 1 ≤ n by omega)
      simpa only [Nat.mul_add, Nat.mul_one] using hh
    have hread' : ∀ i < J, μ (catalog + J * k + i) = f k i := hread k hk
    have hc :=
      LightSpanRowEqual.meets (d := d + 1) (a := catalog + J * k) heq μ (f k) row hw (by omega) hrow hone (hf k hk) hr
        hread' hreadRow
    have hFlag := flag_le_one f row J k
    unfold roundBody
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSpanRowEqual.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSpanRowEqual.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSpanRowEqual.time] <;> omega)
      on_goal -1 => (rintro out ν ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν
    have hEqFlag := LightSpanRowEqual.flag_le_one (f k) row J
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen (LightSpanRowEqual.flag (f k) row J = 1) (fun he => ?_) (fun hne => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout,
              LightSpanRowEqual.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hout, LightSpanRowEqual.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, LightSpanRowEqual.time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hcurrent : ∀ i < J, f k i = row i := by
        by_contra hh
        simp [LightSpanRowEqual.flag, hh] at he
      have hNext : flag f row J (k + 1) = 0 := by
        unfold flag
        rw [if_pos ((present_succ f row J k).mpr (Or.inr hcurrent))]
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightSpanRowEqual.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightSpanRowEqual.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSpanRowEqual.time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, out, ?_⟩
      simp [update_frame_setLocal, hNext]
    · have hcurrent : ¬∀ i < J, f k i = row i := by
        intro hh
        apply hne
        unfold LightSpanRowEqual.flag
        rw [if_pos hh]
      have hNext : flag f row J (k + 1) = flag f row J k :=
        by
        have hp : Present f row J (k + 1) ↔ Present f row J k :=
          by
          constructor
          · intro h
            rcases (present_succ f row J k).mp h with h | h
            · exact h
            · exact False.elim (hcurrent h)
          · intro h
            exact (present_succ f row J k).mpr (Or.inl h)
        unfold flag
        rw [hp]
      refine Ends.skip ⟨by simp, out, ?_⟩
      simp [update_frame_setLocal, hNext]
  case done => intro σ _ h; exact h
  case bound =>
    rintro k _ hk _ ⟨result, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨result, rfl⟩
    have hFlag := flag_le_one f row J n
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (flag f row J n : ℕ) ?_ ?_ ?_
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
    exact ⟨by simp, rfl⟩
end ThreeSum.LightSpanCatalogTest
