-- Prove2me | solution 1 for ThreeSum.LightSignedCoefficientLayout.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:21.971163+00:00
-- url     : https://prove2.me/submissions/dafdb4bb-8a5f-4943-bf3d-671bc50356c1

import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientLayout
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_involutive
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedCoefficientLayout
open Light TernarySignedLayout
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightSignedCoefficientLayout
theorem _root_.solution {proc src dst J U : ℕ} (hp : P[proc]? = some body) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + (J + 2) ≤ dst) (hspace : dst + (J + 2) ≤ lim.space)
    (hread : ∀ i < J + 2, μ (src + i) = f i) (hf : ∀ i < J + 2, |f i| ≤ (U : ℤ)) (hword : (U : ℤ) ≤ lim.word) :
    Meets lim P proc depth [src, dst, J] μ (time J)
      (fun _ ν => (∀ i < J + 2, ν (dst + i) = f (offset J i)) ∧ SameOutside μ ν dst (J + 2)) :=
  by
  apply Meets.of_body hp
  unfold body time
  refine
    Ends.for
      (fun i σ =>
        σ.loc = frame [src, dst, J, i] ∧ (∀ j < i, σ.mem (dst + offset J j) = f j) ∧ SameOutside μ σ.mem dst (J + 2))
      (J + 2) 40 ?start ?round ?done ?bound
  case start => refine ⟨by simp [update_frame_setLocal], ?_, SameOutside.refl⟩; intro j hj; omega
  case round =>
    rintro i σ hi _ ⟨hloc, written, kept⟩
    cases σ with
    | mk loc ν =>
      dsimp only at hloc written kept ⊢
      subst loc
      have hr : ν (src + i) = f i := (kept _ (Or.inl (by omega))).trans (hread i hi)
      have hfit := (hf i hi).trans hword
      have ho := offset_lt hi
      have haddrWord : ((dst + offset J i : ℕ) : ℤ) ≤ lim.word :=
        (Int.ofNat_le.mpr (show dst + offset J i ≤ lim.space by omega)).trans hw
      have hnew : ∀ j < i, j ≠ i → offset J j ≠ offset J i :=
        by
        intro j hj hji heq
        have hh := congrArg (offset J) heq
        rw [offset_involutive (by omega), offset_involutive hi] at hh
        exact hji hh
      have finish :
        ∀ value : ℤ,
          value = f i →
            (Function.update (frame [src, dst, J, i]) 3 ((i : ℤ) + 1) = frame [src, dst, J, i + 1] ∧
              (∀ j < i + 1, Function.update ν (dst + offset J i) value (dst + offset J j) = f j) ∧
                SameOutside μ (Function.update ν (dst + offset J i) value) dst (J + 2)) :=
        by
        intro value hval
        refine ⟨by simp [update_frame_setLocal], ?_, kept.update ⟨by omega, by omega⟩ _⟩
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by have := hnew j hj (by omega); omega), written j hj]
        · simpa [hval]
      unfold roundBody
      refine
        Ends.iteLast ?_ ?_
          (by (
              (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
          (by
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [] <;> first
                  | omega
                  | (ring_nf; omega)))
      · intro hd
        have hd' : i < J := by exact_mod_cast (show (i : ℤ) < (J : ℤ) from hd)
        have heq : (dst : ℤ) + (J : ℤ) - 1 - (i : ℤ) = ((dst + offset J i : ℕ) : ℤ) := by
          simp only [offset, if_pos hd']; omega
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          refine _root_.Light.Ends.storeToThen (dst + offset J i) (f i) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, heq, hr]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [heq, hr] <;> first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, heq, hr] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp, by simpa using finish _ rfl⟩
      · intro hd
        have hd' : ¬i < J := by exact_mod_cast (show ¬(i : ℤ) < (J : ℤ) from hd)
        have heq : offset J i = i := by simp [offset, hd']
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          refine _root_.Light.Ends.storeToThen (dst + i) (f i) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hr] <;> first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp, by simpa only [heq, Nat.cast_add, Nat.cast_one] using finish (f i) rfl⟩
  case done =>
    rintro σ _ ⟨hloc, written, kept⟩
    refine ⟨?_, kept⟩
    intro i hi
    have hh := written (offset J i) (offset_lt hi)
    rwa [offset_involutive hi] at hh
  case bound =>
    rintro i σ hi _ ⟨hloc, _, _⟩
    cases σ with
    | mk loc ν =>
      dsimp only at hloc ⊢
      subst loc
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightSignedCoefficientLayout
