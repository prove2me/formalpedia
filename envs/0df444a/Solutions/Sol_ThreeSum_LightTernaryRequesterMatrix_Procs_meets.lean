-- Prove2me | solution 1 for ThreeSum.LightTernaryRequesterMatrix.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:57.946048+00:00
-- url     : https://prove2.me/submissions/a7ee536d-2432-49dc-ab27-0dcaf2460769

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_Procs_inner_meets
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
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
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightTernaryRequesterMatrix
namespace Procs
theorem _root_.solution {main : ℕ} (S : Procs P main) {src n U J radix carry Q positions matrix work : ℕ} (μ : ℕ → ℤ)
    (f : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 5 < lim.depth) (hb : 1 < radix) (hQ : 0 < Q)
    (hsrc : src + n ≤ positions) (hcarry : carry + Q * (J + 1) ≤ positions) (hpos : positions + n * Q ≤ matrix)
    (hmat : matrix + n * Q * (J + 2) ≤ work) (hspace : LightTernarySignedRow.space work (3 * U) ≤ lim.space)
    (hword : (LightTernarySignedRow.word (3 * U) radix J : ℤ) ≤ lim.word) (hread : ∀ a < n, μ (src + a) = f a)
    (hvalues : ∀ a < n, |f a| ≤ (U : ℤ)) (hCarries : LightTernaryCarryCodes.Table μ carry J Q) :
    Meets lim P main depth [src, n, U, J, radix, carry, Q, positions, matrix, work] μ (time n Q J U)
      (fun _ ν => Entries ν positions matrix J Q (n * Q) U radix f ∧ Kept μ ν positions) :=
  by
  have hwsp : work ≤ lim.space := by unfold LightTernarySignedRow.space LightOutputDecodeDigits.space at hspace; omega
  have hQle : Q ≤ Q * (J + 1) := Nat.le_mul_of_pos_right Q (by omega)
  have hn : n ≤ n * Q := Nat.le_mul_of_pos_right n hQ
  have hSmallWord := hword
  unfold LightTernarySignedRow.word LightOutputDecodeDigits.word at hSmallWord
  apply Meets.of_body S.mainBody
  unfold body time
  refine
    Ends.for (Inv μ f src n U J radix carry Q positions matrix work) n (innerTime Q J U + 180) ?start ?round ?done
      ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ, ?_, ?_, SameOn.refl⟩
    · simp only [update_frame_setLocal]
      exact congrArg (fun loc => (⟨loc, μ⟩ : State)) (frame_append_zeros _ 1).symm
    · intro r hr; simp at hr
  case round =>
    rintro i _ hi _ ⟨result, ν, rfl, H, K⟩
    have hread' : ∀ a < n, ν (src + a) = f a := by intro a ha; rw [K _ (by omega), hread a ha]
    have hCarries' : LightTernaryCarryCodes.Table ν carry J Q :=
      by
      intro q hq
      rcases hCarries q hq with ⟨h0, hbits⟩
      have hEnd : carry + q * (J + 1) + J + 1 ≤ positions :=
        by
        have hh := Nat.mul_le_mul_right (J + 1) (show q + 1 ≤ Q by omega)
        rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
      refine ⟨?_, ?_⟩
      · rw [K _ (by omega)]; exact h0
      · intro j hj
        rw [K _ (by omega)]; exact hbits j hj
    have hcall :=
      S.inner_meets (depth := depth + 1) (n := n) ν f hw (by omega) hb hQ hi hsrc hcarry hpos hmat hspace hword hread'
        hvalues hCarries' H
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
          (simp [] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      on_goal -1 => (rintro ret ξ ⟨hEntries, hKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    exact ⟨by simp, ret, ξ, by simp [update_frame_setLocal], hEntries, fun x hx => (hKeep x hx).trans (K x hx)⟩
  case done => rintro _ _ ⟨r, ν, rfl, H, K⟩; exact ⟨H, K⟩
  case bound =>
    rintro i _ hi _ ⟨r, ν, rfl, H, K⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end Procs
end ThreeSum.LightTernaryRequesterMatrix
