-- Prove2me | solution 1 for ThreeSum.LightTernaryRequesterMatrix.Procs.inner_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:24.076256+00:00
-- url     : https://prove2.me/submissions/c9a45492-ece0-4ac0-b2db-b4d06198f13b

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_carry_read
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
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
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryCarryApply_meets
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalRequester_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_row_keep
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
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
theorem _root_.solution {main : ℕ} (S : Procs P main) {src n U J radix carry Q positions matrix work i : ℕ} (μ : ℕ → ℤ)
    (f : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 4 < lim.depth) (hb : 1 < radix) (hQ : 0 < Q)
    (hi : i < n) (hsrc : src + n ≤ positions) (hcarry : carry + Q * (J + 1) ≤ positions)
    (hpos : positions + n * Q ≤ matrix) (hmat : matrix + n * Q * (J + 2) ≤ work)
    (hspace : LightTernarySignedRow.space work (3 * U) ≤ lim.space)
    (hword : (LightTernarySignedRow.word (3 * U) radix J : ℤ) ≤ lim.word) (hread : ∀ a < n, μ (src + a) = f a)
    (hvalues : ∀ a < n, |f a| ≤ (U : ℤ)) (hCarries : LightTernaryCarryCodes.Table μ carry J Q)
    (hOld : Entries μ positions matrix J Q (i * Q) U radix f) :
    Meets lim P S.inner depth [src, U, J, radix, carry, Q, positions, matrix, work, i] μ (innerTime Q J U)
      (fun _ ν => Entries ν positions matrix J Q ((i + 1) * Q) U radix f ∧ Kept μ ν positions) :=
  by
  have hwsp : work ≤ lim.space := by unfold LightTernarySignedRow.space LightOutputDecodeDigits.space at hspace; omega
  have hJWord : ((J + 2 : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : J + 2 ≤ LightTernarySignedRow.word (3 * U) radix J := by
      unfold LightTernarySignedRow.word LightOutputDecodeDigits.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hQle : Q ≤ Q * (J + 1) := Nat.le_mul_of_pos_right Q (by omega)
  have hQword : (Q : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (show Q ≤ lim.space by omega)).trans hw
  have hSmallWord := hword
  unfold LightTernarySignedRow.word LightOutputDecodeDigits.word at hSmallWord
  have hn : n ≤ n * Q := Nat.le_mul_of_pos_right n hQ
  have hiQ : (i + 1) * Q ≤ n * Q := Nat.mul_le_mul_right Q (by omega)
  have hiWord : (i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (show i ≤ lim.space by omega)).trans hw
  have hval := hvalues i hi
  have hvalBounds := abs_le.mp hval
  apply Meets.of_body S.innerBody
  unfold LightTernaryRequesterMatrix.innerBody innerTime
  refine
    Ends.for (InnerInv μ f src U J radix carry Q positions matrix work i) Q
      (LightTernaryOriginalRequester.time J U + 280) ?start ?round ?done ?bound (hT := by
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
    · simpa using hOld
  case round =>
    rintro j _ hj _ ⟨result, ν, rfl, hEntries, hKeep⟩
    let r := i * Q + j
    have hr : r < n * Q := by dsimp [r]; nlinarith
    have hdiv : r / Q = i := by
      dsimp only [r]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : r % Q = j := by simp [r, Nat.add_mod, Nat.mod_eq_of_lt hj]
    have hrowEnd : matrix + r * (J + 2) + J + 2 ≤ work :=
      by
      have hh := Nat.mul_le_mul_right (J + 2) (show r + 1 ≤ n * Q by omega)
      rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
    have hrOffset : (i : ℤ) * Q + j ≤ lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show i * Q + j ≤ lim.space by dsimp [r] at hr; omega)).trans hw)
    have hiQWord : (i : ℤ) * Q ≤ lim.word := by omega
    have hposWord : (positions : ℤ) + (i : ℤ) * Q + j ≤ lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show positions + i * Q + j ≤ lim.space by dsimp [r] at hr; omega)).trans hw)
    unfold round
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.storeToThen (positions + r) (i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, r]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [r] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, r] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    let ξ := Function.update ν (positions + r) (i : ℤ)
    have hOldRows : Entries ξ positions matrix J Q r U radix f :=
      by
      intro s hs
      rcases hEntries s (by dsimp [r] at hs; exact hs) with ⟨hrow, hp⟩
      refine ⟨?_, ?_⟩
      · rcases hrow with ⟨hv, h0, h1⟩
        refine ⟨?_, ?_, ?_⟩
        · intro k
          dsimp [ξ]
          rw [Function.update_of_ne (by have := k.isLt; omega)]
          exact hv k
        · dsimp [ξ]; rw [Function.update_of_ne (by omega)]; exact h0
        · dsimp [ξ]; rw [Function.update_of_ne (by omega)]; exact h1
      · dsimp [ξ]; rw [Function.update_of_ne (by omega)]; exact hp
    have hcell : ξ (src + i) = f i := by
      dsimp [ξ]
      rw [Function.update_of_ne (by omega), hKeep _ (by omega), hread i hi]
    have hcRead : ∀ k ≤ J, ξ (carry + j * (J + 1) + k) = carryAt (TernaryCarryCode.carryFromCode J j) (J - k) :=
      by
      intro k hk
      have hcB : carry + j * (J + 1) + k < positions :=
        by
        have hh := Nat.mul_le_mul_right (J + 1) (show j + 1 ≤ Q by omega)
        rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
      dsimp [ξ]
      rw [Function.update_of_ne (by omega), hKeep _ hcB]
      exact carry_read hCarries hj k hk
    have hrowMul : (i : ℤ) * Q + j ≥ 0 := by positivity
    have hrowAddr : (matrix : ℤ) + ((i : ℤ) * Q + j) * ((J : ℤ) + 2) ≤ lim.word := by
      exact_mod_cast
        ((Int.ofNat_le.mpr (show matrix + (i * Q + j) * (J + 2) ≤ lim.space by dsimp [r] at hrowEnd; omega)).trans hw)
    have hrowProd : ((i : ℤ) * Q + j) * ((J : ℤ) + 2) ≤ lim.word := by omega
    have hcEnd : carry + j * (J + 1) + J + 1 ≤ matrix + r * (J + 2) :=
      by
      have hh := Nat.mul_le_mul_right (J + 1) (show j + 1 ≤ Q by omega)
      rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
    have hcAddr : (carry : ℤ) + (j : ℤ) * ((J : ℤ) + 1) ≤ lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show carry + j * (J + 1) ≤ lim.space by omega)).trans hw)
    have hcProd : (j : ℤ) * ((J : ℤ) + 1) ≤ lim.word := by omega
    have hrowProdNonneg : 0 ≤ ((i : ℤ) * Q + j) * ((J : ℤ) + 2) := by positivity
    have hcProdNonneg : 0 ≤ (j : ℤ) * ((J : ℤ) + 1) := by positivity
    have hcall :=
      S.requesterProcs.meets (d := depth + 1) (μ := ξ) (U := U) (radix := radix) (J := J) (dst := matrix + r * (J + 2))
        (carry := carry + j * (J + 1)) (work := work) (f i) (TernaryCarryCode.carryFromCode J j) hw (by omega) hb hval
        hcEnd hrowEnd hspace hword hcRead
    have hcell' := hcell
    dsimp only [ξ, r] at hcell'
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, r, hcell']
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [r, hcell'] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, r, hcell'] <;> omega)
      on_goal -1 => (rintro ret η ⟨hNew, hPres⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, ret, η, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro s hs
      change s < r + 1 at hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
      · rcases hOldRows s hs with ⟨hrow, hp⟩
        refine ⟨LightTernarySignedMatrix.row_keep hrow hPres ?_, ?_⟩
        · have hh := Nat.mul_le_mul_right (J + 2) (show s + 1 ≤ r by omega)
          rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
        · exact (hPres _ (by omega)).trans hp
      · refine ⟨?_, ?_⟩
        · simpa only [hdiv, hmod] using hNew
        · rw [hPres _ (by omega)]
          simp [ξ, hdiv]
    · intro x hx
      rw [hPres x (by omega)]
      change ξ x = μ x
      dsimp [ξ]
      rw [Function.update_of_ne (by omega), hKeep x hx]
  case done =>
    rintro _ _ ⟨r, ν, rfl, H, K⟩
    exact ⟨by simpa only [Nat.add_mul, one_mul] using H, K⟩
  case bound =>
    rintro j _ hj _ ⟨r, ν, rfl, H, K⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end Procs
end ThreeSum.LightTernaryRequesterMatrix
