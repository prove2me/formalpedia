-- Prove2me | solution 1 for ThreeSum.LightTernarySignedMatrix.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:20.263025+00:00
-- url     : https://prove2.me/submissions/756ba528-2686-4564-8ebb-37fdac2a5a0a

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_row_keep
import Theorems.Thm_Light_Limits_Addr_abs_le
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
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_left_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_right_meets
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
open ThreeSum ThreeSum.LightTernarySignedMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernarySignedMatrix
namespace Procs
theorem _root_.solution {pMain : ℕ} {right : Bool} (C : Procs P pMain right) {μ : ℕ → ℤ} {src n U J radix dst work : ℕ}
    (f : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 3 < lim.depth) (hb : 1 ≤ radix) (hsrc : src + n ≤ dst)
    (hsep : dst + n * (J + 2) ≤ work) (hspace : space work U ≤ lim.space) (hword : (word U radix J : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src + i) = f i) (hvalues : ∀ i < n, |f i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, n, U, J, radix, dst, work] μ (time n J U)
      (fun _ ν => Rows ν dst n J (fun i => raw right U radix J (f i)) ∧ Kept μ ν dst) :=
  by
  have hwork : work ≤ lim.space :=
    by
    unfold space LightTernarySignedRow.space LightOutputDecodeDigits.space at hspace
    omega
  have hUWord : (2 * U : ℕ) ≤ word U radix J :=
    by
    unfold word LightTernarySignedRow.word LightOutputDecodeDigits.word
    omega
  have hU : ((2 * U : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hUWord).trans hword
  have hJWord : J + 2 ≤ word U radix J :=
    by
    unfold word LightTernarySignedRow.word LightOutputDecodeDigits.word
    omega
  have hJ : ((J + 2 : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hJWord).trans hword
  apply Meets.of_body C.main
  unfold body time
  refine
    Ends.for (Inv right μ f src n U J radix dst work) n (LightTernarySignedRow.time J (3 * U) + 190) ?start ?round ?done
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
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi
      omega
  case round =>
    rintro i _ hi _ ⟨r, ν, rfl, written, kept⟩
    have hstep : (i + 1) * (J + 2) ≤ n * (J + 2) := Nat.mul_le_mul_right (J + 2) (by omega)
    have hrowEnd : dst + i * (J + 2) + J + 2 ≤ work :=
      by
      rw [Nat.add_mul] at hstep
      simp only [Nat.one_mul] at hstep
      omega
    have hcell : ν (src + i) = f i := (kept _ (by omega)).trans (hread i hi)
    have hval := hvalues i hi
    have hval' := abs_le.mp hval
    have haddrMul : i * (J + 2) ≤ lim.space := by omega
    have haddrMul' : (i : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by
      exact (by exact_mod_cast haddrMul : (i : ℤ) * ((J : ℤ) + 2) ≤ lim.space).trans hw
    have haddrMulNonneg : (0 : ℤ) ≤ (i : ℤ) * ((J : ℤ) + 2) := by positivity
    have hrowAddr : (dst : ℤ) + (i : ℤ) * ((J : ℤ) + 2) ≤ lim.word :=
      by
      have hh : dst + i * (J + 2) ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (dst : ℤ) + (i : ℤ) * ((J : ℤ) + 2) ≤ lim.space).trans hw
    have haddrEq : ((dst + i * (J + 2) : ℕ) : ℤ) = (dst : ℤ) + (i : ℤ) * ((J : ℤ) + 2) := by push_cast; rfl
    have hcall :
      Meets lim P C.pRow (d + 1)
        [f i, (if right then 2 * U else U), (if right then 1 else -1), J, radix, dst + i * (J + 2), work,
          (if right then 0 else 1), (if right then 1 else 0)]
        ν (LightTernarySignedRow.time J (3 * U))
        (fun _ ν' =>
          LightTernarySignedRow.Row ν' (dst + i * (J + 2)) J (raw right U radix J (f i)) ∧
            Kept ν ν' (dst + i * (J + 2))) :=
      by
      cases right
      · exact C.row.left_meets hw (by omega) hb hval hrowEnd hspace hword
      · exact C.row.right_meets hw (by omega) hb hval hrowEnd hspace hword
    cases right <;> focus
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
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcell, haddrEq,
                raw, LightTernarySignedRow.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hcell, haddrEq, raw, LightTernarySignedRow.time] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcell, haddrEq, raw,
                LightTernarySignedRow.time] <;> omega)
        on_goal -1 => (rintro s ν' ⟨stored, kept'⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    all_goals
      refine ⟨by simp, s, ν', by simp [update_frame_setLocal], ?_, ?_⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · apply row_keep (written j hj) kept'
          have hbefore : (j + 1) * (J + 2) ≤ i * (J + 2) := Nat.mul_le_mul_right (J + 2) (by omega)
          rw [Nat.add_mul] at hbefore
          simp only [Nat.one_mul] at hbefore
          omega
        · exact stored
      · intro a ha
        exact (kept' a (by omega)).trans (kept a ha)
  case done =>
    rintro _ _ ⟨r, ν, rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨r, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end Procs
end ThreeSum.LightTernarySignedMatrix
