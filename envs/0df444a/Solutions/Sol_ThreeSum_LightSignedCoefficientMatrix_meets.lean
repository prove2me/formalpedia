-- Prove2me | solution 1 for ThreeSum.LightSignedCoefficientMatrix.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:57.859355+00:00
-- url     : https://prove2.me/submissions/c8a4093e-4978-4004-b04c-ce0615898935

import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientLayout
import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientMatrix
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
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightSignedCoefficientLayout_meets
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
open ThreeSum ThreeSum.LightSignedCoefficientMatrix
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightSignedCoefficientMatrix
theorem _root_.solution {proc pRow src dst rows J U : ℕ} (hp : P[proc]? = some (body pRow))
    (hrow : P[pRow]? = some LightSignedCoefficientLayout.body) (μ : ℕ → ℤ) (f : ℕ → ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth < lim.depth) (hsrc : src + rows * (J + 2) ≤ dst)
    (hspace : dst + rows * (J + 2) ≤ lim.space) (hread : ∀ r < rows, ∀ i < J + 2, μ (src + r * (J + 2) + i) = f r i)
    (hf : ∀ r < rows, ∀ i < J + 2, |f r i| ≤ (U : ℤ)) (hword : (U : ℤ) ≤ lim.word) (hrowsWord : (rows : ℤ) ≤ lim.word)
    (hJWord : ((J + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [src, dst, rows, J] μ (time rows J)
      (fun _ ν =>
        (∀ r < rows, ∀ i < J + 2, ν (dst + r * (J + 2) + i) = f r (TernarySignedLayout.offset J i)) ∧
          SameOutside μ ν dst (rows * (J + 2))) :=
  by
  apply Meets.of_body hp
  unfold body time
  refine
    Ends.for
      (fun r σ =>
        ∃ Z ν,
          σ = ⟨frame [src, dst, rows, J, r, Z], ν⟩ ∧
            (∀ s < r, ∀ i < J + 2, ν (dst + s * (J + 2) + i) = f s (TernarySignedLayout.offset J i)) ∧
              SameOutside μ ν dst (rows * (J + 2)))
      rows (LightSignedCoefficientLayout.time J + 90) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro s hs; omega
  case round =>
    rintro r _ hr _ ⟨Z, ν, rfl, written, kept⟩
    have hend : r * (J + 2) + (J + 2) ≤ rows * (J + 2) :=
      by
      have hh := Nat.mul_le_mul_right (J + 2) (show r + 1 ≤ rows by omega)
      nlinarith
    have hoffWord : ((r * (J + 2) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show r * (J + 2) ≤ lim.space by omega)).trans hw
    have hsrcWord : ((src + r * (J + 2) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show src + r * (J + 2) ≤ lim.space by omega)).trans hw
    have hdstWord : ((dst + r * (J + 2) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show dst + r * (J + 2) ≤ lim.space by omega)).trans hw
    have hoffWordInt : (r : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by exact_mod_cast hoffWord
    have hoffNonnegInt : 0 ≤ (r : ℤ) * ((J : ℤ) + 2) := by positivity
    have hsrcWordInt : (src : ℤ) + (r : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by exact_mod_cast hsrcWord
    have hdstWordInt : (dst : ℤ) + (r : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by exact_mod_cast hdstWord
    have hreadν (i : ℕ) (hi : i < J + 2) : ν (src + r * (J + 2) + i) = f r i := by
      rw [kept _ (Or.inl (by omega)), hread r hr i hi]
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
      |
        refine
          _root_.Light.Ends.callToThen
            ((LightSignedCoefficientLayout.meets (depth := depth + 1) (src := src + r * (J + 2)) (dst :=
                dst + r * (J + 2)) (J := J) (U := U) hrow ν (f r) hw (by omega) (by omega) hreadν (hf r hr) hword)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightSignedCoefficientLayout.meets (depth := depth + 1) (src := src + r * (J + 2)) (dst :=
              dst + r * (J + 2)) (J := J) (U := U) hrow ν (f r) hw (by omega) (by omega) hreadν (hf r hr) hword)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSignedCoefficientLayout.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSignedCoefficientLayout.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSignedCoefficientLayout.time] <;> omega)
      on_goal -1 => (rintro R ξ ⟨values, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, R, ξ, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro s hs i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
      · have hoff : s * (J + 2) + i < r * (J + 2) :=
          by
          have hh := Nat.mul_le_mul_right (J + 2) (show s + 1 ≤ r by omega)
          nlinarith
        rw [hkeep _ (Or.inl (by omega)), written s hs i hi]
      · simpa [Nat.add_assoc] using values i hi
    · intro a ha
      rw [hkeep a (by omega), kept a ha]
  case done => rintro _ _ ⟨Z, ν, rfl, written, kept⟩; exact ⟨written, kept⟩
  case bound =>
    rintro r _ _ _ ⟨Z, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightSignedCoefficientMatrix
