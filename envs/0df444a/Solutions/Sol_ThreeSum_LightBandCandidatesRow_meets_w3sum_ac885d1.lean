-- Prove2me | solution 1 for ThreeSum.LightBandCandidatesRow.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:28.99465+00:00
-- url     : https://prove2.me/submissions/a266331e-3278-4208-80ec-f65f1efe589d

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesCell
import Definitions.Def_Submission_ThreeSum_LightBandCandidatesRow
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidatesRow
open Light BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src dst n outer U : ℕ} {f : ℕ → ℕ}
namespace ThreeSum.LightBandCandidatesRow
theorem _root_.solution {pMain pCell : ℕ} (mode : Mode) (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightBandCandidatesCell.body mode)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d < lim.depth) (hsrc : src + n ≤ dst) (hspace : dst + 4 * n ≤ lim.space)
    (hword : ((U + 10 : ℕ) : ℤ) ≤ lim.word) (hn : n ≤ U) (houter : outer ≤ U) (hf : ∀ j < n, f j ≤ U)
    (hread : ∀ j < n, μ (src + j) = (f j : ℤ)) :
    Meets lim P pMain d [src, dst, n, outer] μ (time n)
      (fun _ ν => (∀ j < n, Seg ν (dst + 4 * j) (make mode outer j (f j)).cells) ∧ SameOutside μ ν dst (4 * n)) :=
  by
  have hnWord : (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : n ≤ U + 10)).trans hword
  have hoWord : (outer : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : outer ≤ U + 10)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ mode f src dst n outer) n (LightBandCandidatesCell.time + 92) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, 0, μ, ?_, ?_, SameOutside.refl⟩
    · simp [update_frame_setLocal]
      exact (frame_append_zeros [src, dst, n, outer, 0] 2).symm
    · intro k hk; omega
  case round =>
    rintro j _ hj _ ⟨x, r, ν, rfl, written, kept⟩
    have hjWord : (j : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : j ≤ U + 10)).trans hword
    have hfWord : (f j : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by have := hf j hj; omega : f j ≤ U + 10)).trans hword
    have hread' : ν (src + j) = (f j : ℤ) := by
      rw [kept _ (Or.inl (by omega))]
      exact hread j hj
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (f j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread']
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hread'] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread'] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hc :=
      LightBandCandidatesCell.meets (d := d + 1) (μ := ν) (r := f j) (i := outer) (j := j) (dst := dst + 4 * j) mode
        hcell hw (by omega) hword (hf j hj) houter (by omega)
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
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightBandCandidatesCell.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightBandCandidatesCell.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandCandidatesCell.time] <;> omega)
      on_goal -1 => (rintro value ν₁ ⟨hrow, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, f j, value, ν₁, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (written k hk).of_sameOutside hkeep (Or.inl (by simp [Record.cells]; omega))
      · exact hrow
    · intro a ha
      rw [hkeep a (by unfold Outside at *; omega), kept a ha]
  case done =>
    rintro _ _ ⟨x, r, ν, rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro j _ _ _ ⟨x, r, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightBandCandidatesRow
