-- Prove2me | solution 1 for ThreeSum.LightRadixRows.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:05.915642+00:00
-- url     : https://prove2.me/submissions/9b83faba-b64e-46d4-9cdd-f9d88390ba3d

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_04c57512725a2a98
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_RadixKeyLists_step_length
import Theorems.Thm_ThreeSum_RadixKeyLists_step_take_succ
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixRows
open Light RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightRadixRows
theorem _root_.solution {pMain pAffine srcBase srcPrev dst p U V : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pAffine)) (haffine : P[pAffine]? = some LightReportingAffine.body)
    (base prev : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hbaseEnd : srcBase + base.length ≤ dst)
    (hprevEnd : srcPrev + prev.length ≤ dst) (hspace : dst + base.length * prev.length ≤ lim.space)
    (hword : (word p U V : ℤ) ≤ lim.word) (hd : d < lim.depth) (hbaseRead : Seg μ srcBase base)
    (hprevRead : Seg μ srcPrev prev) (hbaseBound : ∀ x ∈ base, |x| ≤ (U : ℤ)) (hprevBound : ∀ y ∈ prev, |y| ≤ (V : ℤ)) :
    Meets lim P pMain d [srcBase, srcPrev, dst, base.length, prev.length, p] μ (time base.length prev.length)
      (fun _ ν => Seg ν dst (step (p : ℤ) base prev) ∧ SameOutside μ ν dst (base.length * prev.length)) :=
  by
  have hbudget (n : ℕ) (hn : n ≤ word p U V) : (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hn).trans hword
  have hpWord := hbudget p (by unfold word; omega)
  have hsumWord := hbudget (U + p * V) (by unfold word; omega)
  have hmulWord := hbudget (p * V) (by unfold word; omega)
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ srcBase srcPrev dst p base prev) base.length (LightReportingAffine.time prev.length + 75) ?start
      ?round ?done ?bound (hT := by
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
    refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · simp [update_frame_setLocal]
      change
        frame [(srcBase : ℤ), srcPrev, dst, base.length, prev.length, p, 0] =
          frame ([(srcBase : ℤ), srcPrev, dst, base.length, prev.length, p, 0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · simp [step]
  case round =>
    rintro j _ hj _ ⟨r, ν, rfl, hout, hkeep⟩
    have hend : j * prev.length + prev.length ≤ base.length * prev.length := by
      calc
        j * prev.length + prev.length = (j + 1) * prev.length := by ring
        _ ≤ base.length * prev.length := Nat.mul_le_mul_right prev.length (by omega)
    have hjProd : (j : ℤ) * (prev.length : ℤ) ≤ lim.word :=
      by
      have hh : j * prev.length ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ) * (prev.length : ℤ) ≤ lim.space).trans hw
    have hrowAddr : (dst : ℤ) + (j : ℤ) * (prev.length : ℤ) ≤ lim.word :=
      by
      have hh : dst + j * prev.length ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (dst : ℤ) + (j : ℤ) * (prev.length : ℤ) ≤ lim.space).trans hw
    have hreadBase : ν (srcBase + j) = base[j] := (hkeep _ (Or.inl (by omega))).trans (hbaseRead j hj)
    have hreadPrev (i : ℕ) (hi : i < prev.length) : ν (srcPrev + i) = prev[i] :=
      (hkeep _ (Or.inl (by omega))).trans (hprevRead i hi)
    have hkey := hbaseBound _ (List.getElem_mem hj)
    have hmul : ∀ i < prev.length, |(p : ℤ) * ν (srcPrev + i)| ≤ lim.word :=
      by
      intro i hi
      rw [hreadPrev i hi, abs_mul, Int.abs_natCast]
      exact
        (mul_le_mul_of_nonneg_left (hprevBound _ (List.getElem_mem hi)) (Int.natCast_nonneg _)).trans
          (by simpa only [Nat.cast_mul] using hmulWord)
    have hsum : ∀ i < prev.length, |base[j] + (p : ℤ) * ν (srcPrev + i)| ≤ lim.word :=
      by
      intro i hi
      have hv : |(p : ℤ) * ν (srcPrev + i)| ≤ (p : ℤ) * V :=
        by
        rw [hreadPrev i hi, abs_mul, Int.abs_natCast]
        exact mul_le_mul_of_nonneg_left (hprevBound _ (List.getElem_mem hi)) (Int.natCast_nonneg _)
      exact
        (abs_add_le _ _).trans ((add_le_add hkey hv).trans (by simpa only [Nat.cast_add, Nat.cast_mul] using hsumWord))
    have hc :=
      LightReportingAffine.meets (d := d + 1) (src := srcPrev) (dst := dst + j * prev.length) (n := prev.length) (b :=
        base[j]) (c := (p : ℤ)) haffine hw (by omega) (by omega) (Or.inr (Or.inl (by omega))) hmul hsum
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadBase,
              LightReportingAffine.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadBase, LightReportingAffine.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadBase, LightReportingAffine.time] <;>
            omega)
      on_goal -1 => (rintro result ν₁ ⟨hrow, hrowKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, result, ν₁, by simp [update_frame_setLocal], ?_, ?_⟩
    · rw [step_take_succ _ _ _ hj]
      have hlen : (step (p : ℤ) (base.take j) prev).length = j * prev.length := by
        rw [step_length, List.length_take, min_eq_left (Nat.le_of_lt hj)]
      apply seg_append.mpr
      constructor
      · exact hout.of_sameOutside hrowKeep (Or.inl (by rw [hlen]))
      · rw [hlen]
        intro i hi
        have hi' : i < prev.length := by simpa only [List.length_map] using hi
        rw [List.getElem_map, hrow i hi', hreadPrev i hi']
    · intro a ha
      exact (hrowKeep a (by omega)).trans (hkeep a ha)
  case done =>
    rintro _ _ ⟨r, ν, rfl, hout, hkeep⟩
    exact ⟨by simpa only [List.take_length] using hout, hkeep⟩
  case bound =>
    rintro j _ hj _ ⟨r, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightRadixRows
