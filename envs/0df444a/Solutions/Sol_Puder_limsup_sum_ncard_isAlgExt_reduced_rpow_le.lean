-- Prove2me | solution 1 for Puder.limsup_sum_ncard_isAlgExt_reduced_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:39:51.35281+00:00
-- url     : https://prove2.me/submissions/30373802-952c-4ed9-83f1-e5d52273b9eb

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore
import Theorems.Thm_Puder_tracesEachCoreEdgeTwice_of_isAlgExt
import Theorems.Thm_Puder_finite_and_limsup_sum_ncard_tracesEachCoreEdgeTwice_reduced_rpow_le

open Filter

namespace Puder.Q263Cnt

/-- A subgroup with a finite basis is finitely generated. -/
theorem fg_of_hasRank {d m : ℕ} {J : Subgroup (FreeGroup (Fin d))} (h : HasRank J m) : J.FG := by
  obtain ⟨b⟩ := h
  have : Group.FG J :=
    Group.fg_of_surjective (f := (b.repr.symm : FreeGroup (Fin m) →* J)) b.repr.symm.surjective
  exact (Group.fg_iff_subgroup_fg J).mp inferInstance

/-- Puder (4.1): proper rank-`m` algebraic extensions of `⟨w⟩` trace each core edge twice. -/
theorem subset {d m : ℕ} (w : FreeGroup (Fin d)) :
    {J : Subgroup (FreeGroup (Fin d)) | HasRank J m ∧
      IsAlgExt (Subgroup.zpowers w) J ∧ Subgroup.zpowers w ≠ J} ⊆
    {J : Subgroup (FreeGroup (Fin d)) | HasRank J m ∧ w ∈ J ∧ TracesEachCoreEdgeTwice J w} := by
  rintro J ⟨hr, halg, hne⟩
  exact ⟨hr, halg.1 (Subgroup.mem_zpowers w),
    tracesEachCoreEdgeTwice_of_isAlgExt w J (fg_of_hasRank hr) halg hne⟩

end Puder.Q263Cnt

namespace Puder

theorem limsup_sum_ncard_isAlgExt_reduced_rpow_le_dev (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              IsAlgExt (Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j)))) J ∧
              Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≠ J}.ncard : ℝ)) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              IsAlgExt (Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j)))) J ∧
              Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≠ J}.ncard : ℝ)) ^
          (1 / (t : ℝ))) atTop ≤
        if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1 := by
  obtain ⟨hfin, hb, hl⟩ :=
    finite_and_limsup_sum_ncard_tracesEachCoreEdgeTwice_reduced_rpow_le k m hk hm1 hm
  have ha0 : ∀ t : ℕ, 0 ≤ (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              IsAlgExt (Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j)))) J ∧
              Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≠ J}.ncard : ℝ)) ^
          (1 / (t : ℝ)) := fun t =>
    Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) _
  have hab : ∀ t : ℕ, (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              IsAlgExt (Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j)))) J ∧
              Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≠ J}.ncard : ℝ)) ^
          (1 / (t : ℝ)) ≤
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
              TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard
              : ℝ)) ^ (1 / (t : ℝ)) := by
    intro t
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast Set.ncard_le_ncard (Q263Cnt.subset _) (hfin _)
  have hba := hb
  obtain ⟨c, hc⟩ := hba
  refine ⟨⟨c, (eventually_map.mp hc).mono fun t ht => (hab t).trans ht⟩, le_trans ?_ hl⟩
  exact Filter.limsup_le_limsup (Eventually.of_forall hab)
    (isCoboundedUnder_le_of_le atTop ha0) hb

end Puder

theorem solution : type_of% @Puder.limsup_sum_ncard_isAlgExt_reduced_rpow_le_dev := @Puder.limsup_sum_ncard_isAlgExt_reduced_rpow_le_dev
