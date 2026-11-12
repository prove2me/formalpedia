-- Prove2me | solution 2 for Puder.limsup_sum_ncard_crit_reduced_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:07:36.308399+00:00
-- url     : https://prove2.me/submissions/0dcbd7a1-58a8-4d69-bf73-4649e8e02be5

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg
import Theorems.Thm_Puder_isAlgExt_zpowers_of_mem_crit
import Theorems.Thm_Puder_setOf_isAlgExt_finite_of_fg
import Theorems.Thm_Puder_limsup_sum_ncard_isAlgExt_reduced_rpow_le

open Filter

namespace Puder.Q263P43

/-- The trivial subgroup has no basis with a nonempty index set. -/
theorem zpowers_ne_one_of_hasRank {d m : ℕ} (hm1 : 1 ≤ m) {w : FreeGroup (Fin d)}
    (h : HasRank (Subgroup.zpowers w) m) : w ≠ 1 := by
  rintro rfl
  obtain ⟨b⟩ := h
  have h1 : b ⟨0, hm1⟩ = 1 := by
    apply Subtype.ext
    have := (b ⟨0, hm1⟩).2
    simpa using this
  have := b.repr_apply_coe ⟨0, hm1⟩
  rw [h1, map_one] at this
  exact FreeGroup.of_ne_one _ this.symm

/-- A nontrivial element of a free group is primitive in the cyclic subgroup it generates. -/
theorem isPrimitiveIn_zpowers {d : ℕ} {w : FreeGroup (Fin d)} (hw : w ≠ 1) :
    IsPrimitiveIn (Subgroup.zpowers w) w := by
  have hord : orderOf w = 0 :=
    orderOf_eq_zero_iff.mpr (not_isOfFinOrder_of_isMulTorsionFree hw)
  let f : Multiplicative ℤ →* Subgroup.zpowers w :=
    zpowersHom (Subgroup.zpowers w) ⟨w, Subgroup.mem_zpowers w⟩
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro n hn
      have hn' : w ^ n.toAdd = 1 := by
        have := congrArg Subtype.val hn
        simpa [f] using this
      rw [zpow_eq_one_iff_modEq, hord] at hn'
      have : n.toAdd = 0 := by simpa [Int.ModEq] using hn'
      simpa using congrArg Multiplicative.ofAdd this
    · rintro ⟨x, n, rfl⟩
      exact ⟨Multiplicative.ofAdd n, Subtype.ext (by simp [f])⟩
  let e : Multiplicative ℤ ≃* Subgroup.zpowers w := MulEquiv.ofBijective f hf
  let b : FreeGroupBasis Unit (Subgroup.zpowers w) :=
    FreeGroupBasis.ofRepr (e.symm.trans (FreeGroup.mulEquivIntOfUnique (α := Unit)).symm)
  refine ⟨Unit, b, (), ?_⟩
  change ((e.symm.trans (FreeGroup.mulEquivIntOfUnique (α := Unit)).symm).symm
    (FreeGroup.of ()) : FreeGroup (Fin d)) = w
  simp [e, f, FreeGroup.mulEquivIntOfUnique, FreeGroup.equivIntOfUnique]

/-- Puder (4.1): `Crit w` sits inside the set of proper rank-`m` algebraic extensions of
`⟨w⟩` when `π(w) = m ≥ 1`. -/
theorem crit_subset {d m : ℕ} (hm1 : 1 ≤ m) {w : FreeGroup (Fin d)}
    (hπ : primitivityRank w = m) :
    Crit w ⊆ {J : Subgroup (FreeGroup (Fin d)) | HasRank J m ∧
      IsAlgExt (Subgroup.zpowers w) J ∧ Subgroup.zpowers w ≠ J} := by
  intro J hJ
  obtain ⟨hwJ, hnp, r, hr, hrπ⟩ := hJ
  have hrm : r = m := by rw [hπ] at hrπ; exact_mod_cast hrπ
  subst hrm
  refine ⟨hr, isAlgExt_zpowers_of_mem_crit ⟨hwJ, hnp, r, hr, hrπ⟩, ?_⟩
  rintro rfl
  exact hnp (isPrimitiveIn_zpowers (zpowers_ne_one_of_hasRank hm1 hr))

theorem ncard_crit_le {d m : ℕ} (hm1 : 1 ≤ m) {w : FreeGroup (Fin d)}
    (hπ : primitivityRank w = m) :
    (Crit w).ncard ≤ {J : Subgroup (FreeGroup (Fin d)) | HasRank J m ∧
      IsAlgExt (Subgroup.zpowers w) J ∧ Subgroup.zpowers w ≠ J}.ncard := by
  have hfin := setOf_isAlgExt_finite_of_fg (Subgroup.zpowers w)
    ⟨{w}, by simp [Subgroup.zpowers_eq_closure]⟩
  exact Set.ncard_le_ncard (crit_subset hm1 hπ) (hfin.subset fun J hJ => hJ.2.1)

end Puder.Q263P43

namespace Puder

theorem limsup_sum_ncard_crit_reduced_rpow_le_dev (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) atTop ≤
        if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1 := by
  obtain ⟨hb, hl⟩ := limsup_sum_ncard_isAlgExt_reduced_rpow_le k m hk hm1 hm
  set a : ℕ → ℝ := fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ)) with ha_def
  set b : ℕ → ℝ := fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              IsAlgExt (Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j)))) J ∧
              Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≠ J}.ncard : ℝ)) ^
          (1 / (t : ℝ)) with hb_def
  have ha0 : ∀ t, 0 ≤ a t := fun t =>
    Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) _
  have hab : ∀ t, a t ≤ b t := by
    intro t
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) _
      (by positivity)
    calc _ ≤ ∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              IsAlgExt (Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j)))) J ∧
              Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≠ J}.ncard : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact_mod_cast Q263P43.ncard_crit_le hm1 (Finset.mem_filter.mp hi).2.2
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_filter] at hi ⊢
            exact ⟨hi.1, hi.2.1⟩
          · intro _ _ _; exact Nat.cast_nonneg _
  have hba : IsBoundedUnder (· ≤ ·) atTop a := by
    obtain ⟨c, hc⟩ := hb
    exact ⟨c, (eventually_map.mp hc).mono fun t ht => (hab t).trans ht |> fun h => h⟩
  refine ⟨hba, le_trans ?_ hl⟩
  exact Filter.limsup_le_limsup (Eventually.of_forall hab)
    (isCoboundedUnder_le_of_le atTop ha0) hb

end Puder

theorem solution : type_of% @Puder.limsup_sum_ncard_crit_reduced_rpow_le_dev := @Puder.limsup_sum_ncard_crit_reduced_rpow_le_dev
