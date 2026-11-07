-- Prove2me | solution 1 for Puder.limsup_sum_ncard_crit_rpow_eq_rhoStair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T09:43:56.196201+00:00
-- url     : https://prove2.me/submissions/562cb38c-3edb-449a-a13b-9744c7d77754
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Theorems.Thm_Puder_crit_finite_and_isBigO_uniformExp_card_fixedPoints
import Theorems.Thm_Puder_limsup_sum_ncard_crit_rpow_le_rhoStair
import Theorems.Thm_Puder_tendsto_card_primitivityRank_eq_rpow_rhoStair
import Theorems.Thm_Puder_limsup_card_wordFree_eq_one_rpow

section
open Filter Topology
namespace Puder.BQ.PartC
theorem freeGroup_fin_zero_eq_one (x : FreeGroup (Fin 0)) : x = 1 := by
  apply FreeGroup.toWord_injective
  rw [FreeGroup.toWord_one]
  rcases h : x.toWord with _ | ⟨a, _⟩
  · rfl
  · exact a.1.elim0

theorem eq_one_of_rank_zero {d : ℕ} {J : Subgroup (FreeGroup (Fin d))}
    (b : FreeGroupBasis (Fin 0) J) {x : FreeGroup (Fin d)} (hx : x ∈ J) : x = 1 := by
  have : b.repr ⟨x, hx⟩ = b.repr 1 := by
    rw [freeGroup_fin_zero_eq_one (b.repr ⟨x, hx⟩), freeGroup_fin_zero_eq_one (b.repr 1)]
  have := congrArg Subtype.val (b.repr.injective this)
  simpa using this

theorem eq_bot_of_rank_zero {d : ℕ} {J : Subgroup (FreeGroup (Fin d))}
    (b : FreeGroupBasis (Fin 0) J) : J = ⊥ :=
  (Subgroup.eq_bot_iff_forall J).mpr fun _ hx => eq_one_of_rank_zero b hx

theorem one_le_primitivityRank {d : ℕ} {w : FreeGroup (Fin d)} (hw : w ≠ 1) :
    1 ≤ primitivityRank w := by
  unfold primitivityRank
  refine le_iInf₂ fun r hr => ?_
  obtain ⟨J, hwJ, ⟨b⟩, -⟩ := hr
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact absurd (eq_one_of_rank_zero b hwJ) hw
  · exact_mod_cast hr

/-- The trivial subgroup has rank `0`. -/
theorem hasRank_bot (d : ℕ) : HasRank (⊥ : Subgroup (FreeGroup (Fin d))) 0 :=
  ⟨FreeGroupBasis.ofRepr
    { toFun := fun _ => 1
      invFun := fun _ => 1
      left_inv := fun x => by
        obtain ⟨x, hx⟩ := x
        rw [Subgroup.mem_bot] at hx
        subst hx
        rfl
      right_inv := fun x => (freeGroup_fin_zero_eq_one x).symm
      map_mul' := fun _ _ => (mul_one 1).symm }⟩

/-- `1` is primitive in no subgroup: basis elements are never `1`. -/
theorem not_isPrimitiveIn_one {d : ℕ} (J : Subgroup (FreeGroup (Fin d))) :
    ¬ IsPrimitiveIn J 1 := by
  rintro ⟨ι, b, i, hi⟩
  have h1 : b i = 1 := Subtype.ext hi
  have : b.repr (b i) = b.repr 1 := by rw [h1]
  rw [FreeGroupBasis.repr_apply_coe, map_one] at this
  exact FreeGroup.of_ne_one i this

theorem primitivityRank_one {d : ℕ} : primitivityRank (1 : FreeGroup (Fin d)) = 0 :=
  le_antisymm
    (iInf₂_le (f := fun (r : ℕ) (_ : ∃ J : Subgroup (FreeGroup (Fin d)),
        (1 : FreeGroup (Fin d)) ∈ J ∧ HasRank J r ∧ ¬ IsPrimitiveIn J 1) => (r : ℕ∞))
      0 ⟨⊥, Subgroup.one_mem _, hasRank_bot d, not_isPrimitiveIn_one _⟩)
    (zero_le)

theorem primitivityRank_eq_zero_iff {d : ℕ} {w : FreeGroup (Fin d)} :
    primitivityRank w = 0 ↔ w = 1 := by
  constructor
  · intro h
    by_contra hw
    have := one_le_primitivityRank hw
    rw [h] at this
    exact absurd this (by simp)
  · rintro rfl
    exact primitivityRank_one

end Puder.BQ.PartC
end

section
open Filter Topology
namespace Puder.BQ
/-! ### Part C: primitivity rank `0` and nonempty `Crit` -/
alias primitivityRank_eq_zero_iff := Puder.BQ.PartC.primitivityRank_eq_zero_iff

end Puder.BQ
end

section
open Filter Topology
namespace Puder.BQ.PartC
theorem ncard_crit_one {d : ℕ} : (Crit (1 : FreeGroup (Fin d))).ncard = 1 := by
  have : Crit (1 : FreeGroup (Fin d)) = {⊥} := by
    ext J
    simp only [Crit, Set.mem_singleton_iff, primitivityRank_one]
    constructor
    · rintro ⟨-, -, r, ⟨b⟩, hr⟩
      have : r = 0 := by exact_mod_cast hr
      subst this
      exact eq_bot_of_rank_zero b
    · rintro rfl
      exact ⟨Subgroup.one_mem _, not_isPrimitiveIn_one _, 0, hasRank_bot d, by simp⟩
  rw [this, Set.ncard_singleton]

end Puder.BQ.PartC
end

section
open Filter Topology
namespace Puder.BQ
alias ncard_crit_one := Puder.BQ.PartC.ncard_crit_one

end Puder.BQ
end

section
open Filter Topology
namespace Puder.BQ.PartC
theorem crit_nonempty {d : ℕ} {w : FreeGroup (Fin d)} {r : ℕ} (hr : primitivityRank w = r) :
    (Crit w).Nonempty := by
  classical
  let P : ℕ → Prop := fun r => ∃ J : Subgroup (FreeGroup (Fin d)),
    w ∈ J ∧ HasRank J r ∧ ¬ IsPrimitiveIn J w
  have hex : ∃ r, P r := by
    by_contra hne
    push Not at hne
    have : primitivityRank w = ⊤ :=
      le_antisymm le_top (le_iInf₂ fun r hr => absurd hr (by simpa [P] using hne r))
    rw [hr] at this
    exact ENat.natCast_ne_top r this
  have hmin : primitivityRank w = (Nat.find hex : ℕ∞) := by
    refine le_antisymm (iInf₂_le (f := fun (r : ℕ) (_ : P r) => (r : ℕ∞)) _ (Nat.find_spec hex))
      (le_iInf₂ fun r hr => ?_)
    exact_mod_cast Nat.find_min' hex hr
  obtain ⟨J, hwJ, hJ, hn⟩ := Nat.find_spec hex
  exact ⟨J, hwJ, hn, Nat.find hex, hJ, hmin.symm⟩

end Puder.BQ.PartC
end

section
open Filter Topology
namespace Puder.BQ
alias crit_nonempty := Puder.BQ.PartC.crit_nonempty

theorem one_le_ncard_crit {d : ℕ} {w : FreeGroup (Fin d)} {r : ℕ} (hr : primitivityRank w = r) :
    1 ≤ (Crit w).ncard := by
  obtain ⟨hfin, -⟩ := Puder.crit_finite_and_isBigO_uniformExp_card_fixedPoints d w r hr
  exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos hfin).mpr (crit_nonempty hr)).ne'

end Puder.BQ
end

section
open Filter Topology
open Puder.BQ in
theorem Puder.limsup_sum_ncard_crit_rpow_eq_rhoStair_dev (d m : ℕ) (hd : 2 ≤ d) (hm : m ≤ d) :
    IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ =>
        (∑ i : Fin p → Fin d ⊕ Fin d with
            Puder.primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Puder.Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (p : ℝ))) ∧
      limsup (fun p : ℕ =>
        (∑ i : Fin p → Fin d ⊕ Fin d with
            Puder.primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Puder.Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (p : ℝ))) atTop = StrongConv.rhoStair d m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · -- `m = 0`: the words reducing to `1`, each with the one critical subgroup `{1}`
    have hsum : ∀ p : ℕ, (∑ i : Fin p → Fin d ⊕ Fin d with
            Puder.primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = (0 : ℕ),
          ((Puder.Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) =
        ((Finset.univ.filter fun i : Fin p → Fin d ⊕ Fin d =>
            StrongConv.wordFree (List.ofFn fun j => some (i j)) = 1).card : ℝ) := by
      intro p
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr ?_ ?_
      · ext i; simp [primitivityRank_eq_zero_iff]
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_zero,
          primitivityRank_eq_zero_iff] at hi
        rw [hi, ncard_crit_one]
    simp_rw [hsum]
    have hrho : StrongConv.rhoStair d 0 = 2 * Real.sqrt (2 * d - 1) := by
      unfold StrongConv.rhoStair
      rw [if_pos]
      have : (0 : ℝ) ≤ Real.sqrt (2 * d - 1) := Real.sqrt_nonneg _
      push_cast; linarith
    rw [hrho]
    exact Puder.limsup_card_wordFree_eq_one_rpow d hd
  · obtain ⟨hB, hle⟩ := Puder.limsup_sum_ncard_crit_rpow_le_rhoStair d m hd hm1 hm
    refine ⟨hB, le_antisymm hle ?_⟩
    have hT := Puder.tendsto_card_primitivityRank_eq_rpow_rhoStair d m hd hm1 hm
    rw [← hT.limsup_eq]
    refine limsup_le_limsup (Eventually.of_forall fun p => ?_) hT.isCoboundedUnder_le hB
    dsimp only
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact_mod_cast one_le_ncard_crit hi

end

section
open Filter Topology
theorem solution (d m : ℕ) (hd : 2 ≤ d) (hm : m ≤ d) :
    IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ =>
        (∑ i : Fin p → Fin d ⊕ Fin d with
            Puder.primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Puder.Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (p : ℝ))) ∧
      limsup (fun p : ℕ =>
        (∑ i : Fin p → Fin d ⊕ Fin d with
            Puder.primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Puder.Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (p : ℝ))) atTop = StrongConv.rhoStair d m := by
  exact Puder.limsup_sum_ncard_crit_rpow_eq_rhoStair_dev d m hd hm
end
