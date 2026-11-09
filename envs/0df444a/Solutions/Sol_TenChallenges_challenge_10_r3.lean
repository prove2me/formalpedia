-- Prove2me | solution 1 for TenChallenges.challenge_10_r3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:51:53.969846+00:00
-- url     : https://prove2.me/submissions/0adba33c-c253-4809-a84d-0a6ac6864dec

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Finite.Basic

universe u v

namespace Aux_TC10_R3

open Classical SimpleGraph
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

lemma partitionerWins_mono {f : V → Option Bool} {α β : Ordinal.{v}}
    (hβα : β ≤ α) (h : PartitionerWins G f α) : PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  intro v γ hγ
  exact h v γ (hγ.trans_le hβα)

lemma partitionerWins_zero (f : V → Option Bool) : PartitionerWins G f (0 : Ordinal.{v}) := by
  rw [PartitionerWins]
  intro v β hβ
  exact absurd hβ (not_lt_of_ge zero_le)

lemma extends_refl (f : V → Option Bool) : Extends f f :=
  fun _ _ h => h

lemma extends_update_of_none {f : V → Option Bool} {v : V} (hv : f v = none) (b : Bool) :
    Extends f (Function.update f v (some b)) := by
  intro x c hfx
  have hxv : x ≠ v := by
    intro h
    subst h
    rw [hv] at hfx
    cases hfx
  simp [Function.update_of_ne hxv, hfx]

lemma hasFiniteDomain_empty : HasFiniteDomain (emptyPartition V) := by
  simp [HasFiniteDomain, emptyPartition]

lemma hasFiniteDomain_update {f : V → Option Bool} (hf : HasFiniteDomain f) (v : V) (b : Option Bool) :
    HasFiniteDomain (Function.update f v b) := by
  refine (hf.insert v).subset fun x hx => ?_
  by_cases hxv : x = v
  · subst hxv
    exact Set.mem_insert _ _
  · right
    simpa [Function.update_of_ne hxv] using hx

lemma unfriendlyAt_of_no_same {f : V → Option Bool} {v : V} (b : Bool)
    (hfv : f v = some b) (hno : ∀ w, G.Adj v w → f w ≠ some b) :
    UnfriendlyAt G f v := by
  refine ⟨b, hfv, ?_⟩
  have hempty : IsEmpty (NeighColored G f v (some b)) := by
    refine ⟨fun ⟨w, hw⟩ => ?_⟩
    exact hno w hw.1 hw.2
  rw [Cardinal.mk_eq_zero]
  exact zero_le

lemma step1 (v₁ : V) :
    let g₁ := Function.update (emptyPartition V) v₁ (some false)
    IsLegalResponse G (emptyPartition V) g₁ v₁ := by
  intro g₁
  refine ⟨extends_update_of_none rfl false,
    hasFiniteDomain_update hasFiniteDomain_empty v₁ (some false), ?_⟩
  refine unfriendlyAt_of_no_same G false (by simp [g₁]) ?_
  intro w hadj
  have hw : w ≠ v₁ := G.ne_of_adj hadj |>.symm
  simp [g₁, Function.update_of_ne hw, emptyPartition]

lemma step2 (v₁ v₂ : V) :
    let g₁ := Function.update (emptyPartition V) v₁ (some false)
    let g₂ := if v₂ = v₁ then g₁ else Function.update g₁ v₂ (some true)
    IsLegalResponse G g₁ g₂ v₂ := by
  intro g₁ g₂
  have hg₁_fin : HasFiniteDomain g₁ :=
    hasFiniteDomain_update hasFiniteDomain_empty v₁ (some false)
  by_cases hv : v₂ = v₁
  · subst hv
    have hg₂ : g₂ = g₁ := if_pos rfl
    rw [hg₂]
    refine ⟨extends_refl g₁, hg₁_fin, (step1 G v₂).2.2⟩
  · have hg₂ : g₂ = Function.update g₁ v₂ (some true) := if_neg hv
    rw [hg₂]
    have hg₁v₂ : g₁ v₂ = none := by simp [g₁, Function.update_of_ne hv, emptyPartition]
    refine ⟨extends_update_of_none hg₁v₂ true,
      hasFiniteDomain_update hg₁_fin v₂ (some true), ?_⟩
    refine unfriendlyAt_of_no_same G true (by simp) ?_
    intro w hadj
    have hw₂ : w ≠ v₂ := G.ne_of_adj hadj |>.symm
    rw [Function.update_of_ne hw₂]
    by_cases hw₁ : w = v₁
    · subst hw₁
      simp [g₁]
    · simp [g₁, Function.update_of_ne hw₁, emptyPartition]

lemma step3 (v₁ v₂ v₃ : V) :
    let g₁ := Function.update (emptyPartition V) v₁ (some false)
    let g₂ := if v₂ = v₁ then g₁ else Function.update g₁ v₂ (some true)
    ∃ g₃ : V → Option Bool, IsLegalResponse G g₂ g₃ v₃ := by
  intro g₁ g₂
  have hg₁_fin : HasFiniteDomain g₁ :=
    hasFiniteDomain_update hasFiniteDomain_empty v₁ (some false)
  have hg₂_fin : HasFiniteDomain g₂ := by
    by_cases hv : v₂ = v₁
    · simpa [g₂, hv] using hg₁_fin
    · simpa [g₂, hv] using hasFiniteDomain_update hg₁_fin v₂ (some true)
  have hg₂_v₁ : g₂ v₁ = some false := by
    by_cases hv : v₂ = v₁
    · simp [g₂, hv, g₁]
    · simp [g₂, hv, Function.update_of_ne (Ne.symm hv), g₁]
  have hg₂_false : ∀ w, g₂ w = some false → w = v₁ := by
    intro w hw
    by_contra hne
    by_cases hv : v₂ = v₁
    · simp [g₂, hv, g₁, Function.update_of_ne hne, emptyPartition] at hw
    · by_cases hw₂ : w = v₂
      · subst hw₂
        simp [g₂, hv] at hw
      · simp [g₂, hv, Function.update_of_ne hw₂, g₁, Function.update_of_ne hne, emptyPartition] at hw
  have hg₂_true : ∀ w, g₂ w = some true → w = v₂ := by
    intro w hw
    by_contra hne
    by_cases hv : v₂ = v₁
    · subst hv
      simp [g₂, g₁, Function.update_of_ne hne, emptyPartition] at hw
    · simp [g₂, hv, Function.update_of_ne hne] at hw
      by_cases hw₁ : w = v₁
      · subst hw₁
        simp [g₁] at hw
      · simp [g₁, Function.update_of_ne hw₁, emptyPartition] at hw
  by_cases h31 : v₃ = v₁
  · subst h31
    refine ⟨g₂, extends_refl g₂, hg₂_fin, ?_⟩
    refine unfriendlyAt_of_no_same G false hg₂_v₁ ?_
    intro w hadj hgw
    exact G.ne_of_adj hadj (hg₂_false w hgw).symm
  · by_cases h32 : v₃ = v₂
    · subst h32
      exact ⟨g₂, extends_refl g₂, hg₂_fin, (step2 G v₁ v₃).2.2⟩
    · have hg₂_v₃ : g₂ v₃ = none := by
        by_cases hv : v₂ = v₁
        · simp [g₂, hv, g₁, Function.update_of_ne h31, emptyPartition]
        · simp [g₂, hv, Function.update_of_ne h32, g₁, Function.update_of_ne h31, emptyPartition]
      by_cases hadj1 : G.Adj v₃ v₁
      · let g₃ := Function.update g₂ v₃ (some true)
        refine ⟨g₃, extends_update_of_none hg₂_v₃ true,
          hasFiniteDomain_update hg₂_fin v₃ (some true), ?_⟩
        refine ⟨true, by simp [g₃], ?_⟩
        have hle1 : #(NeighColored G g₃ v₃ (some true)) ≤ 1 := by
          unfold NeighColored
          rw [Cardinal.mk_le_one_iff_set_subsingleton]
          rintro x ⟨hx_adj, hx_col⟩ y ⟨hy_adj, hy_col⟩
          have hx3 : x ≠ v₃ := G.ne_of_adj hx_adj |>.symm
          have hy3 : y ≠ v₃ := G.ne_of_adj hy_adj |>.symm
          have hx2 : x = v₂ := hg₂_true x (by simpa [g₃, Function.update_of_ne hx3] using hx_col)
          have hy2 : y = v₂ := hg₂_true y (by simpa [g₃, Function.update_of_ne hy3] using hy_col)
          exact hx2.trans hy2.symm
        have hge1 : (1 : Cardinal) ≤ #(NeighColored G g₃ v₃ (some false)) := by
          rw [Cardinal.one_le_iff_ne_zero, Cardinal.mk_ne_zero_iff]
          refine ⟨⟨v₁, hadj1, ?_⟩⟩
          change g₃ v₁ = some false
          simpa [g₃, Function.update_of_ne (Ne.symm h31)] using hg₂_v₁
        exact hle1.trans hge1
      · let g₃ := Function.update g₂ v₃ (some false)
        refine ⟨g₃, extends_update_of_none hg₂_v₃ false,
          hasFiniteDomain_update hg₂_fin v₃ (some false), ?_⟩
        refine unfriendlyAt_of_no_same G false (by simp [g₃]) ?_
        intro w hadj hgw
        have hw3 : w ≠ v₃ := G.ne_of_adj hadj |>.symm
        have hw1 : w = v₁ := hg₂_false w (by simpa [g₃, Function.update_of_ne hw3] using hgw)
        subst hw1
        exact hadj1 hadj

theorem win_three : PartitionerWins G (emptyPartition V) (3 : Ordinal.{v}) := by
  rw [PartitionerWins]
  intro v₁ α₁ hα₁
  let g₁ := Function.update (emptyPartition V) v₁ (some false)
  refine ⟨g₁, step1 G v₁, ?_⟩
  have h3 : (3 : Ordinal.{v}) = (2 : Ordinal.{v}) + (1 : Ordinal.{v}) :=
    two_add_one_eq_three.symm
  rw [h3, Order.lt_add_one_iff] at hα₁
  refine partitionerWins_mono G hα₁ ?_
  rw [PartitionerWins]
  intro v₂ α₂ hα₂
  let g₂ := if v₂ = v₁ then g₁ else Function.update g₁ v₂ (some true)
  refine ⟨g₂, step2 G v₁ v₂, ?_⟩
  have h2 : (2 : Ordinal.{v}) = (1 : Ordinal.{v}) + (1 : Ordinal.{v}) :=
    one_add_one_eq_two.symm
  rw [h2, Order.lt_add_one_iff] at hα₂
  refine partitionerWins_mono G hα₂ ?_
  rw [PartitionerWins]
  intro v₃ α₃ hα₃
  obtain ⟨g₃, hg₃⟩ := step3 G v₁ v₂ v₃
  refine ⟨g₃, hg₃, ?_⟩
  have h1 : (1 : Ordinal.{v}) = (0 : Ordinal.{v}) + (1 : Ordinal.{v}) :=
    (zero_add (1 : Ordinal.{v})).symm
  rw [h1, Order.lt_add_one_iff] at hα₃
  have hα₃_eq : α₃ = 0 := le_antisymm hα₃ zero_le
  rw [hα₃_eq]
  exact partitionerWins_zero G g₃

end Aux_TC10_R3

open Aux_TC10_R3 TenChallenges in
theorem solution : statement_10.{u, v} 3 := by
  intro V _ G
  exact win_three G
