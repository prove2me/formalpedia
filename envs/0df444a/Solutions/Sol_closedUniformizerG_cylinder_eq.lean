-- Prove2me | solution 1 for closedUniformizerG_cylinder_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:22.54935+00:00
-- url     : https://prove2.me/submissions/8aa55cac-dbc8-486e-9f7f-480f176c32e4

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_closedFiberG_nonempty_iff
import Theorems.Thm_leftmostAuxG_eq
import Theorems.Thm_leftmostBranchG_least

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    (f : ℕ → ℕ) (n : ℕ) :
    { x | ∀ i < n, closedUniformizerG F hF hne x i = f i } =
      (projFiberCylNG F f n ∩
        ⋂ (m : Fin n), ⋂ (j : Fin (f m)),
          (projFiberCylNG F (Function.update f m j) (↑m + 1))ᶜ) ∪
      ((Prod.fst '' F)ᶜ ∩ { _x | ∀ i < n, hne.some.2 i = f i }) := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iInter, mem_compl_iff,
    projFiberCylNG, fiberRestNG, mem_ofPred_eq]
  constructor
  · intro hx
    by_cases hcf : (closedFiberG F x).Nonempty
    · left
      have hx' : ∀ i < n, leftmostBranchG F x hcf i = f i := by
        intro i hi; have := hx i hi
        simp only [closedUniformizerG, dif_pos hcf] at this; exact this
      constructor
      · have := (leftmostAuxG F x hcf n).2; rw [fiberRestNG] at this
        obtain ⟨y, hy_mem, hy_ext⟩ := this
        exact ⟨y, hy_mem, fun i hi =>
          (hy_ext i hi).trans ((leftmostAuxG_eq F x hcf n i hi).trans (hx' i hi))⟩
      · intro ⟨m, hm⟩ ⟨j, hj⟩ hmem
        apply leftmostBranchG_least F x hcf m j (by rw [hx' m hm]; exact hj)
        obtain ⟨y, hy_mem, hy_ext⟩ := hmem
        refine ⟨y, hy_mem, fun i hi => ?_⟩
        have hye := hy_ext i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · rw [Function.update_of_ne (show (i : ℕ) ≠ m from by omega)] at hye ⊢
          rwa [leftmostAuxG_eq F x hcf m i h, hx' i (by omega)]
        · subst h; rwa [Function.update_self] at hye ⊢
    · right
      exact ⟨fun h => hcf ((closedFiberG_nonempty_iff F x).mpr h),
             fun i hi => by have := hx i hi; simp [closedUniformizerG, dif_neg hcf] at this; exact this⟩
  · rintro (⟨hproj, hmin⟩ | ⟨hnotproj, hdef⟩)
    · intro i hi
      simp only [closedUniformizerG]
      split
      · next hcf =>
        suffices key : ∀ j < n, leftmostBranchG F x hcf j = f j from key i hi
        intro j hj
        induction j using Nat.strongRecOn with
        | _ j IH =>
        apply le_antisymm
        · apply Nat.find_min'
          obtain ⟨y, hy_mem, hy_ext⟩ := hproj
          exact ⟨y, hy_mem, fun k hk => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
            · rw [Function.update_of_ne (by omega),
                   leftmostAuxG_eq F x hcf j k hlt, IH k hlt (by omega)]
              exact hy_ext k (by omega)
            · rw [heq, Function.update_self]; exact hy_ext _ (by omega)⟩
        · by_contra hlt; rw [not_le] at hlt
          have hspec := Nat.find_spec (exists_extNG (leftmostAuxG F x hcf j).2)
          obtain ⟨y', hy'_mem, hy'_ext⟩ := hspec
          have hmemN : x ∈ projFiberCylNG F
              (Function.update f j (leftmostBranchG F x hcf j)) (j + 1) :=
            ⟨y', hy'_mem, fun k hk => by
              have hye := hy'_ext k hk
              rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt' | heq
              · rw [Function.update_of_ne (by omega)] at hye ⊢
                rw [leftmostAuxG_eq F x hcf j k hlt', IH k hlt' (by omega)] at hye
                exact hye
              · rw [heq, Function.update_self] at hye ⊢; exact hye⟩
          exact absurd hmemN (hmin ⟨j, hj⟩ ⟨leftmostBranchG F x hcf j, hlt⟩)
      · next hncf =>
        exfalso; apply hncf
        obtain ⟨y, hy_mem, _⟩ := hproj; exact ⟨y, hy_mem⟩
    · intro i hi
      simp only [closedUniformizerG, dif_neg (by
        intro h; exact hnotproj ((closedFiberG_nonempty_iff F x).mp h))]
      exact hdef i hi
