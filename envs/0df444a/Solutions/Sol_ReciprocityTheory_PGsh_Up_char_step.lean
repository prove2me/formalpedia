-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.char_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:52.675789+00:00
-- url     : https://prove2.me/submissions/c8b4c956-d37b-4c12-b350-cffed9699bba

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
import Theorems.Thm_ReciprocityTheory_PGsh_Up_det_ne_of_span
import Theorems.Thm_ReciprocityTheory_PGsh_Up_not_span_lt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mulVec_inj_of_det
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] [IsDomain R]
variable {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (c : R) (hc : c ≠ 0)
    (hspan : ∀ s (hs : s ≤ g), ∀ w : Fin s → R, c • w ∈ omTr M s hs) (s : ℕ) (hs1 : s + 1 ≤ g)
    (ι : Fin s → Fin N)
    (hι : Submodule.span R (Set.range fun i : Fin s => fun a : Fin s =>
      M (Fin.castLE (Nat.le_of_succ_le hs1) a) (ι i)) = omTr M s (Nat.le_of_succ_le hs1)) :
    ∃ b, b ∉ Set.range ι ∧ Submodule.span R (Set.range fun i : Fin (s + 1) => fun a : Fin (s + 1) =>
      M (Fin.castLE hs1 a) (Fin.snoc (α := fun _ => Fin N) ι b i)) = omTr M (s + 1) hs1 := by
  classical
  have hcast : ∀ a : Fin s, (Fin.castLE hs1 (Fin.castSucc a) : Fin g) =
      Fin.castLE (Nat.le_of_succ_le hs1) a := fun a => Fin.ext rfl
  set T : Fin N → Fin (s + 1) → R := fun b a => M (Fin.castLE hs1 a) b with hT
  set A : Matrix (Fin s) (Fin s) R :=
    Matrix.of fun a i => M (Fin.castLE (Nat.le_of_succ_le hs1) a) (ι i) with hA
  have hAdet : A.det ≠ 0 := by
    refine det_ne_of_span A c hc fun w => ?_
    have h1 := hspan s (Nat.le_of_succ_le hs1) w
    rw [← hι] at h1
    exact h1
  have hlam : ∀ b, ∃ l : Fin s → R, ∀ a : Fin s, M (Fin.castLE (Nat.le_of_succ_le hs1) a) b =
      ∑ i, l i * M (Fin.castLE (Nat.le_of_succ_le hs1) a) (ι i) := by
    intro b
    have hmem : (fun a : Fin s => M (Fin.castLE (Nat.le_of_succ_le hs1) a) b) ∈
        omTr M s (Nat.le_of_succ_le hs1) := Submodule.subset_span ⟨b, rfl⟩
    rw [← hι, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨l, hl⟩ := hmem
    refine ⟨l, fun a => ?_⟩
    have h2 := congrFun hl a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    exact h2.symm
  choose l hl using hlam
  have hlι : ∀ j, l (ι j) = Pi.single j 1 := by
    intro j
    apply mulVec_inj_of_det A hAdet
    funext a
    have h1 := hl (ι j) a
    simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  set μ : Fin N → R := fun b => T b (Fin.last s) - ∑ i, l b i * T (ι i) (Fin.last s) with hμ
  have hdecomp : ∀ b, T b = ∑ i, l b i • T (ι i) + μ b • (Pi.single (Fin.last s) 1 : Fin (s + 1) → R) := by
    intro b
    funext a
    induction a using Fin.lastCases with
    | last => simp [hμ, Finset.sum_apply]
    | cast a =>
      simpa [hT, Finset.sum_apply, Pi.single_apply, hcast, Fin.castSucc_ne_last] using hl b a
  have hex : ∃ b, μ b ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle : omTr M (s + 1) hs1 ≤ Submodule.span R (Set.range fun i => T (ι i)) := by
      rw [omTr, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      show T b ∈ _
      rw [hdecomp b, hall b, zero_smul, add_zero]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact not_span_lt (Matrix.of fun a i => T (ι i) a) c hc fun w => hle (hspan (s + 1) hs1 w)
  obtain ⟨b0, hb0⟩ := hex
  obtain ⟨bs, -, hbs⟩ := Finset.exists_max_image Finset.univ
    (fun b => v (algebraMap R C (μ b))) ⟨b0, Finset.mem_univ _⟩
  have hμs : μ bs ≠ 0 := by
    intro h
    have h1 := hbs b0 (Finset.mem_univ _)
    rw [h, map_zero, map_zero] at h1
    have h2 : v (algebraMap R C (μ b0)) = 0 := le_antisymm h1 zero_le
    rw [Valuation.zero_iff] at h2
    exact hb0 (hv.hom_inj (by rw [h2, map_zero]))
  have hbsι : bs ∉ Set.range ι := by
    rintro ⟨j, hj⟩
    apply hμs
    rw [← hj]
    simp [hμ, hlι j, Pi.single_apply]
  refine ⟨bs, hbsι, le_antisymm ?_ ?_⟩
  · rw [omTr, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Fin.snoc (α := fun _ => Fin N) ι bs i, rfl⟩
  · set S := Submodule.span R (Set.range fun i : Fin (s + 1) => fun a : Fin (s + 1) =>
      M (Fin.castLE hs1 a) (Fin.snoc (α := fun _ => Fin N) ι bs i)) with hS
    have hTι : ∀ i, T (ι i) ∈ S := fun i => by
      have h1 : (fun a : Fin (s + 1) => M (Fin.castLE hs1 a)
          (Fin.snoc (α := fun _ => Fin N) ι bs (Fin.castSucc i))) ∈ S :=
        Submodule.subset_span ⟨Fin.castSucc i, rfl⟩
      simpa only [Fin.snoc_castSucc] using h1
    have hTbs : T bs ∈ S := by
      have h1 : (fun a : Fin (s + 1) => M (Fin.castLE hs1 a)
          (Fin.snoc (α := fun _ => Fin N) ι bs (Fin.last s))) ∈ S :=
        Submodule.subset_span ⟨Fin.last s, rfl⟩
      simpa only [Fin.snoc_last] using h1
    have hE : μ bs • (Pi.single (Fin.last s) 1 : Fin (s + 1) → R) ∈ S := by
      have h2 : μ bs • (Pi.single (Fin.last s) 1 : Fin (s + 1) → R) =
          T bs - ∑ i, l bs i • T (ι i) := by
        rw [hdecomp bs]
        abel
      rw [h2]
      exact S.sub_mem hTbs (S.sum_mem fun i _ => S.smul_mem _ (hTι i))
    rw [omTr, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    show T b ∈ S
    obtain ⟨d, hd⟩ := hv.dvd_of_le (hbs b (Finset.mem_univ _))
    rw [hdecomp b, hd, mul_comm, mul_smul]
    exact S.add_mem (S.sum_mem fun i _ => S.smul_mem _ (hTι i)) (S.smul_mem _ hE)
end ReciprocityTheory.PGsh.Up
