-- Prove2me | solution 1 for SNumbers.exists_kolmogorov_flag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:22:03.461818+00:00
-- url     : https://prove2.me/submissions/88cbbcd7-9ed0-473d-b3d3-bfe17fbe8d67

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_exists_norm_mkQL_gt_of_lt_kolmogorovNumber
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
public import Theorems.Thm_Submodule_norm_mkQL_apply_le
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL


section
@[expose] public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma rank_span_range_le {k : ℕ} (y : Fin k → Y) :
    Module.rank 𝕜 (Submodule.span 𝕜 (Set.range y)) ≤ (k : Cardinal) := by
  classical
  -- Present the range as a `Finset`, so that the bound is a cast of a
  -- natural number and no universe lifting is involved.
  have hset : Set.range y = ((Finset.univ.image y : Finset Y) : Set Y) := by simp
  rw [hset]
  refine (rank_span_finset_le _).trans ?_
  have hcard : (Finset.univ.image y).card ≤ k := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := y)
  exact_mod_cast hcard
private lemma lt_norm_add_of_lt_norm_mkQL {V : Submodule 𝕜 Y} {y w : Y} {γ : ℝ}
    (hy : γ < ‖V.mkQL y‖) (hw : w ∈ V) : γ < ‖y + w‖ := by
  have hw0 : V.mkQL w = 0 := by
    simp only [Submodule.mkQL_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hw
  calc γ < ‖V.mkQL y‖ := hy
    _ = ‖V.mkQL (y + w)‖ := by rw [map_add, hw0, add_zero]
    _ ≤ ‖y + w‖ := V.norm_mkQL_apply_le _
section Identity
open MeasureTheory
end Identity
section Hilbert
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
end Hilbert
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ}
    (hγd : γ < kolmogorovNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ (x : Fin m → X) (V : Fin m → Submodule 𝕜 Y),
      (∀ j, ‖x j‖ ≤ 1) ∧
      (∀ j k : Fin m, k < j → S (x k) ∈ V j) ∧
      (∀ (j : Fin m) (w : Y), w ∈ V j → γ < ‖S (x j) + w‖) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, Fin.elim0, (fun j => j.elim0), (fun j => j.elim0),
      (fun j => j.elim0)⟩
  | succ k ih =>
    intro hk
    obtain ⟨x', V', hx'norm, hx'mem, hx'gt⟩ := ih (Nat.le_of_succ_le hk)
    -- The span of the images chosen so far has dimension at most `k ≤ n`.
    set W : Submodule 𝕜 Y := Submodule.span 𝕜 (Set.range fun i : Fin k => S (x' i))
      with hW
    have hWrank : Module.rank 𝕜 W ≤ (n : Cardinal) :=
      (rank_span_range_le _).trans (by exact_mod_cast Nat.le_of_succ_le_succ hk)
    obtain ⟨xm, hxm_norm, hxm_gt⟩ :=
      exists_norm_mkQL_gt_of_lt_kolmogorovNumber S hWrank hγd
    refine ⟨Fin.snoc x' xm, Fin.snoc V' W, ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hxm_norm
      | cast j' => simpa using hx'norm j'
    · intro j
      induction j using Fin.lastCases with
      | last =>
        intro i hi
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last (ne_of_lt hi)
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        exact Submodule.subset_span ⟨i', rfl⟩
      | cast j' =>
        intro i hi
        have hne : i ≠ Fin.last k := ne_of_lt (hi.trans (Fin.castSucc_lt_last j'))
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hne
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hx'mem j' i' (Fin.castSucc_lt_castSucc_iff.mp hi)
    · intro j
      induction j using Fin.lastCases with
      | last =>
        intro w hw
        rw [Fin.snoc_last] at hw ⊢
        exact lt_norm_add_of_lt_norm_mkQL hxm_gt hw
      | cast j' =>
        intro w hw
        rw [Fin.snoc_castSucc] at hw ⊢
        exact hx'gt j' w hw
end SNumbers
