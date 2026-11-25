-- Prove2me | solution 1 for SNumbers.bernsteinNumber_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:49:07.67128+00:00
-- url     : https://prove2.me/submissions/8ade1ff1-cfb8-4c95-a781-8b471066f3d3

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_bddAbove_bernsteinSet
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg
public import Theorems.Thm_SNumbers_gainOnSubspace_anti
section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
private lemma rank_eq_succ_implies_ne_bot {M : Submodule 𝕜 X} {n : ℕ}
    (hM_rank : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal)) :
    M ≠ ⊥ := fun hM_bot => by
  rw [hM_bot, rank_bot] at hM_rank
  exact Nat.succ_ne_zero n (by exact_mod_cast hM_rank.symm)
private lemma rank_span_range_fin {V : Type u} [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} {g : Fin n → V} (hg : LinearIndependent 𝕜 g) :
    Module.rank 𝕜 (Submodule.span 𝕜 (Set.range g)) = (n : Cardinal) := by
  classical
  have : Fintype (Set.range g) := Set.fintypeRange g
  rw [rank_span hg, Cardinal.mk_fintype, Set.card_range_of_injective hg.injective,
      Fintype.card_fin]
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S (n + 1) ≤ bernsteinNumber S n := by
  refine Real.sSup_le ?_ (bernsteinNumber_nonneg S n)
  rintro _ ⟨M, hM_rank, rfl⟩
  -- `M` has rank `n + 2`. Pick an `(n+1)`-dim subspace `M' ⊆ M`.
  have hM_rank' : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 M := by
    rw [hM_rank]; exact_mod_cast Nat.le_succ _
  obtain ⟨f, hf_li⟩ := exists_linearIndependent_of_le_rank hM_rank'
  set g : Fin (n + 1) → X := fun i => (f i : X) with hg_def
  have hg_li : LinearIndependent 𝕜 g :=
    (M.subtype.linearIndependent_iff (Submodule.ker_subtype M)).mpr hf_li
  set M' : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range g) with hM'_def
  have hM'_rank : Module.rank 𝕜 M' = ((n + 1 : ℕ) : Cardinal) :=
    rank_span_range_fin hg_li
  have hM'_le : M' ≤ M := by
    rw [hM'_def]
    exact Submodule.span_le.mpr <| by rintro _ ⟨i, rfl⟩; exact (f i).2
  calc gainOnSubspace S M
      ≤ gainOnSubspace S M' :=
        gainOnSubspace_anti hM'_le (rank_eq_succ_implies_ne_bot hM'_rank)
    _ ≤ bernsteinNumber S n := le_csSup (bddAbove_bernsteinSet S n) ⟨M', hM'_rank, rfl⟩
end SNumbers
