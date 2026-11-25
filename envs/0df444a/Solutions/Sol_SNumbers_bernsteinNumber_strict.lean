-- Prove2me | solution 1 for SNumbers.bernsteinNumber_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:34.660773+00:00
-- url     : https://prove2.me/submissions/08342425-dd69-46d0-909c-3e13514708ee

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_gainOnSubspace_le_div
public import Theorems.Thm_SNumbers_le_gainOnSubspace
public import Theorems.Thm_SNumbers_bddAbove_bernsteinSet
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
private lemma gainOnSubspace_id_eq_one {M : Submodule 𝕜 X} (hM : M ≠ ⊥) :
    gainOnSubspace (ContinuousLinearMap.id 𝕜 X) M = 1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    refine (gainOnSubspace_le_div (S := ContinuousLinearMap.id 𝕜 X)
      hx_mem hx_ne).trans_eq ?_
    rw [ContinuousLinearMap.id_apply, div_self hx_pos.ne']
  · refine le_gainOnSubspace hM ?_
    intro x _ hx_ne
    rw [ContinuousLinearMap.id_apply, div_self (norm_pos_iff.mpr hx_ne).ne']
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
theorem _root_.solution {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    bernsteinNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  -- Construct an `(n+1)`-dim subspace `M ⊆ X`.
  have h' : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 X := by
    rw [Nat.cast_succ]; exact Cardinal.natCast_add_one_le_iff.mpr h
  obtain ⟨g, hg_li⟩ := exists_linearIndependent_of_le_rank h'
  set M : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range g)
  have hM_rank : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal) :=
    rank_span_range_fin hg_li
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: every gain in `bSet` is `1`.
    refine Real.sSup_le ?_ zero_le_one
    rintro _ ⟨M', hM'_rank, rfl⟩
    rw [gainOnSubspace_id_eq_one (rank_eq_succ_implies_ne_bot hM'_rank)]
  · -- `≥ 1`: `M` is a witness with gain `= 1`.
    refine (le_of_eq (gainOnSubspace_id_eq_one
      (rank_eq_succ_implies_ne_bot hM_rank)).symm).trans ?_
    exact le_csSup (bddAbove_bernsteinSet _ n) ⟨M, hM_rank, rfl⟩
end SNumbers
