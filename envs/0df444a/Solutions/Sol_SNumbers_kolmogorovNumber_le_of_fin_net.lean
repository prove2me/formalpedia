-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_le_of_fin_net
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:59:20.435079+00:00
-- url     : https://prove2.me/submissions/e85b0e8c-b0c9-40bf-aadb-b9de0bc5aee6

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_ContinuousLinearMap_opNorm_le_of_unit_closedBall
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
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
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
theorem _root_.solution {S : X →L[𝕜] Y} {k : ℕ} {y : Fin k → Y}
    {ε : ℝ} (hcov : ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε) :
    kolmogorovNumber S k ≤ ε := by
  set V : Submodule 𝕜 Y := Submodule.span 𝕜 (Set.range y) with hV
  refine (kolmogorovNumber_le_deviation (rank_span_range_le y)).trans ?_
  show ‖V.mkQL.comp S‖ ≤ ε
  refine ContinuousLinearMap.opNorm_le_of_unit_closedBall _ fun x hx => ?_
  obtain ⟨i, hi⟩ := hcov x hx
  -- `y i` lies in `V`, so it is killed by the quotient map.
  have hzero : V.mkQL (y i) = 0 := by
    simp only [Submodule.mkQL_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨i, rfl⟩
  calc ‖(V.mkQL.comp S) x‖
      = ‖V.mkQL (S x - y i)‖ := by
        simp only [coe_comp, Function.comp_apply, map_sub, hzero, sub_zero]
    _ ≤ ‖S x - y i‖ := V.norm_mkQL_apply_le _
    _ ≤ ε := hi
end SNumbers
