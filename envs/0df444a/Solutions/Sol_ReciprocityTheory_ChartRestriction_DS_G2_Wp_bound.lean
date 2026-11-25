-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.G2.Wp_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:22.387017+00:00
-- url     : https://prove2.me/submissions/bfc06af8-c37f-433d-a2ca-d8e6e2a66296

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_StdGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_CrossOpEigGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_NcVOneDecomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_G2_crossOp_eig_gap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_eig_gap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_crossOp_eig_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
section OneB
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
private lemma mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : Module.End ℂ W) (hT : ∀ u v, inner ℂ (T u) v = inner ℂ u (T v)) (c : ℝ)
    {ι : Type*} [DecidableEq ι] (θ : ι → ℝ) (y : ι → W) (s : Finset ι)
    (hy : ∀ i ∈ s, T (y i) = ((θ i : ℝ) : ℂ) • y i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (y i) (y j) = 0)
    (hc : ∀ i ∈ s, y i ≠ 0 → c ≤ θ i) :
    c * ‖∑ i ∈ s, y i‖ ^ 2 ≤ RCLike.re (inner ℂ (T (∑ i ∈ s, y i)) (∑ i ∈ s, y i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have IH := ih (fun j hj => hy j (Finset.mem_insert_of_mem hj))
      (fun a ha b hb hab => horth a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab)
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    have h0 : inner ℂ (y i) (∑ j ∈ s, y j) = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun j hj => horth i (Finset.mem_insert_self i s) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have h0' : inner ℂ (∑ j ∈ s, y j) (y i) = 0 := by
      rw [← inner_conj_symm, h0, map_zero]
    have hTi : T (y i) = ((θ i : ℝ) : ℂ) • y i := hy i (Finset.mem_insert_self i s)
    have h1 : inner ℂ (T (y i)) (∑ j ∈ s, y j) = 0 := by
      rw [hTi, inner_smul_left, h0, mul_zero]
    have h2 : inner ℂ (T (∑ j ∈ s, y j)) (y i) = 0 := by
      rw [hT, hTi, inner_smul_right, h0', mul_zero]
    have h3 : RCLike.re (inner ℂ (T (y i)) (y i)) = θ i * ‖y i‖ ^ 2 := by
      rw [hTi, inner_smul_left, Complex.conj_ofReal, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact Complex.re_ofReal_mul _ _
    have hn : ‖y i + ∑ j ∈ s, y j‖ ^ 2 = ‖y i‖ ^ 2 + ‖∑ j ∈ s, y j‖ ^ 2 := by
      rw [@norm_add_sq ℂ, h0]; simp
    have hre : RCLike.re (inner ℂ (T (y i + ∑ j ∈ s, y j)) (y i + ∑ j ∈ s, y j)) =
        θ i * ‖y i‖ ^ 2 + RCLike.re (inner ℂ (T (∑ j ∈ s, y j)) (∑ j ∈ s, y j)) := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2, add_zero, zero_add,
        map_add, h3]
    rw [hn, hre]
    by_cases hyi : y i = 0
    · rw [hyi]; simp only [norm_zero]; nlinarith [IH]
    · have := hc i (Finset.mem_insert_self i s) hyi
      nlinarith [IH, mul_le_mul_of_nonneg_right this (sq_nonneg ‖y i‖)]
end OneB
end ReciprocityTheory.ChartRestriction.DS.G2
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.G2
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {x : Big n 1 M} (hx : x ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖x‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by
  classical
  have hx' : x ∈ ⨆ θ : {θ : ℝ // 0 < θ},
      Module.End.eigenspace (crossOp ε E 1 0) (((θ : ℝ)) : ℂ) ⊓ ncV ε V 1 := by
    have h1 : x ∈ ⨆ (θ : ℝ) (_ : 0 < θ),
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 := hx
    rwa [iSup_subtype'] at h1
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have key := mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen (crossOp ε E 1 0) (crossOp_symm hU 1 0) (h - n + 1)
    (fun θ : {θ : ℝ // 0 < θ} => (θ : ℝ)) f f.support
    (fun i _ => Module.End.mem_eigenspace_iff.1 (hf i).1)
    (fun i _ j _ hij => inner_crossOp_eig_eq_zero hU (fun h' => hij (Subtype.ext h'))
      (Module.End.mem_eigenspace_iff.1 (hf i).1) (Module.End.mem_eigenspace_iff.1 (hf j).1))
    (fun i _ hi0 => by
      rcases crossOp_eig_gap hE hU hV hmono hh hbig (hf i) hi0 with h1 | h1
      · exact h1.2
      · exact absurd i.2 (by linarith [h1.1, h1.2]))
  simp only [Finsupp.sum]
  linarith [key]
end ReciprocityTheory.ChartRestriction.DS.G2
