-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.hlow_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:41.746715+00:00
-- url     : https://prove2.me/submissions/7c630634-0027-4064-9c0e-fe42a296d5db

import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_prefix_prod_ge_one
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_TB_injective
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_eq_TB
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_TB
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_li_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B) :
    ∃ c : ℝ, 0 < c ∧ ∀ (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (k : Fin d),
      c ≤ ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs (fun i => fB B (e i)) j‖ ^ 2 := by
  classical
  obtain ⟨K, hKpos, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (TB B)).mp (TB_injective A B hA hAB)
  have hbound : ∀ v, ‖v‖ ≤ (K : ℝ) * ‖TB B v‖ := by
    intro v
    have h := hK.le_mul_dist v 0
    simpa [dist_zero_right] using h
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  set m : ℝ := min 1 (((K : ℝ)⁻¹) ^ 2) with hm
  have hm0 : 0 < m := lt_min one_pos (pow_pos (inv_pos.mpr hK0) 2)
  have hm1 : m ≤ 1 := min_le_left _ _
  refine ⟨m ^ d, pow_pos hm0 d, ?_⟩
  intro e k
  obtain ⟨h1, -⟩ := li_basis A B hA hAB e
  have hone := prefix_prod_ge_one e h1 k
  have hterm : ∀ j : Fin d, m * ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 ≤
      ‖gs (fun i => fB B (e i)) j‖ ^ 2 := by
    intro j
    have h := gs_TB B hbound (fun i => fB 1 (e i)) j
    have hw : (fun i => TB B (fB 1 (e i))) = (fun i => fB B (e i)) := by
      funext i; exact (fB_eq_TB B (e i)).symm
    rw [hw] at h
    have h3 : (K : ℝ)⁻¹ * ‖gs (fun i => fB 1 (e i)) j‖ ≤ ‖gs (fun i => fB B (e i)) j‖ := by
      rw [inv_mul_le_iff₀ hK0]; exact h
    have h4 : 0 ≤ (K : ℝ)⁻¹ * ‖gs (fun i => fB 1 (e i)) j‖ := by positivity
    calc m * ‖gs (fun i => fB 1 (e i)) j‖ ^ 2
        ≤ ((K : ℝ)⁻¹) ^ 2 * ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = ((K : ℝ)⁻¹ * ‖gs (fun i => fB 1 (e i)) j‖) ^ 2 := by ring
      _ ≤ ‖gs (fun i => fB B (e i)) j‖ ^ 2 := by gcongr
  set S := univ.filter (fun j : Fin d => j ≤ k) with hS
  have hcard : S.card ≤ d := (Finset.card_le_univ S).trans_eq (Fintype.card_fin d)
  calc m ^ d ≤ m ^ S.card := pow_le_pow_of_le_one hm0.le hm1 hcard
    _ = m ^ S.card * 1 := (mul_one _).symm
    _ ≤ m ^ S.card * ∏ j ∈ S, ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hone (by positivity)
    _ = ∏ j ∈ S, m * ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ ∏ j ∈ S, ‖gs (fun i => fB B (e i)) j‖ ^ 2 :=
        Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => hterm j)
end ReciprocityTheory.ReducedBases.T2
