-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongMassNearSmall_proof_987004547669
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:17.515802+00:00
-- url     : https://prove2.me/submissions/38272cce-22b2-475c-abc1-ef17c8a1095b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CutOffNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceImmersiveGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongMassNearSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_dim_component_linForm_8c41886dbd0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_cutoff_near_zeroSet_710ba7aa020d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_sup_linForm_39b08eae98d4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
namespace LelongMassNearSmall
theorem _root_.solution (hReg : RegMassNearSmall.Statement)
    (hVar : VarMassNearSmall.Statement) : LelongMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ _ hIdim hf hfc δ hδ
  set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS
  have hSfin : S.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  set M : ℝ := ∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun W _ => Nat.cast_nonneg _
  have hδ' : 0 < δ / (M + 1) := by positivity
  obtain ⟨U₀, hU₀, hIU₀, hT⟩ := hReg n d J I u φ f hJ hdim hu hφ hIdim hf.continuous hfc δ hδ
  have hW : ∀ W ∈ S, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
      ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
        |varInt W d (fun x => χ x * f x) φ| ≤ δ / (M + 1) := by
    intro W hWm
    obtain ⟨hWp, hWJ, -⟩ := mem_minimalPrimes_sup_linForm hWm
    refine hVar n d W I φ f hWp
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hJ hdim hu hWm)
      (fun i => ?_) hIdim hf.continuous hfc _ hδ'
    obtain ⟨U, hU, hSU, hC⟩ := hφ i
    exact ⟨U, hU, hWJ.trans hSU, hC⟩
  choose! UW hUW hIUW hLW using hW
  have hU : IsOpen (U₀ ∩ ⋂ W ∈ S, UW W) :=
    hU₀.inter (hSfin.isOpen_biInter fun W hW => hUW W hW)
  have hIU : zeroSet I ⊆ U₀ ∩ ⋂ W ∈ S, UW W :=
    Set.subset_inter hIU₀ (Set.subset_iInter₂ fun W hW => hIUW W hW)
  obtain ⟨χ, hχ, hχ01, hχU, V, hV, hIV, hχ1⟩ := exists_cutoff_near_zeroSet I hU hIU
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩
  refine ⟨χ, hχ, ⟨V, hV, hIV, hχ1⟩, ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact hT χ hχ.continuous hχb (hχU.trans Set.inter_subset_left) ε ⟨hε.1, hε.2.le⟩
  · rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
    calc |∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) *
            varInt W d (fun x => χ x * f x) φ|
        ≤ ∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * (δ / (M + 1)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun W hW => ?_)
          have hWS : W ∈ S := hSfin.mem_toFinset.1 hW
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hLW W hWS χ hχ.continuous hχb
            (hχU.trans (Set.inter_subset_right.trans (Set.biInter_subset_of_mem hWS))))
            (Nat.cast_nonneg _)
      _ = M * (δ / (M + 1)) := by rw [← Finset.sum_mul]
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith
end LelongMassNearSmall
end GroundTheory.Heights₂.Heights
