-- Prove2me | solution 1 for Paper.Hypergraph.cutoff_from_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:44.782815+00:00
-- url     : https://prove2.me/submissions/d32d4aa2-2c9a-4b05-8b89-a87aed6fb2ab

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_RoundingCutoff
import Theorems.Thm_Paper_Hypergraph_cutoff_good_annulus
import Theorems.Thm_Paper_Hypergraph_component_cutoffPiece
import Theorems.Thm_Paper_Hypergraph_annulus_fractionalSeparator
import Theorems.Thm_Paper_Hypergraph_coverCost_induce_restrictDemand
import Theorems.Thm_Paper_Hypergraph_coverCost_smul
import Theorems.Thm_Paper_Hypergraph_cutoff_layer_parameters
import Theorems.Thm_Paper_Hypergraph_edgeVolume_mono
import Theorems.Thm_Paper_Hypergraph_fractionalSeparator_congr
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj
import Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_mono
import Theorems.Thm_Paper_Hypergraph_roundingBall_mono
import Theorems.Thm_Paper_Hypergraph_roundingBall_volume_le
import Theorems.Thm_Paper_Hypergraph_separatorRegion_closed
import Theorems.Thm_Paper_Hypergraph_separatorRegion_disjoint_terminals
import Theorems.Thm_Paper_Hypergraph_separatorRegion_subset
import Theorems.Thm_Paper_Hypergraph_terminals_subset_separatorRegion
import Theorems.Thm_Paper_Hypergraph_vertexDistance_self_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ x : ℕ → ℝ} {φ r C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (hr : 0 < r ∧ r < 1) (hC : 0 ≤ C) (hK : r / 2 ≤ H.coverCost x)
    {Q : Finset ℕ} (hQ : Q ⊆ H.vertices) (hne : Q.Nonempty)
    (hsmall : ∀ v ∈ Q, x v < (r / (9 + 2 * Real.logb 2 (H.coverCost x / r))) / 2)
    (hround : ∀ (A B : Finset ℕ) (z : ℕ → ℝ),
      A ⊆ (H.induce Q).vertices → B ⊆ (H.induce Q).vertices →
      (H.induce Q).FractionalSeparator A B z →
      (∀ v ∈ (H.induce Q).vertices, z v ≠ 0 → x v ≠ 0) →
      ∃ S ⊆ (H.induce Q).vertices.filter (fun v => z v ≠ 0),
        (H.induce Q).IntegralSeparator A B S ∧
        H.setCoverCost S ≤ C * (H.induce Q).coverCost z) :
    Nonempty (H.CutoffPiece γ x Q (φ / (1 - r) * ∑ e ∈ H.edges, γ e)
      (C * ((18 + 4 * Real.logb 2 (H.coverCost x / r)) / r))) := by
  let δ := r / (9 + 2 * Real.logb 2 (H.coverCost x / r))
  obtain ⟨c, hc⟩ := hne
  obtain ⟨vmax, hvmax, hmax⟩ := Q.exists_max_image x ⟨c, hc⟩
  let q := x vmax
  have hq0 : 0 ≤ q := (hx.1 vmax (hQ hvmax)).1
  have hq : ∀ v ∈ H.vertices ∩ Q, x v ≤ q := fun v hv => hmax v (mem_inter.mp hv).2
  have hqsmall : q < δ / 2 := hsmall vmax hvmax
  have hδ : 0 < δ := by linarith
  have hgap : 0 < δ - q := by linarith
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  have hcJ : c ∈ (H.induce Q).vertices := mem_inter.mpr ⟨hQ hc, hc⟩
  have hcoef : (18 + 4 * Real.logb 2 (H.coverCost x / r)) / r = 2 / δ := by
    dsimp [δ]
    field_simp
    ring
  have hcoef0 : 0 ≤ C * ((18 + 4 * Real.logb 2 (H.coverCost x / r)) / r) := by
    rw [hcoef]
    positivity
  by_cases hout : ∃ v, (H.induce Q).primal.Reachable c v ∧
      r / 4 < (H.induce Q).vertexDistance x c v
  swap
  · apply H.component_cutoffPiece hγ hx hr.2 hcoef0 hQ hc
    intro v hv
    have hle : (H.induce Q).vertexDistance x c v ≤ r / 4 :=
      le_of_not_gt fun h => hout ⟨v, hv, h⟩
    linarith [hr.1]
  obtain ⟨s, hs, hsrad, hcost⟩ := H.cutoff_good_annulus hn Q hcJ hr.1 hK hq0 hq hqsmall hout
  let J := H.induce Q
  let a := s + δ / 2
  let b := s + 3 * δ / 2
  let A := H.roundingBall x Q c a
  let B := J.vertices \ H.roundingBall x Q c b
  let T := H.roundingBall x Q c b \ A
  let z := (δ - q)⁻¹ • restrictDemand x T
  have hA : A ⊆ J.vertices := filter_subset _ _
  have hB : B ⊆ J.vertices := sdiff_subset
  have hTQ : T ⊆ Q := fun v hv => (mem_inter.mp (mem_filter.mp (mem_sdiff.mp hv).1).1).2
  have hzexpr : ∀ v ∈ J.vertices, z v =
      if a < J.vertexDistance x c v ∧ J.vertexDistance x c v ≤ b then x v / (δ - q) else 0 := by
    intro v hv
    change v ∈ H.vertices ∩ Q at hv
    dsimp only [J]
    simp only [z, Pi.smul_apply, smul_eq_mul, restrictDemand, T, A, roundingBall,
      mem_sdiff, mem_filter, hv, true_and, not_le]
    split_ifs <;> simp_all [div_eq_mul_inv, mul_comm]
  have hzfrac : J.FractionalSeparator A B z := by
    have hf := J.annulus_fractionalSeparator (fun v hv => hn v (mem_inter.mp hv).1) hcJ hq
      (show q < (b - a) / 2 by dsimp [a, b]; linarith) hq0
    dsimp only at hf
    have hBexpr : J.vertices.filter (fun v => b < J.vertexDistance x c v) = B := by
      ext v
      simp only [B, roundingBall, mem_filter, mem_sdiff]
      change (v ∈ J.vertices ∧ b < J.vertexDistance x c v) ↔
        v ∈ J.vertices ∧ ¬ (v ∈ J.vertices ∧ J.vertexDistance x c v ≤ b)
      simp only [not_and, not_le]
      tauto
    rw [hBexpr] at hf
    apply J.fractionalSeparator_congr hA hf
    intro v hv
    rw [hzexpr v hv]
    have heq : b - a - q = δ - q := by dsimp [a, b]; ring
    rw [heq]
  have hzsupp : ∀ v ∈ J.vertices, z v ≠ 0 → x v ≠ 0 := by
    intro v hv hz hzero
    exact hz (by simp [z, restrictDemand, hzero])
  obtain ⟨S, hS, hsep, hScost⟩ := hround A B z hA hB hzfrac hzsupp
  have hST : S ⊆ T := by
    intro v hv
    have hne := (mem_filter.mp (hS hv)).2
    by_contra ht
    exact hne (by simp [z, restrictDemand, ht])
  have hSQ : S ⊆ Q := hST.trans hTQ
  have hSsupp : S ⊆ H.vertices.filter (fun v => x v ≠ 0) := by
    intro v hv
    exact mem_filter.mpr ⟨hQ (hSQ hv), hzsupp v (mem_filter.mp (hS hv)).1 (mem_filter.mp (hS hv)).2⟩
  have hAS : Disjoint A S := by
    apply disjoint_left.mpr
    intro v hvA hvS
    exact (mem_sdiff.mp (hST hvS)).2 hvA
  let P := J.separatorRegion A S
  have hPV : P ⊆ J.vertices \ S := J.separatorRegion_subset A S
  have hPQ : P ⊆ Q := fun v hv => (mem_inter.mp (mem_sdiff.mp (hPV hv)).1).2
  have hAP : A ⊆ P := by
    intro v hv
    exact J.terminals_subset_separatorRegion hA (mem_sdiff.mpr ⟨hv, fun hvS => disjoint_left.mp hAS hv hvS⟩)
  have hPB : P ⊆ H.roundingBall x Q c b := by
    intro v hv
    by_contra hnot
    exact disjoint_left.mp (J.separatorRegion_disjoint_terminals hsep) hv
      (mem_sdiff.mpr ⟨(mem_sdiff.mp (hPV hv)).1, hnot⟩)
  have hbaseP : H.roundingBall x Q c s ⊆ P :=
    (H.roundingBall_mono x Q c (show s ≤ a by dsimp [a]; linarith)).trans hAP
  have hcbase : c ∈ H.roundingBall x Q c s := by
    apply mem_filter.mpr ⟨hcJ, ?_⟩
    apply (J.vertexDistance_self_le (fun v hv => hn v (mem_inter.mp hv).1) hcJ).trans
    have hseednum := cutoff_layer_parameters hr.1 hK
    obtain ⟨N, hN, hrad, hbudget, hseed⟩ := hseednum
    have hqbound := hseed q hqsmall
    have hxc := hq c hcJ
    linarith [hr.1]
  have hzQ : restrictDemand z Q = z := by
    funext v
    by_cases hvQ : v ∈ Q
    · simp [restrictDemand, hvQ]
    · have hnot : v ∉ T := fun h => hvQ (hTQ h)
      simp [restrictDemand, hvQ, z, hnot]
  have hzCost : J.coverCost z = (δ - q)⁻¹ * H.coverCost (restrictDemand x T) := by
    rw [H.coverCost_induce_restrictDemand z Q, hzQ]
    exact H.coverCost_smul _ (inv_pos.mpr hgap)
  have hcostP : H.setCoverCost S ≤ C * (2 / δ) * H.coverCost (restrictDemand x P) := by
    rw [hzCost] at hScost
    have hinv : (δ - q)⁻¹ ≤ 2 / δ := by
      rw [inv_eq_one_div]
      exact (div_le_div_iff₀ hgap hδ).2 (by linarith)
    have hcost' : H.coverCost (restrictDemand x T) ≤ H.coverCost
        (restrictDemand x (H.roundingBall x Q c s)) := hcost
    have hTP := hcost'.trans (H.restrictDemand_cost_mono hn hbaseP)
    apply hScost.trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hC
    exact mul_le_mul hinv hTP (H.coverCost_nonneg _) (by positivity)
  refine ⟨{
    piece := P
    separator := S
    nonempty := ⟨c, hbaseP hcbase⟩
    piece_subset := hPQ
    separator_subset := hSQ
    disjoint := disjoint_left.mpr (fun v hv hvS => (mem_sdiff.mp (hPV hv)).2 hvS)
    support := hSsupp
    separated := ?_
    volume_le := (H.edgeVolume_mono hγ
      (hPB.trans (H.roundingBall_mono x Q c hsrad))).trans
      (H.roundingBall_volume_le hγ hx Q hcJ hr.2)
    cost_le := by simpa only [hcoef] using hcostP }⟩
  · intro e he
    by_contra hnsep
    obtain ⟨hu, hv⟩ := not_or.mp hnsep
    obtain ⟨u, hue, huP⟩ := not_disjoint_iff.mp hu
    obtain ⟨v, hve, hvR⟩ := not_disjoint_iff.mp hv
    have hv := mem_sdiff.mp hvR
    have hnP : v ∉ P := fun h => hv.2 (mem_union_left _ h)
    have hnS : v ∉ S := fun h => hv.2 (mem_union_right _ h)
    have huv : u ≠ v := by intro h; subst v; exact hnP huP
    have hadj := (H.primal_induce_adj Q (hPQ huP) hv.1).mpr ⟨huv, e, he, hue, hve⟩
    exact hnP (J.separatorRegion_closed A S huP
      (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hQ hv.1, hv.1⟩, hnS⟩) hadj)
end Paper.Hypergraph
