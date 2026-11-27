-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelProjectionLocallyInjective_proof_0e4c6c01386c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:05:36.377009+00:00
-- url     : https://prove2.me/submissions/f9c586ce-dd4d-4e62-9432-5fd47d7e4e02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProjectionLocallyInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveProperClosedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProjectionLocallyInjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveProperClosedFinite_proof_19a9f160baa2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelProper_proof_63b250feae60
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_eq_graph_of_mem_zeroSetIn_acfc7619bda0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRoot_map_eval_of_mem_zeroSetIn_9b21e58aa6cf


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
open MvPolynomial Topology IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace NormalModelProjectionLocallyInjective
theorem _root_.solution : NormalModelProjectionLocallyInjective.Statement := by
  intro n J M w hJ hdim hw
  choose a b hbJ hab using M.birational
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  have hBJ : B ∉ J := fun h => by
    have := hJ
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hbJ i hi

  set S : Set (Fin n → ℂ) := ComplexSets.zeroSet J ∩ ComplexSets.zeroSet (Ideal.span {B}) with hS
  have hSfin : S.Finite := CurveProperClosedFinite.proof n J _ hJ hdim
    (fun h => hBJ (h (Ideal.subset_span rfl)))

  choose P hPm hP using M.integral
  set F : Set (Fin n ⊕ Fin M.m → ℂ) := {z | z ∈ zeroSetIn M.ideal ∧ firstCoords z ∈ S} with hF
  have hFfin : F.Finite := by
    have hT : (⋃ x ∈ S, ({x} : Set (Fin n → ℂ)) ×ˢ
        Set.pi Set.univ (fun i => {y : ℂ | ((P i).map (eval x)).IsRoot y})).Finite :=
      hSfin.biUnion fun x _ => (Set.finite_singleton x).prod
        (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map (eval x)).ne_zero)
    refine (hT.image fun p => Sum.elim p.1 p.2).subset ?_
    intro z hz
    refine ⟨(firstCoords z, fun i => z (Sum.inr i)), ?_, ?_⟩
    · refine Set.mem_biUnion hz.2 ⟨rfl, fun i _ => ?_⟩
      exact isRoot_map_eval_of_mem_zeroSetIn hz.1 i (P i) (hP i)
    · funext s
      rcases s with j | i <;> rfl
  refine ⟨(F \ {w})ᶜ, (hFfin.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds
    (fun h => h.2 rfl), ?_⟩

  have hnear : ∀ z ∈ zeroSetIn M.ideal ∩ (F \ {w})ᶜ, (∃ i, eval (firstCoords z) (b i) = 0) → z = w := by
    rintro z ⟨hz, hzU⟩ ⟨i, hi⟩
    have hxJ : firstCoords z ∈ ComplexSets.zeroSet J := fun q hq => by
      rw [← M.comap_eq, Ideal.mem_comap] at hq
      have h := hz _ hq
      rw [eval_rename] at h
      exact h
    have hxB : firstCoords z ∈ ComplexSets.zeroSet (Ideal.span {B}) := fun q hq => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hq
      rw [eval_mul, hB, map_prod, Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
    by_contra hne
    exact hzU ⟨⟨hz, hxJ, hxB⟩, hne⟩
  intro z hz z' hz' hzz
  by_cases hbz : ∀ i, eval (firstCoords z) (b i) ≠ 0
  · have hbz' : ∀ i, eval (firstCoords z') (b i) ≠ 0 := hzz ▸ hbz
    rw [M.eq_graph_of_mem_zeroSetIn a b hab z hz.1 hbz, M.eq_graph_of_mem_zeroSetIn a b hab z' hz'.1 hbz', hzz]
  · simp only [not_forall, not_not] at hbz
    have hbz' : ∃ i, eval (firstCoords z') (b i) = 0 := hzz ▸ hbz
    rw [hnear z hz hbz, hnear z' hz' hbz']
end NormalModelProjectionLocallyInjective
end GroundTheory.Heights₂.Heights
