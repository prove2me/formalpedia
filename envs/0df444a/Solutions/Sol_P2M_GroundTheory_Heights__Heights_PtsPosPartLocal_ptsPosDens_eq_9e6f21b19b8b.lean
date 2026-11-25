-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_ptsPosDens_eq_9e6f21b19b8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:50.515715+00:00
-- url     : https://prove2.me/submissions/6e1450fa-aa65-4042-9856-a5cdbe234454

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_of_eq_9866b3b330bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_of_eq_97f246a53542
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_apply_eq_of_segre_eq_0b2426e6d1f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_sheetDensity_eq_f776bfe0d7d4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
namespace GroundTheory.Heights₂.Heights.PtsPosPartLocal
theorem _root_.solution {P : Ideal (MRing ι)} {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z)
    {E : Set ((Σ k, ι k) → ℂ)}
    (hE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z p) ∈ E ↔ z ∈ E))
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {U : Set (Fin e → ℂ)}
    {N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hU : IsOpen U)
    (hγ : ∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (hN : IsOpen N) (hNp : ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)))
    (hEN : ∀ z' ∈ E, Ψ (segre z') 0 ≠ 0 → (crd Ψ (segre z'), nrm Ψ (segre z')) ∈ N)
    (y : Fin e → ℂ) :
    ptsPosDens P Ψ (pot L) (E.indicator g) y = (U ∩ γ ⁻¹' E).indicator
      (fun y => max (g (γ y) * maDensity (fun j y' => pot L j (γ y')) y) 0) y := by
  classical
  have hEg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      E.indicator g (fun p => c p.1 * z p) = E.indicator g z := by
    intro c z hc
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hE c z hc).2 hz), hg c z hc]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hE c z hc).1 h))]
  have hmemE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      ((fun p => c p.1 * z p) ∈ E) = (z ∈ E) := fun c z hc => propext (hE c z hc)

  have hnz : ∀ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (E.indicator g) y w ≠ 0 →
      (y, w) ∈ N ∧ γ y ∈ E := by
    intro w hw hne
    obtain ⟨-, -, -, hΨw⟩ := hw
    unfold sheetDensity at hne
    split_ifs at hne with h
    · have hc := h.choose_spec
      have hcE : h.choose y ∈ E := by
        by_contra hn
        exact hne (by rw [Set.indicator_of_notMem hn, zero_mul])
      have hw0 : Ψ (segre (h.choose y)) 0 ≠ 0 := by
        rw [hc.1, hΨw]; simp
      have hqN := hEN _ hcE hw0
      rw [hc.1, crd_of_eq hΨw, nrm_of_eq hΨw] at hqN
      refine ⟨hqN, ?_⟩
      obtain ⟨hyU, hw1⟩ := hNp _ hqN
      have hseg : segre (h.choose y) = segre (γ y) := hc.1.trans (hw1 ⟨h.choose y, hc.2.self_of_nhds.2.1, hc.1, hΨw⟩)
      have := apply_eq_of_segre_eq hmemE hc.2.self_of_nhds.2.1.1 hseg
      rw [this]
      exact hcE
    · exact absurd rfl hne
  unfold ptsPosDens
  by_cases hy : y ∈ U ∩ γ ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    have hyU := hy.1
    have hΨ1 : Ψ (segre (γ y)) = Fin.cons 1 y := (hγ y hyU).2.2
    have hfib : segre (γ y) ∈ fibre P Ψ y := ⟨γ y, (hγ y hyU).2.1, rfl, hΨ1⟩
    have hqN : (y, segre (γ y)) ∈ N := by
      have h := hEN _ hy.2 (by rw [hΨ1]; simp)
      rwa [crd_of_eq hΨ1, nrm_of_eq hΨ1] at h
    rw [finsum_eq_single _ (segre (γ y)) ?_, finsum_eq_if, if_pos hfib,
      sheetDensity_eq hL hEg hU hγ hN hNp hqN hfib, Set.indicator_of_mem (show γ y ∈ E from hy.2)]
    intro w hne
    rw [finsum_eq_if]
    split_ifs with hw
    · by_cases h0 : sheetDensity P Ψ (pot L) (E.indicator g) y w = 0
      · rw [h0, max_self]
      · exact absurd ((hNp _ (hnz w hw h0).1).2 hw) hne
    · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    by_cases h0 : sheetDensity P Ψ (pot L) (E.indicator g) y w = 0
    · rw [h0, max_self]
    · obtain ⟨hqN, hγE⟩ := hnz w hw h0
      exact absurd ⟨(hNp _ hqN).1, hγE⟩ hy
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
