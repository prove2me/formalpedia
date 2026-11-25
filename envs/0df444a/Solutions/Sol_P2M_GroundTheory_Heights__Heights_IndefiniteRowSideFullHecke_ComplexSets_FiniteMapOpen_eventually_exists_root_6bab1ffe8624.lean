-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_eventually_exists_root_6bab1ffe8624
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:32:19.433896+00:00
-- url     : https://prove2.me/submissions/423c0d80-103f-4dd5-8713-61ed151cace7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_continuous_evalYT_eb4576ed961d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
theorem _root_.solution {d : ℕ} {F : Polynomial (MvPolynomial (Fin d) ℂ)} (hF : F.Monic)
    {y₀ : Fin d → ℂ} {t₀ : ℂ} (h₀ : evalYT F y₀ t₀ = 0) {V : Set ℂ} (hV : V ∈ 𝓝 t₀) :
    ∀ᶠ y in 𝓝 y₀, ∃ t ∈ V, evalYT F y t = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hcont := (continuous_evalYT F t₀).tendsto y₀
  rw [h₀] at hcont
  have hsmall : ∀ᶠ y in 𝓝 y₀, ‖evalYT F y t₀‖ < ε ^ F.natDegree :=
    (tendsto_norm_zero.comp hcont) (Iio_mem_nhds (pow_pos hε _))
  filter_upwards [hsmall] with y hy
  set G := F.map (MvPolynomial.eval y) with hG
  have hGm : G.Monic := hF.map _
  have hGdeg : G.natDegree = F.natDegree := hF.natDegree_map _
  have hsplit : G.Splits := IsAlgClosed.splits G
  by_contra! hfar
  have hle : ∀ r ∈ G.roots, ε ≤ ‖t₀ - r‖ := by
    intro r hr
    have hr0 : G.eval r = 0 := (Polynomial.mem_roots hGm.ne_zero).1 hr
    by_contra! hlt
    refine hfar r (hball ?_) hr0
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    exact hlt
  have hprod : ‖G.eval t₀‖ = (G.roots.map fun r => ‖t₀ - r‖).prod := by
    rw [hsplit.eval_eq_prod_roots_of_monic hGm]
    exact (G.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun r : ℂ => t₀ - r)).symm
  have hge : ε ^ F.natDegree ≤ ‖G.eval t₀‖ := by
    have := Multiset.prod_map_le_prod_map₀ (fun _ => ε) (fun r => ‖t₀ - r‖)
      (fun _ _ => hε.le) hle
    rw [Multiset.map_const', Multiset.prod_replicate] at this
    rw [hprod, ← hGdeg, hsplit.natDegree_eq_card_roots]
    exact this
  exact absurd hy (not_lt.2 hge)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
