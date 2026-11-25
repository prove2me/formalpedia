-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RegularLocusDense_proof_ee86a3a1f765
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:05.236806+00:00
-- url     : https://prove2.me/submissions/b6c5c888-b143-43bf-a916-57f73922a815

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_conormal_zero_85fd5e0d4c9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_maxRank_equations_f246dd7c3832

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
open Topology Filter Module
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace RegularLocusDense
theorem _root_.solution (hIFT : AnalyticImplicitChart.Statement) : RegularLocusDense.Statement := by
  intro σ _ X w hX
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N, hNo, hwN, fun B hBo hBN x hx => ?_⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  have hU : IsOpen (interior t ∩ B) := isOpen_interior.inter hBo
  obtain ⟨a, haY, ι, hι, h, W, hWo, haW, hWU, hha, hhY, hli, hspan⟩ :=
    exists_maxRank_equations (X ∩ B) hU ⟨x, hx, mem_interior_iff_mem_nhds.2 ht, hx.2⟩
  obtain ⟨d, A, O, V, g, -, hOo, hVo, haV, hVW, hg, hAg, hVO⟩ :=
    hIFT σ ι h a W (fun j => hha j a haW) (fun j => hhY j a haW haY) hli (hWo.mem_nhds haW)

  have hgV : ∀ y ∈ O, g y ∈ V ∧ ∀ j, h j (g y) = 0 := fun y hy =>
    (show g y ∈ {z | z ∈ V ∧ ∀ j, h j z = 0} from hVO ▸ Set.mem_image_of_mem g hy)
  have hYV : ∀ z ∈ X ∩ B, z ∈ V → g (A z) = z ∧ A z ∈ O := by
    intro z hzY hzV
    have hz : z ∈ g '' O := hVO ▸ (⟨hzV, fun j => hhY j z (hVW hzV) hzY⟩ : z ∈ {z | z ∈ V ∧ ∀ j, h j z = 0})
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hAg y hy]
    exact ⟨rfl, hy⟩
  obtain ⟨hga, hy₀O⟩ := hYV a haY haV

  have hAD : ∀ y ∈ O, A.comp (fderiv ℂ g y) = ContinuousLinearMap.id ℂ _ := by
    intro y hy
    have h3 : HasFDerivAt (fun y => A (g y)) (A.comp (fderiv ℂ g y)) y :=
      A.hasFDerivAt.comp y (hg y hy).differentiableAt.hasFDerivAt
    have h4 : HasFDerivAt (fun y => A (g y)) (ContinuousLinearMap.id ℂ (Fin d → ℂ)) y :=
      (hasFDerivAt_id y).congr_of_eventuallyEq (by filter_upwards [hOo.mem_nhds hy] with u hu using hAg u hu)
    exact h3.unique h4
  have hhD : ∀ y ∈ O, ∀ j, (fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y) = 0 := by
    intro y hy j
    have h3 : HasFDerivAt (fun y => h j (g y)) ((fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y)) y :=
      (hha j (g y) (hVW (hgV y hy).1)).differentiableAt.hasFDerivAt.comp y
        (hg y hy).differentiableAt.hasFDerivAt
    have h4 : HasFDerivAt (fun y => h j (g y)) (0 : (Fin d → ℂ) →L[ℂ] ℂ) y :=
      (hasFDerivAt_const 0 y).congr_of_eventuallyEq
        (by filter_upwards [hOo.mem_nhds hy] with u hu using (hgV u hu).2 j)
    exact h3.unique h4

  have hC : ∀ c ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} ∩ O, ∀ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ c →
      (∀ᶠ u in 𝓝 c, u ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} → ψ u = 0) → fderiv ℂ ψ c = 0 := by
    rintro c ⟨⟨hcO, hcY⟩, -⟩ ψ hψ hψC
    have hzV := (hgV c hcO).1
    have hAz : A (g c) = c := hAg c hcO
    have hψ' : AnalyticAt ℂ ψ (A (g c)) := by rw [hAz]; exact hψ
    have hH : AnalyticAt ℂ (fun u => ψ (A u)) (g c) := hψ'.comp (A.analyticAt (g c))
    have hHY : ∀ᶠ u in 𝓝 (g c), u ∈ X ∩ B → ψ (A u) = 0 := by
      have hAt : Tendsto A (𝓝 (g c)) (𝓝 c) := by
        have h0 := A.continuous.tendsto (g c)
        rwa [hAz] at h0
      filter_upwards [hVo.mem_nhds hzV, hAt hψC] with u huV huψ huY
      obtain ⟨hgu, huO⟩ := hYV u huY huV
      exact huψ ⟨huO, hgu.symm ▸ huY⟩
    have hmem := hspan (g c) ⟨hVW hzV, hcY⟩ _ hH hHY
    have hchain : fderiv ℂ (fun u => ψ (A u)) (g c) = (fderiv ℂ ψ c).comp A := by
      have hψd : HasFDerivAt ψ (fderiv ℂ ψ c) (A (g c)) := by
        rw [hAz]; exact hψ.differentiableAt.hasFDerivAt
      exact (hψd.comp (g c) A.hasFDerivAt).fderiv
    have hkill : ∀ ℓ ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) (g c)),
        ℓ.comp (fderiv ℂ g c) = 0 := by
      intro ℓ hℓ
      induction hℓ using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hhD c hcO j
      | zero => simp
      | add x y _ _ hx hy => rw [ContinuousLinearMap.add_comp, hx, hy, add_zero]
      | smul r x _ hx =>
        rw [ContinuousLinearMap.smul_comp, hx]
        ext v
        simp
    have hk := hkill _ hmem
    rw [hchain, ContinuousLinearMap.comp_assoc, hAD c hcO, ContinuousLinearMap.comp_id] at hk
    exact hk

  have hvan : ∀ i, ∀ᶠ y in 𝓝 (A a), f i (g y) = 0 := by
    intro i
    refine eventually_zero_of_conormal_zero (C := {y | y ∈ O ∧ g y ∈ X ∩ B})
      ⟨hy₀O, hga.symm ▸ haY⟩ (hOo.mem_nhds hy₀O) hC ?_ ?_
    · have hfa : AnalyticAt ℂ (f i) (g (A a)) := hga.symm ▸ hf i a (hBN haY.2)
      exact hfa.comp (hg (A a) hy₀O)
    · refine Eventually.of_forall fun y hy => ?_
      have hgy : g y ∈ X ∩ N := ⟨hy.2.1, hBN hy.2.2⟩
      rw [hXN] at hgy
      exact hgy.2 i
  obtain ⟨O', hO'P, hO'o, hy₀O'⟩ :=
    eventually_nhds_iff.1 ((eventually_all.2 hvan).and (hOo.mem_nhds hy₀O))
  refine ⟨a, interior_subset (hWU haW).1, haY, d, A, O', V ∩ A ⁻¹' O', g, hO'o,
    hVo.inter (hO'o.preimage A.continuous), ⟨haV, hy₀O'⟩, hg.mono fun y hy => (hO'P y hy).2,
    fun y hy => hAg y (hO'P y hy).2, ?_⟩
  ext z
  constructor
  · rintro ⟨hzY, hzV, hzO'⟩
    exact ⟨A z, hzO', (hYV z hzY hzV).1⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hf0, hyO⟩ := hO'P y hy
    have hgyV := (hgV y hyO).1
    have hgB : g y ∈ B := (hWU (hVW hgyV)).2
    have hgX : g y ∈ X := by
      have hz : g y ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN hgB, hf0⟩
      rw [← hXN] at hz
      exact hz.1
    refine ⟨⟨hgX, hgB⟩, hgyV, ?_⟩
    show A (g y) ∈ O'
    rw [hAg y hyO]
    exact hy
end RegularLocusDense
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
