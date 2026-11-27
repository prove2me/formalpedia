-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperOpenProjectionLocalUnbranched_proof_505328ddd7e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:18.005988+00:00
-- url     : https://prove2.me/submissions/c79f8a49-4826-4058-91ab-46f53c7c26a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionLocalUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreLocalUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperOpenProjectionLocalUnbranched
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_forall_ne_zero_of_isOpen_fc98376a5123

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
open Topology Metric Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ProperOpenProjectionLocalUnbranched
theorem _root_.solution (hFin : CompactHolomorphicFibreFinite.Statement)
    (hLoc : IsolatedFibreLocalUnbranched.Statement) : ProperOpenProjectionLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A D hB hf hXB hD hAD hprop hopen y₀ hy₀
  have zerosX : ∀ z, z ∈ X ∩ B → ∀ i, f i z = 0 := fun z hz => by
    rw [hXB] at hz
    exact hz.2
  have memX : ∀ z, z ∈ B → (∀ i, f i z = 0) → z ∈ X ∩ B := fun z hz h0 => by
    rw [hXB]
    exact ⟨hz, h0⟩

  set F := {x | x ∈ X ∩ B ∧ A x = y₀} with hF
  have hFc : IsCompact F := by
    have := hprop {y₀} (Set.singleton_subset_iff.2 hy₀) isCompact_singleton
    simpa only [Set.mem_singleton_iff] using this

  set n := Fintype.card σ
  let L : (σ → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) (Fintype.equivFin σ)
  set U₀ : Set (Fin n → ℂ) := L.symm ⁻¹' B with hU₀
  set Φ : (Fin n → ℂ) → Fin (k + d) → ℂ :=
    fun v => Fin.append (fun i => f i (L.symm v)) (A (L.symm v)) with hΦ
  set yv : Fin (k + d) → ℂ := Fin.append (0 : Fin k → ℂ) y₀ with hyv
  have hU₀o : IsOpen U₀ := hB.preimage L.symm.continuous
  have hΦd : DifferentiableOn ℂ Φ U₀ := by
    refine differentiableOn_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [hΦ, Fin.append_left]
      exact (hf i).differentiableOn.comp L.symm.differentiable.differentiableOn (fun v hv => hv)
    · simp only [hΦ, Fin.append_right]
      exact ((differentiable_apply (𝕜 := ℂ) j).comp
        (A.differentiable.comp L.symm.differentiable)).differentiableOn
  have hfib : {v | v ∈ U₀ ∧ Φ v = yv} = L.symm ⁻¹' F := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hU₀, hF, hΦ, hyv]
    constructor
    · rintro ⟨hv, he⟩
      refine ⟨memX _ hv fun i => ?_, ?_⟩
      · simpa using congrFun he (Fin.castAdd d i)
      · funext j
        simpa using congrFun he (Fin.natAdd k j)
    · rintro ⟨hv, hA⟩
      refine ⟨hv.2, funext fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [zerosX _ hv i]
      · simp [hA]
  have hfibc : IsCompact {v | v ∈ U₀ ∧ Φ v = yv} := by
    rw [hfib, ← L.image_eq_preimage_symm]
    exact hFc.image L.continuous
  have hFfin : F.Finite := by
    have h1 := (hFin n (k + d) U₀ Φ yv hU₀o hΦd hfibc).image L.symm
    rwa [hfib, Set.image_preimage_eq _ L.symm.surjective] at h1

  have hloc : ∀ x ∈ F, ∃ (M : Set (σ → ℂ)) (g : (Fin d → ℂ) → ℂ), IsOpen M ∧ x ∈ M ∧
      AnalyticAt ℂ g y₀ ∧ (¬ ∀ᶠ t in 𝓝 y₀, g t = 0) ∧
      ∀ z ∈ X ∩ B ∩ M, g (A z) ≠ 0 →
        ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O := by
    intro x hx
    have hiso : ∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ B ∩ W, A x' = A x → x' = x := by
      refine ⟨(F \ {x})ᶜ, hFfin.sdiff.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl, ?_⟩
      rintro x' ⟨hx'XB, hx'W⟩ hx'A
      by_contra hne
      exact hx'W ⟨⟨hx'XB, hx'A.trans hx.2⟩, hne⟩
    obtain ⟨M, g, hM, hg, hg0, hsec⟩ := hLoc σ X B k f d A hB hf hXB hopen x hx.1 hiso
    rw [hx.2] at hg hg0
    exact ⟨interior M, g, isOpen_interior, mem_interior_iff_mem_nhds.2 hM, hg, hg0,
      fun z hz => hsec z ⟨hz.1, interior_subset hz.2⟩⟩
  choose! M g hMo hxM hga hgne hsec using hloc
  set s := hFfin.toFinset with hs
  have hsF : ∀ x, x ∈ s ↔ x ∈ F := fun x => hFfin.mem_toFinset

  obtain ⟨r₀, hr₀, hr₀D⟩ := nhds_basis_closedBall.mem_iff.1 (hD.mem_nhds hy₀)
  set Mall := ⋃ x ∈ F, M x with hMall
  have hMallo : IsOpen Mall := isOpen_biUnion fun x hx => hMo x hx
  set C := {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ r₀} \ Mall with hC
  have hCc : IsCompact C := (hprop _ hr₀D (isCompact_closedBall y₀ r₀)).diff hMallo
  have hAC : y₀ ∉ A '' C := by
    rintro ⟨c, ⟨⟨hcXB, -⟩, hcM⟩, hcA⟩
    exact hcM (Set.mem_biUnion (show c ∈ F from ⟨hcXB, hcA⟩) (hxM c ⟨hcXB, hcA⟩))
  have hev : ∀ᶠ t in 𝓝 y₀, t ∈ ball y₀ r₀ ∧ t ∉ A '' C ∧ ∀ x ∈ s, AnalyticAt ℂ (g x) t := by
    refine (show ∀ᶠ t in 𝓝 y₀, t ∈ ball y₀ r₀ from ball_mem_nhds y₀ hr₀).and
      ((show ∀ᶠ t in 𝓝 y₀, t ∉ A '' C from
        ((hCc.image A.continuous).isClosed.isOpen_compl).mem_nhds hAC).and ?_)
    exact (Filter.eventually_all_finset s).2 fun x hx => (hga x ((hsF x).1 hx)).eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hgan : ∀ x ∈ s, AnalyticOnNhd ℂ (g x) (ball y₀ r) := fun x hx t ht => (hball t ht).2.2 x hx
  refine ⟨ball y₀ r, fun t => ∏ x ∈ s, g x t, isOpen_ball, mem_ball_self hr, ?_,
    Finset.analyticOnNhd_fun_prod s hgan, ?_, ?_⟩
  · intro t ht
    exact hr₀D (ball_subset_closedBall (hball t ht).1)
  · intro W hWo hWU hW
    have hne : ∀ x ∈ s, ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ ball y₀ r → W.Nonempty →
        ∃ t ∈ W, g x t ≠ 0 := by
      intro x hx W hWo hWU hW
      by_contra hcon
      push Not at hcon
      obtain ⟨t, htW⟩ := hW
      have hzt : g x =ᶠ[𝓝 t] 0 := by
        filter_upwards [hWo.mem_nhds htW] with u hu using hcon u hu
      have hEq := (hgan x hx).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball y₀ r).isPreconnected (hWU htW) hzt
      exact hgne x ((hsF x).1 hx) (by
        filter_upwards [ball_mem_nhds y₀ hr] with u hu using hEq hu)
    obtain ⟨t, htW, ht⟩ := exists_forall_ne_zero_of_isOpen s g (ball y₀ r)
      (fun x hx => (hgan x hx).continuousOn) hne W hWo hWU hW
    exact ⟨t, htW, Finset.prod_ne_zero_iff.2 ht⟩
  · intro y hyU hgy x' hx'XB hx'A
    have hx'M : x' ∈ Mall := by
      by_contra hn
      refine (hball y hyU).2.1 ⟨x', ⟨⟨hx'XB, ?_⟩, hn⟩, hx'A⟩
      rw [hx'A]
      exact ball_subset_closedBall (hball y hyU).1
    obtain ⟨x, hxF, hx'x⟩ := Set.mem_iUnion₂.1 hx'M
    have hgx : g x (A x') ≠ 0 := by
      rw [hx'A]
      exact Finset.prod_ne_zero_iff.1 hgy x ((hsF x).2 hxF)
    exact hsec x hxF x' ⟨hx'XB, hx'x⟩ hgx
end ProperOpenProjectionLocalUnbranched
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
