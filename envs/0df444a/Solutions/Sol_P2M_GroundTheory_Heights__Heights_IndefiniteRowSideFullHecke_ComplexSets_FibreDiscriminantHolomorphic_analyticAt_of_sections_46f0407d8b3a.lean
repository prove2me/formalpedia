-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_analyticAt_of_sections_46f0407d8b3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:15.724856+00:00
-- url     : https://prove2.me/submissions/310f5122-33d9-4f6c-ab0e-e7bf5036d120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_enum_8b9a428901b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_fibreDiscr_eq_pairProd_4d8cdf3a1f36

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
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
theorem _root_.solution {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (hD : IsOpen D)
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) {y₀ : Fin d → ℂ} (hy₀ : y₀ ∈ D)
    (hN : {x | x ∈ Y ∧ A x = y₀}.encard = N)
    (hsec : ∀ x ∈ Y, A x = y₀ → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧ Y ∩ V = h '' O) :
    AnalyticAt ℂ (fibreDiscr Y A l N) y₀ := by
  obtain ⟨p, hp, hrange⟩ := exists_enum hN
  have hpY : ∀ i, p i ∈ Y ∧ A (p i) = y₀ := fun i => by
    have : p i ∈ range p := mem_range_self i
    rw [hrange] at this
    exact this
  choose O V h hO hV hpV hh hAh hYV using fun i => hsec (p i) (hpY i).1 (hpY i).2
  have hyO : ∀ i, y₀ ∈ O i ∧ h i y₀ = p i := by
    intro i
    have : p i ∈ h i '' O i := by
      rw [← hYV i]
      exact ⟨(hpY i).1, hpV i⟩
    obtain ⟨o, ho, hoe⟩ := this
    have hoy : o = y₀ := by rw [← hAh i o ho, hoe, (hpY i).2]
    subst hoy
    exact ⟨ho, hoe⟩
  have hne : ∀ᶠ y in 𝓝 y₀, ∀ q : Fin N × Fin N, q.1 ≠ q.2 → h q.1 y ≠ h q.2 y := by
    rw [Filter.eventually_all]
    intro q
    by_cases hq : q.1 = q.2
    · exact Filter.Eventually.of_forall fun _ h' => absurd hq h'
    · have hc : ContinuousAt (fun y => h q.1 y - h q.2 y) y₀ :=
        (hh q.1 y₀ (hyO q.1).1).continuousAt.sub (hh q.2 y₀ (hyO q.2).1).continuousAt
      have h0 : h q.1 y₀ - h q.2 y₀ ≠ 0 := by
        rw [(hyO _).2, (hyO _).2, sub_ne_zero]
        exact fun e => hq (hp e)
      exact (hc.eventually_ne h0).mono fun y hy _ => sub_ne_zero.1 hy
  have hOev : ∀ᶠ y in 𝓝 y₀, ∀ i, y ∈ O i :=
    Filter.eventually_all.2 fun i => (hO i).mem_nhds (hyO i).1
  have heq : (fun y => pairProd l (fun i => h i y)) =ᶠ[𝓝 y₀] fibreDiscr Y A l N := by
    filter_upwards [hne, hOev, hD.mem_nhds hy₀] with y hy hyO' hyD
    refine (fibreDiscr_eq_pairProd l (hle y hyD) (fun i j hij => ?_) (fun i => ⟨?_, hAh i y (hyO' i)⟩)).symm
    · by_contra hne'
      exact hy (i, j) hne' hij
    · have : h i y ∈ Y ∩ V i := by
        rw [hYV i]
        exact mem_image_of_mem _ (hyO' i)
      exact this.1
  refine AnalyticAt.congr ?_ heq
  unfold pairProd
  apply Finset.analyticAt_fun_prod
  intro q _
  exact ((l.analyticAt _).comp (hh q.1 y₀ (hyO q.1).1)).sub ((l.analyticAt _).comp (hh q.2 y₀ (hyO q.2).1))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
