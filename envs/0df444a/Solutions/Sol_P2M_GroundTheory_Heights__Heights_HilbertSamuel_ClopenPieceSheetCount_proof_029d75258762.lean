-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ClopenPieceSheetCount_proof_029d75258762
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:34.723503+00:00
-- url     : https://prove2.me/submissions/3de19c3d-b945-4b33-89e0-884c91ac0005

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StClopenPieceSheetCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PClopenPieceSheetCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Matrix Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace ClopenPieceSheetCount
theorem _root_.solution : ClopenPieceSheetCount.Statement := by
  intro n d N A Z Ω O F hΩo hΩc hcov hO hF hXOF

  set f : (Fin d → ℂ) → ℕ := fun y => {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.ncard with hf_def

  have hloc : ∀ y ∈ Ω, ∀ᶠ w in 𝓝 y, f w = f y := by
    intro y hy
    obtain ⟨hfin, _hcard, hsec⟩ := hcov y hy
    set S : Set (Fin n → ℂ) := {x | x ∈ Z ∧ A *ᵥ x = y} with hS
    have hsec' : ∀ x ∈ S, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          ContinuousOn g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U :=
      fun x hx => hsec x hx.1 hx.2
    choose! U V g hU hyU _hV _hxV hg hgy hAg hZV using hsec'
    have hca : ∀ x ∈ S, ContinuousAt (g x) y := fun x hx =>
      (hg x hx).continuousAt ((hU x hx).mem_nhds (hyU x hx))

    have hgZ : ∀ x ∈ S, ∀ w ∈ U x, g x w ∈ Z := by
      intro x hx w hw
      have : g x w ∈ g x '' U x := ⟨w, hw, rfl⟩
      rw [← hZV x hx] at this
      exact this.1

    have e1 : ∀ᶠ w in 𝓝 y, w ∈ Ω := hΩo.mem_nhds hy
    have e2 : ∀ᶠ w in 𝓝 y, ∀ x ∈ S, w ∈ U x :=
      (eventually_all_finite hfin).2 fun x hx => (hU x hx).mem_nhds (hyU x hx)
    have e3 : ∀ᶠ w in 𝓝 y, ∀ p ∈ S ×ˢ S, p.1 ≠ p.2 → g p.1 w ≠ g p.2 w := by
      refine (eventually_all_finite (hfin.prod hfin)).2 fun p hp => ?_
      by_cases hne : p.1 = p.2
      · exact Eventually.of_forall fun _ h => absurd hne h
      · have h := ((hca p.1 hp.1).ne_iff_eventually_ne (hca p.2 hp.2)).1
          (by rw [hgy p.1 hp.1, hgy p.2 hp.2]; exact hne)
        exact h.mono fun w hw _ => hw
    have e4 : ∀ᶠ w in 𝓝 y, ∀ x ∈ S, x ∉ O → g x w ∉ F := by
      refine (eventually_all_finite hfin).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · exact Eventually.of_forall fun _ h => absurd hxO h
      · have hxF : x ∉ F := by
          intro hxF
          have hxX : x ∈ {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} := ⟨hx.1, by rw [hx.2]; exact hy⟩
          have : x ∈ {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ O := by rw [hXOF]; exact ⟨hxX, hxF⟩
          exact hxO this.2
        have := (hca x hx).preimage_mem_nhds (hF.isOpen_compl.mem_nhds (by rw [hgy x hx]; exact hxF))
        filter_upwards [this] with w hw _ using hw
    have e5 : ∀ᶠ w in 𝓝 y, ∀ x ∈ S, x ∈ O → g x w ∈ O := by
      refine (eventually_all_finite hfin).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · have := (hca x hx).preimage_mem_nhds (hO.mem_nhds (by rw [hgy x hx]; exact hxO))
        filter_upwards [this] with w hw _ using hw
      · exact Eventually.of_forall fun _ h => absurd h hxO
    filter_upwards [e1, e2, e3, e4, e5] with w hwΩ hwU hwne hwF hwO

    set G : (Fin n → ℂ) → Fin n → ℂ := fun x => g x w with hG
    have hGinj : Set.InjOn G S := by
      intro a ha b hb hab
      by_contra hne
      exact hwne (a, b) ⟨ha, hb⟩ hne hab
    have hGmaps : G '' S ⊆ {x | x ∈ Z ∧ A *ᵥ x = w} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hgZ x hx w (hwU x hx), hAg x hx w (hwU x hx)⟩
    obtain ⟨hfinw, hcardw, _⟩ := hcov w hwΩ
    have hGeq : G '' S = {x | x ∈ Z ∧ A *ᵥ x = w} := by
      refine Set.eq_of_subset_of_ncard_le hGmaps ?_ hfinw
      rw [hGinj.ncard_image, hcardw, _hcard]

    have hT : {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w} = G '' {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y} := by
      ext z
      constructor
      · rintro ⟨hzZ, hzO, hzw⟩
        have hz : z ∈ G '' S := by rw [hGeq]; exact ⟨hzZ, hzw⟩
        obtain ⟨x, hx, rfl⟩ := hz
        refine ⟨x, ⟨hx.1, ?_, hx.2⟩, rfl⟩
        by_contra hxO
        apply hwF x hx hxO
        have hX : G x ∈ {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} := ⟨hzZ, by rw [hzw]; exact hwΩ⟩
        have : G x ∈ {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ F := by rw [← hXOF]; exact ⟨hX, hzO⟩
        exact this.2
      · rintro ⟨x, ⟨hxZ, hxO, hxy⟩, rfl⟩
        have hx : x ∈ S := ⟨hxZ, hxy⟩
        exact ⟨hgZ x hx w (hwU x hx), hwO x hx hxO, hAg x hx w (hwU x hx)⟩
    simp only [hf_def]
    have hsub : {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y} ⊆ S := fun x hx => ⟨hx.1, hx.2.2⟩
    rw [hT, (hGinj.mono hsub).ncard_image]

  have hcont : ContinuousOn f Ω := by
    intro y hy
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, nhds_discrete ℕ, tendsto_pure]
    exact hloc y hy
  rcases Ω.eq_empty_or_nonempty with hE | ⟨y₀, hy₀⟩
  · exact ⟨0, fun y hy => by rw [hE] at hy; exact absurd hy (Set.notMem_empty y)⟩
  · exact ⟨f y₀, fun y hy => hΩc.constant hcont hy hy₀⟩
end ClopenPieceSheetCount
end GroundTheory.Heights₂.Heights.HilbertSamuel
