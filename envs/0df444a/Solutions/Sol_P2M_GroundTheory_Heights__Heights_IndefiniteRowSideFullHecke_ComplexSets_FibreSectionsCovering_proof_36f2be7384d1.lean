-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreSectionsCovering_proof_36f2be7384d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:40.225985+00:00
-- url     : https://prove2.me/submissions/dd3452e6-a9d3-4fd3-980c-6293a31ac420

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreSectionsCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreSectionsCovering

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
open Filter Topology Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FibreSectionsCovering
theorem _root_.solution : FibreSectionsCovering.Statement := by
  intro n e N A Ω X hX hfib hsec
  let f : X → Ω := Set.MapsTo.restrict _ X Ω hX
  show IsCoveringMap f
  have hAc : Continuous (fun x : Fin n → ℂ => A *ᵥ x) :=
    (Matrix.mulVecLin A).continuous_of_finiteDimensional
  choose O V' g hO hAO hV' hxV' hg hgx hAg hXV' using hsec

  have key : ∀ x₀ (h₀ : x₀ ∈ X) x, x ∈ X → x ∈ V' x₀ h₀ → g x₀ h₀ (A *ᵥ x) = x := by
    intro x₀ h₀ x hx hxv
    have hx' : x ∈ g x₀ h₀ '' O x₀ h₀ := hXV' x₀ h₀ ▸ ⟨hx, hxv⟩
    obtain ⟨o, ho, rfl⟩ := hx'
    rw [hAg x₀ h₀ o ho]

  have inX : ∀ x₀ (h₀ : x₀ ∈ X) w, w ∈ O x₀ h₀ → g x₀ h₀ w ∈ X ∧ g x₀ h₀ w ∈ V' x₀ h₀ := by
    intro x₀ h₀ w hw
    have h : g x₀ h₀ w ∈ X ∩ V' x₀ h₀ := hXV' x₀ h₀ ▸ ⟨w, hw, rfl⟩
    exact h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have : IsEmpty X := by
      refine ⟨fun x => ?_⟩
      have h := hfib _ (hX x.2)
      rw [hN, Nat.cast_zero, Set.encard_eq_zero] at h
      have hm : (x : Fin n → ℂ) ∈ {x' | x' ∈ X ∧ A *ᵥ x' = A *ᵥ (x : Fin n → ℂ)} := ⟨x.2, rfl⟩
      rw [h] at hm
      exact hm
    exact IsCoveringMap.of_isEmpty _
  intro y

  have hFenc : {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)}.encard = N := hfib y y.2
  have hFfin := Set.finite_of_encard_eq_coe hFenc
  have := hFfin.to_subtype
  have hFcard : Nat.card {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)} = N := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hFenc]
    rfl
  let eq := (Finite.equivFinOfCardEq hFcard).symm
  let pt : Fin N → Fin n → ℂ := fun i => (eq i : Fin n → ℂ)
  have pt_mem : ∀ i, pt i ∈ X ∧ A *ᵥ pt i = y := fun i => (eq i).2
  have pt_inj : Function.Injective pt := fun i j h => eq.injective (Subtype.ext h)
  let G : Fin N → (Fin (e + 1) → ℂ) → Fin n → ℂ := fun i => g (pt i) (pt_mem i).1
  let OO : Fin N → Set (Fin (e + 1) → ℂ) := fun i => O (pt i) (pt_mem i).1
  let VV : Fin N → Set (Fin n → ℂ) := fun i => V' (pt i) (pt_mem i).1
  have hGy : ∀ i, G i y = pt i := fun i => by
    rw [← (pt_mem i).2]
    exact hgx (pt i) (pt_mem i).1
  have hOy : ∀ i, OO i ∈ 𝓝 (y : Fin (e + 1) → ℂ) := fun i =>
    (hO _ _).mem_nhds (by have h : A *ᵥ pt i ∈ OO i := hAO _ _; rwa [(pt_mem i).2] at h)
  have hGc : ∀ i, ∀ w ∈ OO i, ContinuousAt (G i) w := fun i w hw =>
    (hg _ _).continuousOn.continuousAt ((hO _ _).mem_nhds hw)
  have hS : ∀ᶠ w in 𝓝 (y : Fin (e + 1) → ℂ), (∀ i, w ∈ OO i) ∧ ∀ i j, i ≠ j → G i w ≠ G j w := by
    refine (Filter.eventually_all.2 hOy).and
      (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_)
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · have hne : G i y ≠ G j y := by
        rw [hGy, hGy]
        exact fun h => hij (pt_inj h)
      exact (((hGc i y (mem_of_mem_nhds (hOy i))).ne_iff_eventually_ne
        (hGc j y (mem_of_mem_nhds (hOy j)))).1 hne).mono fun _ hw _ => hw
  obtain ⟨W, hWS, hWo, hyW⟩ := mem_nhds_iff.1 hS
  have hWO : ∀ i, ∀ w ∈ W, w ∈ OO i := fun i w hw => (hWS hw).1 i
  have hWd : ∀ w ∈ W, ∀ i j, i ≠ j → G i w ≠ G j w := fun w hw => (hWS hw).2
  have hGX : ∀ i, ∀ w ∈ W, G i w ∈ X := fun i w hw => (inX _ _ w (hWO i w hw)).1
  have hGV : ∀ i, ∀ w ∈ W, G i w ∈ VV i := fun i w hw => (inX _ _ w (hWO i w hw)).2
  have hAG : ∀ i, ∀ w ∈ W, A *ᵥ G i w = w := fun i w hw => hAg _ _ w (hWO i w hw)
  have hfc : Continuous f := (hAc.comp continuous_subtype_val).subtype_mk fun x => hX x.2
  have hres : ∀ i (q : Ω) (hq : (q : Fin (e + 1) → ℂ) ∈ W),
      f ⟨G i q, hGX i q hq⟩ = q := fun i q hq =>
    Subtype.ext (hAG i q hq)
  let V : Set Ω := {p | (p : Fin (e + 1) → ℂ) ∈ W}
  let U : Fin N → Set X := fun i => {x | (x : Fin n → ℂ) ∈ VV i ∧ A *ᵥ (x : Fin n → ℂ) ∈ W}
  have hVo : IsOpen V := continuous_subtype_val.isOpen_preimage _ hWo
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    continuous_subtype_val.isOpen_preimage _ ((hV' _ _).inter (hWo.preimage hAc))

  have hUG : ∀ i (x : X), x ∈ U i → G i (A *ᵥ (x : Fin n → ℂ)) = x := fun i x hx =>
    key _ _ _ x.2 hx.1
  have open_iff : ∀ i {W' : Set Ω}, W' ⊆ V → (IsOpen W' ↔ IsOpen (f ⁻¹' W' ∩ U i)) := by
    intro i W' hW'V
    refine ⟨fun h => (hfc.isOpen_preimage _ h).inter (hUo i), fun h => ?_⟩
    obtain ⟨T', hT'o, hT'eq⟩ := isOpen_induced_iff.1 h
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpW : (p : Fin (e + 1) → ℂ) ∈ W := hW'V hp
    have hGp : G i p ∈ T' := by
      have hm : (⟨G i p, hGX i p hpW⟩ : X) ∈ f ⁻¹' W' ∩ U i := by
        refine ⟨?_, hGV i p hpW, ?_⟩
        · show f ⟨G i p, hGX i p hpW⟩ ∈ W'
          rw [hres i p hpW]
          exact hp
        · show A *ᵥ G i p ∈ W
          rw [hAG i p hpW]
          exact hpW
      rw [← hT'eq] at hm
      exact hm
    rw [mem_nhds_subtype]
    refine ⟨W ∩ G i ⁻¹' T', Filter.inter_mem (hWo.mem_nhds hpW)
      ((hGc i p (hWO i p hpW)).preimage_mem_nhds (hT'o.mem_nhds hGp)), ?_⟩
    rintro q ⟨hqW, hqT⟩
    have hm : (⟨G i q, hGX i q hqW⟩ : X) ∈ Subtype.val ⁻¹' T' := hqT
    rw [hT'eq] at hm
    have h1 := hm.1
    rw [Set.mem_preimage, hres i q hqW] at h1
    exact h1
  have inj : ∀ i, (U i).InjOn f := by
    intro i x hx x' hx' hxx'
    have h : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (x' : Fin n → ℂ) := congrArg Subtype.val hxx'
    apply Subtype.ext
    rw [← hUG i x hx, ← hUG i x' hx', h]
  have surj : ∀ i, (U i).SurjOn f V := by
    intro i p hp
    refine ⟨⟨G i p, hGX i p hp⟩, ⟨hGV i p hp, ?_⟩, hres i p hp⟩
    show A *ᵥ G i p ∈ W
    rw [hAG i p hp]
    exact hp
  have disj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj => ?_
    exact hWd _ hxi.2 i j hij ((hUG i x hxi).trans (hUG j x hxj).symm)
  have exh : f ⁻¹' V ⊆ ⋃ i, U i := by
    intro x hx
    have hxW : A *ᵥ (x : Fin n → ℂ) ∈ W := hx
    set w := A *ᵥ (x : Fin n → ℂ) with hw
    have hwΩ : w ∈ Ω := hX x.2
    have hFw := hfib w hwΩ
    have hsub : Set.range (fun i => G i w) ⊆ {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      rintro _ ⟨i, rfl⟩
      exact ⟨hGX i w hxW, hAG i w hxW⟩
    have hinj : Function.Injective (fun i => G i w) := by
      intro i j h
      by_contra hij
      exact hWd w hxW i j hij h
    have heq : Set.range (fun i => G i w) = {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      refine ((Set.finite_of_encard_eq_coe hFw).subset hsub).eq_of_subset_of_encard_le hsub ?_
      rw [hFw]
      refine le_trans ?_ hinj.encard_range
      simp
    have hxmem : (x : Fin n → ℂ) ∈ Set.range (fun i => G i w) := by
      rw [heq]
      exact ⟨x.2, rfl⟩
    obtain ⟨i, hi⟩ := hxmem
    refine Set.mem_iUnion.2 ⟨i, ?_, hxW⟩
    show (x : Fin n → ℂ) ∈ VV i
    rw [← hi]
    exact hGV i w hxW
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Ω → X) := ⟨fun _ => ⟨pt ⟨0, hN⟩, (pt_mem _).1⟩⟩
  let T := IsOpen.trivializationDiscrete (f := f) U V hVo open_iff inj surj disj exh
  have hyT : y ∈ T.baseSet := hyW
  exact (IsEvenlyCovered.of_trivialization hyT).to_isEvenlyCovered_preimage
end FibreSectionsCovering
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
