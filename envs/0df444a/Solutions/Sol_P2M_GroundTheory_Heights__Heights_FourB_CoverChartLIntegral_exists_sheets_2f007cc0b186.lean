-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_sheets_2f007cc0b186
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:49:13.950871+00:00
-- url     : https://prove2.me/submissions/5ab86b6d-c71e-4358-bfd3-df56d73a7733

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
theorem _root_.solution {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)} {d : ℕ}
    (hM : IsOpen M₀) (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ)
    (hcov : IsCoveringMap hmaps.restrict) (hfib : ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d)
    (z : Fin e → ℂ) (hz : z ∉ Δ) :
    ∃ U : Set (Fin e → ℂ), IsOpen U ∧ z ∈ U ∧ U ⊆ Δᶜ ∧ ∃ W : Fin d → Set X,
      (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ M₀) ∧ Pairwise (Function.onFun Disjoint W) ∧
      (∀ x ∈ M₀, q x ∈ U → ∃ i, x ∈ W i) ∧ ∀ i, Set.BijOn q (W i) U := by
  set f := hmaps.restrict with hf
  set I := f ⁻¹' {(⟨z, hz⟩ : (Δᶜ : Set (Fin e → ℂ)))} with hI
  obtain ⟨hdisc, U', hzU', hU'o, hfU'o, H, hH⟩ := hcov ⟨z, hz⟩
  have himg : Subtype.val '' I = M₀ ∩ q ⁻¹' {z} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_⟩
      have hp' : f p = ⟨z, hz⟩ := hp
      show q p = z
      exact congrArg Subtype.val hp'
    · rintro ⟨hx, hqx⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hqx, rfl⟩
  have hIe : I.encard = d := by
    rw [← Subtype.val_injective.encard_image, himg, hfib z hz]
  have : Finite I := (Set.finite_of_encard_eq_coe hIe).to_subtype
  have hcard : Nat.card I = d := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hIe]; rfl
  let eI : Fin d ≃ I := ((Finite.equivFin I).trans (finCongr hcard)).symm
  have hqH : ∀ p : f ⁻¹' U', q ((p : M₀) : X) = (H p).1.1.1 := fun p => by
    rw [hH p]; rfl
  let W : Fin d → Set X := fun i =>
    Subtype.val '' (Subtype.val '' {p : f ⁻¹' U' | (H p).2 = eI i} : Set M₀)
  have hmemW : ∀ i x, x ∈ W i ↔ ∃ p : f ⁻¹' U', (H p).2 = eI i ∧ ((p : M₀) : X) = x := by
    intro i x
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  refine ⟨Subtype.val '' U', hΔ.isOpen_compl.isOpenMap_subtype_val _ hU'o, ⟨_, hzU', rfl⟩,
    fun u ⟨u', _, hu⟩ => hu ▸ u'.2, W, fun i => ?_, fun i x hx => ?_, fun i k hik => ?_,
    fun x hx hqx => ?_, fun i => ⟨fun x hx => ?_, fun x hx x' hx' hxx => ?_, fun u hu => ?_⟩⟩
  · have hS : IsOpen {p : f ⁻¹' U' | (H p).2 = eI i} :=
      (isOpen_discrete {eI i}).preimage (continuous_snd.comp H.continuous)
    exact hM.isOpenMap_subtype_val _ (hfU'o.isOpenMap_subtype_val _ hS)
  · obtain ⟨p, -, rfl⟩ := (hmemW i x).1 hx
    exact (p : M₀).2
  · refine Set.disjoint_left.2 fun x hx hx' => hik ?_
    obtain ⟨p, hp, rfl⟩ := (hmemW i x).1 hx
    obtain ⟨p', hp', hpp⟩ := (hmemW k _).1 hx'
    have : p' = p := Subtype.val_injective (Subtype.val_injective hpp)
    rw [this, hp] at hp'
    exact eI.injective hp'
  · obtain ⟨u', hu', hu⟩ := hqx
    have hfx : f ⟨x, hx⟩ = u' := Subtype.ext hu.symm
    let p : f ⁻¹' U' := ⟨⟨x, hx⟩, show f ⟨x, hx⟩ ∈ U' by rw [hfx]; exact hu'⟩
    refine ⟨eI.symm (H p).2, (hmemW _ x).2 ⟨p, ?_, rfl⟩⟩
    exact (eI.apply_symm_apply _).symm
  · obtain ⟨p, -, rfl⟩ := (hmemW i x).1 hx
    rw [hqH p]
    exact ⟨(H p).1.1, (H p).1.2, rfl⟩
  · obtain ⟨p, hp, rfl⟩ := (hmemW i x).1 hx
    obtain ⟨p', hp', rfl⟩ := (hmemW i x').1 hx'
    rw [hqH p, hqH p'] at hxx
    have h1 : (H p).1 = (H p').1 := Subtype.val_injective (Subtype.val_injective hxx)
    have h2 : H p = H p' := Prod.ext h1 (hp.trans hp'.symm)
    rw [H.injective h2]
  · obtain ⟨u', hu', rfl⟩ := hu
    let p : f ⁻¹' U' := H.symm (⟨u', hu'⟩, eI i)
    have hHp : H p = (⟨u', hu'⟩, eI i) := H.apply_symm_apply _
    refine ⟨((p : M₀) : X), (hmemW i _).2 ⟨p, by rw [hHp], rfl⟩, ?_⟩
    rw [hqH p, hHp]
end GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
