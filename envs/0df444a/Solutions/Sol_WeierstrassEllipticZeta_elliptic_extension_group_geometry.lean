-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_group_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T16:17:51.546523+00:00
-- url     : https://prove2.me/submissions/e8fdbd1f-63aa-4c1b-bac2-19a217344c8a

import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Mathlib.Tactic.Abel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Data.Set.Card

open TranscendenceTheory WeierstrassEllipticZeta

noncomputable section

private lemma p2m_pullback_quotient_ncard
    {R A G : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup G] [Module R G]
    (φ : A →ₗ[R] G) (H : Submodule R G) (X : Finset A) :
    ((H.comap φ).mkQ '' (X : Set A)).ncard =
      (H.mkQ '' (φ '' (X : Set A))).ncard := by
  let f := (H.comap φ).mapQ H φ le_rfl
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    exact (Submodule.ker_mapQ _ _ _ _).trans (Submodule.mkQ_map_self _)
  have himage : f '' ((H.comap φ).mkQ '' (X : Set A)) =
      H.mkQ '' (φ '' (X : Set A)) := by
    rw [Set.image_image, Set.image_image]
    rfl
  rw [← himage, Set.ncard_image_of_injective _ hf]

private lemma p2m_graph_quotient_extension_geometry
    (R A B : Type*) [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (Λ : Submodule R A) (η : Λ →ₗ[R] B) :
    Function.Injective (extensionInclusion Λ η) ∧
    Function.Surjective (extensionProjection Λ η) ∧
    LinearMap.ker (extensionProjection Λ η) = LinearMap.range (extensionInclusion Λ η) ∧
    (extensionAdditiveProjection Λ η).comp (extensionCurve Λ η) = LinearMap.id ∧
    (extensionEllipticProjection Λ η).comp (extensionCurve Λ η) = Λ.mkQ ∧
    ∀ H : Submodule R (GraphExtensionGroup Λ η),
      (H ≤ LinearMap.ker (extensionAdditiveProjection Λ η) →
        H.comap (extensionCurve Λ η) = ⊥) ∧
      (H ≤ LinearMap.ker (extensionEllipticProjection Λ η) →
        H.comap (extensionCurve Λ η) ≤ Λ) ∧
      ∀ X : Finset A,
        ((H.comap (extensionCurve Λ η)).mkQ '' (X : Set A)).ncard =
          (H.mkQ '' (extensionCurve Λ η '' (X : Set A))).ncard := by
  have hi : Function.Injective (extensionInclusion Λ η) := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro b hb
    change b = 0
    have hmem : (0, b) ∈ extensionPeriodGraph Λ η := by
      simpa [extensionInclusion] using hb
    obtain ⟨ω, hω⟩ := hmem
    have hzero : ω = 0 := Subtype.ext (congrArg Prod.fst hω)
    simpa [hzero] using (congrArg Prod.snd hω).symm
  have hp : Function.Surjective (extensionProjection Λ η) := by
    intro x
    obtain ⟨a, rfl⟩ := Λ.mkQ_surjective x
    exact ⟨(extensionPeriodGraph Λ η).mkQ (a, 0), rfl⟩
  have hexact : LinearMap.ker (extensionProjection Λ η) =
      LinearMap.range (extensionInclusion Λ η) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨a, b⟩, rfl⟩ := (extensionPeriodGraph Λ η).mkQ_surjective x
      have ha : a ∈ Λ := by simpa [extensionProjection] using hx
      refine ⟨b + η ⟨a, ha⟩, ?_⟩
      change (extensionPeriodGraph Λ η).mkQ (0, b + η ⟨a, ha⟩) =
        (extensionPeriodGraph Λ η).mkQ (a, b)
      apply (Submodule.Quotient.eq _).mpr
      refine ⟨-⟨a, ha⟩, ?_⟩
      simp
    · rintro x ⟨b, rfl⟩
      simp [extensionProjection, extensionInclusion]
  have hfirst : (extensionAdditiveProjection Λ η).comp (extensionCurve Λ η) =
      LinearMap.id := by ext; rfl
  have hsecond : (extensionEllipticProjection Λ η).comp (extensionCurve Λ η) =
      Λ.mkQ := by ext; rfl
  refine ⟨hi, hp, hexact, hfirst, hsecond, ?_⟩
  intro H
  refine ⟨?_, ?_, fun X => p2m_pullback_quotient_ncard (extensionCurve Λ η) H X⟩
  · intro hH
    apply le_antisymm _ bot_le
    intro a ha
    have hz := hH ha
    change a = 0 at hz
    exact hz
  · intro hH a ha
    have hz := hH ha
    change Λ.mkQ a = 0 at hz
    simpa using hz


theorem solution (L : PeriodPair) :
    ∃ η : L.lattice →ₗ[ℤ] ℂ,
      (∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) ∧
      Function.Injective (extensionInclusion L.lattice η) ∧
      Function.Surjective (extensionProjection L.lattice η) ∧
      LinearMap.ker (extensionProjection L.lattice η) =
        LinearMap.range (extensionInclusion L.lattice η) ∧
      (extensionAdditiveProjection L.lattice η).comp (extensionCurve L.lattice η) =
        LinearMap.id ∧
      (extensionEllipticProjection L.lattice η).comp (extensionCurve L.lattice η) =
        L.lattice.mkQ ∧
      ∀ H : Submodule ℤ (GraphExtensionGroup L.lattice η),
        (H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η) →
          H.comap (extensionCurve L.lattice η) = ⊥) ∧
        (H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η) →
          H.comap (extensionCurve L.lattice η) ≤ L.lattice) ∧
        ∀ X : Finset ℂ,
          ((H.comap (extensionCurve L.lattice η)).mkQ '' (X : Set ℂ)).ncard =
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard := by
  let ηadd : L.lattice →+ ℂ :=
    { toFun := fun ω => zetaQuasiPeriod L ω
      map_zero' := by simp [zetaQuasiPeriod]
      map_add' := by
        intro ω ν
        have hz : L.ω₁ / 2 + (ω : ℂ) ∉ L.lattice := by
          intro h
          exact L.ω₁_div_two_notMem_lattice (by simpa using L.lattice.sub_mem h ω.property)
        have hν := weierstrassZeta_add_period L ν (L.ω₁ / 2 + ω) ν.property hz
        change zetaQuasiPeriod L ((ω : ℂ) + ν) = zetaQuasiPeriod L ω + zetaQuasiPeriod L ν
        unfold zetaQuasiPeriod
        rw [← add_assoc, hν]
        unfold zetaQuasiPeriod
        abel }
  refine ⟨ηadd.toIntLinearMap, fun _ => rfl, ?_⟩
  exact p2m_graph_quotient_extension_geometry ℤ ℂ ℂ L.lattice ηadd.toIntLinearMap
