-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.mass_eq_of_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:33.201034+00:00
-- url     : https://prove2.me/submissions/4cbabcb3-d727-40e8-8ac0-09cbe2814d72

import Definitions.Def_Formalism_PeriodIntegrals_UJClassMass
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Reduce
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Abstract
variable {G : Type*} [Group G] (Γ Kf : Subgroup G)
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (L0 : Submodule (𝓞 K) V)
variable {Γ Kf h L0}
private lemma gmap_mul_lemma (a b : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    gmap (a * b) L = gmap a (gmap b L) := by
  first
  | (simp only [Formalism.HermitianLatticesTheory.gmap]; rw [← Submodule.map_comp]; rfl)
  | (ext x; simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map])
private lemma gmap_one_unitary_class_mass (L : Submodule (𝓞 K) V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  first
  | (simp only [Formalism.HermitianLatticesTheory.gmap]; exact Submodule.map_id L)
  | (ext x; simp [Formalism.HermitianLatticesTheory.gmap])
private lemma gmap_inv_gmap_unitary_class_mass (g : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) : gmap g⁻¹ (gmap g L) = L := by
  rw [← gmap_mul_lemma, inv_mul_cancel, gmap_one_unitary_class_mass]
private lemma mul_mul_inv_mem_autL_gmap {g a : V ≃ₗ[K] V} {N : Submodule (𝓞 K) V} (hg : g ∈ isom h)
    (ha : a ∈ autL h N) : g * a * g⁻¹ ∈ autL h (gmap g N) := by
  have ⟨ha1, ha2⟩ : a ∈ isom h ∧ gmap a N = N := ha
  show g * a * g⁻¹ ∈ isom h ∧ gmap (g * a * g⁻¹) (gmap g N) = gmap g N
  exact ⟨mul_mem (mul_mem hg ha1) (inv_mem hg), by rw [gmap_mul_lemma, gmap_mul_lemma, gmap_inv_gmap_unitary_class_mass, ha2]⟩
private lemma inv_mul_mul_mem_autL {g b : V ≃ₗ[K] V} {N : Submodule (𝓞 K) V} (hg : g ∈ isom h)
    (hb : b ∈ autL h (gmap g N)) : g⁻¹ * b * g ∈ autL h N := by
  have ⟨hb1, hb2⟩ : b ∈ isom h ∧ gmap b (gmap g N) = gmap g N := hb
  show g⁻¹ * b * g ∈ isom h ∧ gmap (g⁻¹ * b * g) N = N
  exact ⟨mul_mem (mul_mem (inv_mem hg) hb1) hg, by rw [gmap_mul_lemma, gmap_mul_lemma, hb2, gmap_inv_gmap_unitary_class_mass]⟩
private lemma natCard_autL_gmap {g : V ≃ₗ[K] V} (hg : g ∈ isom h) (N : Submodule (𝓞 K) V) :
    Nat.card (autL h (gmap g N)) = Nat.card (autL h N) :=
  Nat.card_congr
    { toFun := fun b => ⟨g⁻¹ * b.1 * g, inv_mul_mul_mem_autL hg b.2⟩
      invFun := fun a => ⟨g * a.1 * g⁻¹, mul_mul_inv_mem_autL_gmap hg a.2⟩
      left_inv := fun b => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }
private lemma sum_inv_card_autL_eq_of_isClassReps {s t : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L0 s)
    (ht : IsClassReps h L0 t) :
    ∑ N ∈ s, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ = ∑ N ∈ t, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ := by
  classical
  have hs' : (∀ M ∈ s, M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ s ∧ ∃ u ∈ isom h, gmap u N = M := hs
  have ht' : (∀ M ∈ t, M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ t ∧ ∃ u ∈ isom h, gmap u N = M := ht
  have hex : ∀ N ∈ s, ∃ P, P ∈ t ∧ ∃ u ∈ isom h, gmap u P = N :=
    fun N hN => (ht'.2 N (hs'.1 N hN)).exists
  refine Finset.sum_bij (fun N hN => (hex N hN).choose) (fun N hN => (hex N hN).choose_spec.1)
    ?_ ?_ ?_
  · intro N₁ h₁ N₂ h₂ heq
    obtain ⟨u₁, hu₁, e₁⟩ := (hex N₁ h₁).choose_spec.2
    obtain ⟨u₂, hu₂, e₂⟩ := (hex N₂ h₂).choose_spec.2
    rw [heq] at e₁
    have key : gmap (u₂ * u₁⁻¹) N₁ = N₂ := by rw [gmap_mul_lemma, ← e₁, gmap_inv_gmap_unitary_class_mass, e₂]
    exact (hs'.2 N₂ (hs'.1 N₂ h₂)).unique ⟨h₁, _, mul_mem hu₂ (inv_mem hu₁), key⟩
      ⟨h₂, 1, one_mem _, gmap_one_unitary_class_mass N₂⟩
  · intro P hP
    obtain ⟨N, ⟨hN, u, hu, e⟩, -⟩ := hs'.2 P (ht'.1 P hP)
    refine ⟨N, hN, ?_⟩
    obtain ⟨v, hv, e'⟩ := (hex N hN).choose_spec.2
    have key : gmap (u * v) (hex N hN).choose = P := by rw [gmap_mul_lemma, e', e]
    exact (ht'.2 P (ht'.1 P hP)).unique ⟨(hex N hN).choose_spec.1, _, mul_mem hu hv, key⟩
      ⟨hP, 1, one_mem _, gmap_one_unitary_class_mass P⟩
  · intro N hN
    obtain ⟨v, hv, e'⟩ := (hex N hN).choose_spec.2
    have hc := natCard_autL_gmap hv (hex N hN).choose
    rw [e'] at hc
    rw [hc]
end Abstract
end PI.UnitaryGroupMassFormula.UJClassMass
end
end

set_option autoImplicit false
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {G : Type*} [Group G] (Γ Kf : Subgroup G)
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (L0 : Submodule (𝓞 K) V)
variable {Γ Kf h L0}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {s : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L0 s) :
    mass h L0 = ∑ N ∈ s, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ t, IsClassReps h L0 t := ⟨s, hs⟩
  rw [Formalism.HermitianLatticesTheory.mass, dif_pos hex]
  exact sum_inv_card_autL_eq_of_isClassReps hex.choose_spec hs
end PI.UnitaryGroupMassFormula.UJClassMass
