-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.sum_eq_mass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:29.463476+00:00
-- url     : https://prove2.me/submissions/3b3b9668-bb6d-4110-8db3-f529cb123fc8

import Definitions.Def_Formalism_PeriodIntegrals_UJClassMass
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Reduce
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mass_eq_of_reps
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
theorem _root_.solution {Λ : G → Submodule (𝓞 K) V} {ι : Γ → V ≃ₗ[K] V} (D : IsDict Γ Kf h L0 Λ ι)
    (n : ℕ) (g : Fin n → G)
    (hcov : ∀ x, ∃ i, ∃ γ : Γ, ∃ k : Kf, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : Kf), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) :
    ∑ i, ((Nat.card (PI.UJClassMass.stab Γ Kf (g i)) : ℝ))⁻¹ = mass h L0 := by
  classical
  have hR : ∀ i j (u : V ≃ₗ[K] V), u ∈ isom h → gmap u (Λ (g j)) = Λ (g i) → i = j := by
    intro i j u hu huj
    obtain ⟨γ, k, hk⟩ := D.inj (g i) (g j) u hu huj
    exact hdisj i j 1 γ 1 k (by simpa using hk)
  have hinj : Function.Injective (fun i => Λ (g i)) := fun i j hij =>
    hR i j 1 (one_mem _) (by rw [gmap_one_unitary_class_mass]; exact hij.symm)
  have hs : IsClassReps h L0 (Finset.univ.image (fun i => Λ (g i))) := by
    show (∀ M ∈ Finset.univ.image (fun i => Λ (g i)), M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ Finset.univ.image (fun i => Λ (g i)) ∧ ∃ u ∈ isom h, gmap u N = M
    refine ⟨?_, ?_⟩
    · intro M hM
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hM
      rw [← hi]
      exact D.mem _
    · intro M hM
      obtain ⟨x, rfl⟩ := D.surj M hM
      obtain ⟨i, γ, k, rfl⟩ := hcov x
      refine ⟨Λ (g i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), ι γ, D.isIsom γ,
        (D.equiv (g i) γ k).symm⟩, ?_⟩
      rintro N ⟨hN, u, hu, huN⟩
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hN
      have hj' : Λ (g j) = N := hj
      subst hj'
      rw [D.equiv] at huN
      have key : gmap ((ι γ)⁻¹ * u) (Λ (g j)) = Λ (g i) := by
        rw [gmap_mul_lemma, huN, gmap_inv_gmap_unitary_class_mass]
      obtain rfl := hR i j _ (mul_mem (inv_mem (D.isIsom γ)) hu) key
      rfl
  rw [mass_eq_of_reps hs, Finset.sum_image (by intro i _ j _ hij; exact hinj hij)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.card]
end PI.UnitaryGroupMassFormula.UJClassMass
