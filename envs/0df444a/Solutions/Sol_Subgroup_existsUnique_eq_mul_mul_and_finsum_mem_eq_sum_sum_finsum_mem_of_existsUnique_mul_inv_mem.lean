-- Prove2me | solution 1 for Subgroup.existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/04abdd42-1c42-5b8b-95af-ceeffd583ce4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem

set_option autoImplicit false

theorem solution
    {G : Type*} [CommGroup G] (μ F A H : Subgroup G) (hμ : (μ : Set G).Finite)
    (hμF : ∀ ζ ∈ μ, ζ ∈ F → ζ = 1) (hμA : μ ≤ A)
    (hA : ∀ u ∈ A, ∃ ζ ∈ μ, ∃ φ ∈ F, u = ζ * φ)
    (hHF : H ≤ F) (hHA : H ≤ A)
    {m : ℕ} (c : Fin m → G) (hcF : ∀ j, c j ∈ F) (hcA : ∀ j, c j ∈ A)
    (hclass : ∀ φ ∈ F, φ ∈ A → ∃! j : Fin m, φ * (c j)⁻¹ ∈ H) :
    (∀ u ∈ A, ∃! p : μ × Fin m × H, u = (p.1 : G) * c p.2.1 * (p.2.2 : G)) ∧
    ∀ {M : Type*} [AddCommMonoid M] (g : G → M), ((A : Set G) ∩ Function.support g).Finite →
      ∑ᶠ u ∈ (A : Set G), g u = ∑ ζ ∈ hμ.toFinset, ∑ j : Fin m, ∑ᶠ h ∈ (H : Set G), g (ζ * c j * h) := by
  classical

  have hA' : ∀ u ∈ A, ∃ ζ ∈ μ, ∃ φ ∈ F, φ ∈ A ∧ u = ζ * φ := by
    intro u hu
    obtain ⟨ζ, hζ, φ, hφ, rfl⟩ := hA u hu
    refine ⟨ζ, hζ, φ, hφ, ?_, rfl⟩
    have : ζ⁻¹ * (ζ * φ) ∈ A := A.mul_mem (A.inv_mem (hμA hζ)) hu
    simpa using this

  have hexu : ∀ u ∈ A, ∃! p : μ × Fin m × H, u = (p.1 : G) * c p.2.1 * (p.2.2 : G) := by
    intro u hu
    obtain ⟨ζ, hζ, φ, hφF, hφA, rfl⟩ := hA' u hu
    obtain ⟨j, hj, hjuniq⟩ := hclass φ hφF hφA
    refine ⟨(⟨ζ, hζ⟩, j, ⟨φ * (c j)⁻¹, hj⟩), ?_, ?_⟩
    · simp only
      simp [mul_comm, mul_left_comm, mul_assoc]
    · rintro ⟨⟨ζ', hζ'⟩, j', ⟨h', hh'⟩⟩ hEq
      simp only at hEq

      have hφ'F : c j' * h' ∈ F := F.mul_mem (hcF j') (hHF hh')
      have hq : ζ'⁻¹ * ζ = c j' * h' * φ⁻¹ := by
        have : ζ * φ = ζ' * (c j' * h') := by rw [hEq]; simp [mul_assoc]
        calc ζ'⁻¹ * ζ = ζ'⁻¹ * (ζ * φ) * φ⁻¹ := by group
          _ = ζ'⁻¹ * (ζ' * (c j' * h')) * φ⁻¹ := by rw [this]
          _ = c j' * h' * φ⁻¹ := by group
      have hone : ζ'⁻¹ * ζ = 1 :=
        hμF _ (μ.mul_mem (μ.inv_mem hζ') hζ) (hq ▸ F.mul_mem hφ'F (F.inv_mem hφF))
      have hζeq : ζ' = ζ := by
        have := congrArg (ζ' * ·) hone
        simp only [mul_inv_cancel_left, mul_one] at this
        exact this.symm
      have hφeq : φ = c j' * h' := by
        have h2 : c j' * h' * φ⁻¹ = 1 := hq ▸ hone
        have := congrArg (· * φ) h2
        simpa using this.symm
      have hj' : φ * (c j')⁻¹ ∈ H := by
        rw [hφeq]; simpa [mul_comm, mul_assoc] using hh'
      have hjj : j' = j := hjuniq j' hj'
      subst hjj
      ext
      · exact hζeq
      · rfl
      · show h' = φ * (c j')⁻¹
        rw [hφeq]; simp [mul_comm]
  refine ⟨hexu, ?_⟩
  intro M _ g hg

  let e : μ × Fin m × H → G := fun p => (p.1 : G) * c p.2.1 * (p.2.2 : G)
  have he_bij : Set.BijOn e Set.univ (A : Set G) := by
    refine ⟨fun p _ => ?_, ?_, ?_⟩
    · exact A.mul_mem (A.mul_mem (hμA p.1.2) (hcA _)) (hHA p.2.2.2)
    · rintro p - q - hpq
      obtain ⟨r, -, hr⟩ := hexu (e p) (A.mul_mem (A.mul_mem (hμA p.1.2) (hcA _)) (hHA p.2.2.2))
      exact (hr p rfl).trans (hr q hpq).symm
    · intro u hu
      obtain ⟨p, hp, -⟩ := hexu u hu
      exact ⟨p, Set.mem_univ _, hp.symm⟩
  have h1 : ∑ᶠ u ∈ (A : Set G), g u = ∑ᶠ p : μ × Fin m × H, (g ∘ e) p := by
    rw [← finsum_mem_univ (fun p => (g ∘ e) p)]
    exact (finsum_mem_eq_of_bijOn (s := Set.univ) (t := (A : Set G)) (f := fun p => (g ∘ e) p) (g := g)
      e he_bij fun p _ => rfl).symm
  have hfs : Function.HasFiniteSupport (g ∘ e) := by
    show (Function.support (g ∘ e)).Finite
    rw [Function.support_comp_eq_preimage]
    have : e ⁻¹' Function.support g = e ⁻¹' ((A : Set G) ∩ Function.support g) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_inter_iff, iff_and_self]
      intro _
      exact he_bij.1 (Set.mem_univ p)
    rw [this]
    exact hg.preimage (he_bij.2.1.mono (Set.subset_univ _))
  rw [h1, finsum_curry₃ _ hfs]

  rw [show (∑ᶠ ζ : μ, ∑ᶠ (j : Fin m) (h : H), (g ∘ e) (ζ, j, h)) =
      ∑ᶠ ζ ∈ (μ : Set G), ∑ j : Fin m, ∑ᶠ h ∈ (H : Set G), g (ζ * c j * h) from ?_]
  · exact finsum_mem_eq_finite_toFinset_sum _ hμ
  rw [← finsum_set_coe_eq_finsum_mem]
  refine finsum_congr fun ζ => ?_
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← finsum_set_coe_eq_finsum_mem]
  rfl

end S_Subgroup_existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem
end P2MW
export P2MW.S_Subgroup_existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem (solution)
