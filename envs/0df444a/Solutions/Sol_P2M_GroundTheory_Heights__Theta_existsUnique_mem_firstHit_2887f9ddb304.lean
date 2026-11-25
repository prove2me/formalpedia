-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_existsUnique_mem_firstHit_2887f9ddb304
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:46.309013+00:00
-- url     : https://prove2.me/submissions/f00d9e2e-f5fa-4c5d-b1e7-5011110f6a51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (Γ : Subgroup G) (A : ℕ → Set G)
    (hinj : ∀ i, ∀ γ ∈ Γ, ∀ x ∈ A i, γ * x ∈ A i → γ = 1)
    (hcov : ∀ x : G, ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i) (x : G) :
    ∃! γ : Γ, γ • x ∈ firstHit Γ A := by
  classical
  have hex : ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i := hcov x
  let i₀ := Nat.find hex
  obtain ⟨γ, hγ, hγx⟩ := Nat.find_spec hex
  have hmin : ∀ j < i₀, ∀ δ ∈ Γ, δ * x ∉ A j := fun j hj δ hδ hδx =>
    Nat.find_min hex hj ⟨δ, hδ, hδx⟩
  have hγF : (γ : G) * x ∈ firstHit Γ A := by
    refine mem_iUnion.mpr ⟨i₀, hγx, ?_⟩
    rintro ⟨δ, hδ, hδy⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hδy
    obtain ⟨hj, hjA⟩ := mem_iUnion.mp hj
    refine hmin j hj (δ⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem hδ) hγ) ?_
    simpa [mul_assoc] using hjA
  refine ⟨⟨γ, hγ⟩, ?_, ?_⟩
  · show ((⟨γ, hγ⟩ : Γ) • x ∈ firstHit Γ A)
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hγF
  ·
    have key : ∀ (α β : Γ), (α : G) * x ∈ firstHit Γ A → (β : G) * x ∈ firstHit Γ A →
        ∀ i i', (α : G) * x ∈ A i \ saturate Γ (⋃ j < i, A j) →
          (β : G) * x ∈ A i' \ saturate Γ (⋃ j < i', A j) → i ≤ i' := by
      intro α β _ _ i i' hα hβ
      by_contra hlt'
      have hlt := not_le.mp hlt'
      apply hα.2
      refine ⟨(α : G) * (β : G)⁻¹, Γ.mul_mem α.2 (Γ.inv_mem β.2), ?_⟩
      refine mem_iUnion₂.mpr ⟨i', hlt, ?_⟩
      simpa [mul_assoc] using hβ.1
    intro β hβ
    rw [Subgroup.smul_def, smul_eq_mul] at hβ
    obtain ⟨i, hi⟩ := mem_iUnion.mp hβ
    obtain ⟨i', hi'⟩ := mem_iUnion.mp hγF
    have h1 := key β ⟨γ, hγ⟩ hβ hγF i i' hi hi'
    have h2 := key ⟨γ, hγ⟩ β hγF hβ i' i hi' hi
    have hii : i = i' := le_antisymm h1 h2
    subst hii
    have hmul := hinj i ((γ : G) * (β : G)⁻¹) (Γ.mul_mem hγ (Γ.inv_mem β.2)) _ hi.1
      (by simpa [mul_assoc] using hi'.1)
    apply Subtype.ext
    have : (γ : G) = β := by
      have := congrArg (· * (β : G)) hmul
      simpa using this
    exact this.symm
end GroundTheory.Heights₂.Theta
