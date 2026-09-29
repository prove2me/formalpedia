-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b95c8100-6874-5d08-a0f1-3feb633260d2

import Mathlib
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv

set_option autoImplicit false

open scoped Pointwise

namespace R1AF8Card3

noncomputable def toAlgEquiv (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) :
    AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ :=
  AlgEquiv.ofRingEquiv (f := σ) (fun x => by rw [eq_ratCast, map_ratCast])

@[scoped simp] theorem toAlgEquiv_apply (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
    (a : AlgebraicClosure ℚ) : toAlgEquiv σ a = σ a := rfl

theorem mem_decompositionSubgroup (P : ValuationSubring (AlgebraicClosure ℚ))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hτP : ∀ a : AlgebraicClosure ℚ, a ∈ P ↔ τ a ∈ P) :
    τ ∈ P.decompositionSubgroup ℚ := by
  rw [MulAction.mem_stabilizer_iff]
  ext a
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (hτP s).1 hs
  · intro ha
    refine ⟨τ.symm a, (hτP _).2 (by simpa using ha), by simp [AlgEquiv.smul_def]⟩

theorem mem_inertiaSubgroupIn (P : ValuationSubring (AlgebraicClosure ℚ))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hτP : ∀ a : AlgebraicClosure ℚ, a ∈ P ↔ τ a ∈ P)
    (hres : ∀ (a : P) (h : τ (a : AlgebraicClosure ℚ) ∈ P),
      IsLocalRing.residue P ⟨τ (a : AlgebraicClosure ℚ), h⟩ = IsLocalRing.residue P a) :
    τ ∈ P.inertiaSubgroupIn ℚ := by
  have hdec : τ ∈ P.decompositionSubgroup ℚ := mem_decompositionSubgroup P τ hτP
  refine Subgroup.mem_map.2 ⟨⟨τ, hdec⟩, ?_, rfl⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  ext x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  change (⟨τ, hdec⟩ : P.decompositionSubgroup ℚ) • IsLocalRing.residue P a = IsLocalRing.residue P a
  rw [← IsLocalRing.ResidueField.residue_smul]
  have hmem : τ (a : AlgebraicClosure ℚ) ∈ P := (hτP _).1 a.2
  have hsmul : ((⟨τ, hdec⟩ : P.decompositionSubgroup ℚ) • a : P) =
      ⟨τ (a : AlgebraicClosure ℚ), hmem⟩ := by
    apply Subtype.ext
    rfl
  rw [hsmul, hres a hmem]

theorem tameCharacter_eq_one_of_apply_eq (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (hπ0 : π ≠ 0)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτπ : τ π = π) :
    P.tameCharacter π τ = 1 := by
  have h1 : τ π / π = 1 := by rw [hτπ, div_self hπ0]
  unfold ValuationSubring.tameCharacter
  rw [dif_pos (by rw [h1]; exact P.one_mem)]
  have : (⟨τ π / π, by rw [h1]; exact P.one_mem⟩ : P) = 1 := Subtype.ext h1
  rw [this, map_one]

end R1AF8Card3
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv.R1AF8Card3"

open R1AF8Card3 in
theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ) (hπ0 : π ≠ 0)
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
    (hσP : ∀ a : AlgebraicClosure ℚ, a ∈ P ↔ σ a ∈ P) (hσπ : σ π = π)
    (hσres : ∀ (a : P) (h : σ (a : AlgebraicClosure ℚ) ∈ P),
      IsLocalRing.residue P ⟨σ (a : AlgebraicClosure ℚ), h⟩ = IsLocalRing.residue P a) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ P.inertiaSubgroupIn ℚ ∧ P.tameCharacter π τ = 1 ∧
      ∀ a, τ a = σ a :=
  ⟨toAlgEquiv σ, mem_inertiaSubgroupIn P (toAlgEquiv σ) hσP hσres,
    tameCharacter_eq_one_of_apply_eq P π hπ0 (toAlgEquiv σ) hσπ, fun _ => rfl⟩

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv (solution)
