-- Prove2me | solution 1 for WeierstrassCurve.exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/61b81c5f-54f9-56c7-ada0-08a2ca6f96fd

import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure ℚ_[p])]
    (qT : ℚ_[p])
    (s : AlgebraicClosure ℚ_[p])
    (C : VariableChange (AlgebraicClosure ℚ_[p]))
    (hC : C • ((W.map (Int.castRingHom ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
          = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
    (hCσ : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
        (σ s ≠ s → C.map σ.toAlgHom.toRingHom
          = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C)) :
    ∃ φ : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p
          ≃+ Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
      ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → ∀ P, φ (σ • P) = σ • φ P) ∧
        (σ s ≠ s → ∀ P, φ (σ • P) = -(σ • φ P)) := by
  obtain ⟨ψ, hψ⟩ :=
    WeierstrassCurve.exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
      W p qT s C hC hCσ

  have htors : ∀ P, P ∈ Submodule.torsionBy ℤ _ (p:ℤ) →
      ψ P ∈ Submodule.torsionBy ℤ _ (p:ℤ) := fun P hP => by
    rw [Submodule.mem_torsionBy_iff] at hP ⊢
    rw [← map_zsmul ψ, hP]; exact ψ.map_zero
  have htors' : ∀ Q, Q ∈ Submodule.torsionBy ℤ _ (p:ℤ) →
      ψ.symm Q ∈ Submodule.torsionBy ℤ _ (p:ℤ) := fun Q hQ => by
    rw [Submodule.mem_torsionBy_iff] at hQ ⊢
    rw [← map_zsmul ψ.symm, hQ]; exact ψ.symm.map_zero
  refine ⟨AddEquiv.mk'
    ⟨fun P => ⟨ψ P.1, htors P.1 P.2⟩,
     fun Q => ⟨ψ.symm Q.1, htors' Q.1 Q.2⟩,
     fun P => by ext; simp,
     fun Q => by ext; simp⟩
    (fun P Q => by ext; exact map_add ψ P.1 Q.1), ?_⟩
  intro σ
  refine ⟨fun hσs P => ?_, fun hσs P => ?_⟩
  · ext; exact (hψ σ).1 hσs P.1
  · ext; exact (hψ σ).2 hσs P.1

end S_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior
end P2MW
export P2MW.S_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior (solution)
