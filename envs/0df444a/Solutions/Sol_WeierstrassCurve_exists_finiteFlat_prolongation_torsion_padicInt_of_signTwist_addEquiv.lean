-- Prove2me | solution 1 for WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6d3f8e10-e1fd-5b7f-aa23-569c07fb4b0e

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure ℚ_[p])]
    (E₁ E₂ : WeierstrassCurve ℚ_[p])
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (φ : Submodule.torsionBy ℤ (E₁⁄(AlgebraicClosure ℚ_[p])).Point p
          ≃+ Submodule.torsionBy ℤ (E₂⁄(AlgebraicClosure ℚ_[p])).Point p)
    (hφ : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → ∀ P, φ (σ • P) = σ • φ P) ∧
        (σ s ≠ s → ∀ P, φ (σ • P) = -(σ • φ P)))
    (hE₂ : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
        Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
        ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
            Submodule.torsionBy ℤ (E₂⁄(AlgebraicClosure ℚ_[p])).Point p,
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
            (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
            (∀ h : H, g h = σ (f h)) → e g = σ • (e f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ (E₁⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by

  rcases (by
    by_cases hdsq : IsSquare d
    ·
      left; intro σ P
      refine (hφ σ).1 ?_ P
      obtain ⟨t, ht⟩ := hdsq
      have hst : s ^ 2 = (algebraMap ℚ_[p] _ t) ^ 2 := by rw [hs, ht, map_mul, ← sq]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hst with h | h
      · rw [h]; exact σ.commutes t
      · rw [h, map_neg, σ.commutes t]
    · by_cases hp2 : p = 2
      ·
        left; intro σ P
        rcases eq_or_ne (σ s) s with h | h
        · exact (hφ σ).1 h P
        · rw [(hφ σ).2 h P]

          set Q := σ • φ P with hQ
          have key : (p : ℤ) • Q = 0 :=
            Subtype.ext ((Submodule.mem_torsionBy_iff _ _).mp Q.2)
          have key2 : (2 : ℤ) • Q = 0 := by
            have hcast : ((p : ℤ) : ℤ) = (2 : ℤ) := by exact_mod_cast hp2
            rw [← hcast]; exact key
          rw [two_smul] at key2
          exact neg_eq_of_add_eq_zero_left key2
      · exact Or.inr ⟨hp2, hdsq⟩ :
    (∀ σ P, φ (σ • P) = σ • φ P) ∨ (p ≠ 2 ∧ ¬ IsSquare d)) with hφeq | ⟨hp2, hdsq⟩
  ·
    obtain ⟨H, _, _, hfin, hflat, hcocomm, e, he_add, he_act⟩ := hE₂
    exact ⟨H, _, _, hfin, hflat, hcocomm, e.trans φ.symm.toEquiv,
      fun f g => by
        simp only [Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
          he_add f g, map_add],
      fun σ f g hfg => by
        simp only [Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
          he_act σ f g hfg]

        refine φ.injective ?_
        rw [AddEquiv.apply_symm_apply, hφeq, AddEquiv.apply_symm_apply]⟩
  ·
    exact WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare
      p hp2 E₁ E₂ d hd hdsq s hs φ hφ hE₂

end S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv
end P2MW
export P2MW.S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv (solution)
