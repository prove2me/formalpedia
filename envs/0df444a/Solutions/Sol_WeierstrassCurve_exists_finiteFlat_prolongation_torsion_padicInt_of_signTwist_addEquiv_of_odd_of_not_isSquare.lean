-- Prove2me | solution 1 for WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c888bf76-a807-5436-bc19-edef8838c819

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_HopfAlgebra_exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [DecidableEq (AlgebraicClosure ℚ_[p])]
    (E₁ E₂ : WeierstrassCurve ℚ_[p])
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
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
  obtain ⟨H, _, _, hfin, hflat, hcocomm, e, he_add, he_act⟩ := hE₂

  obtain ⟨H', _, _, hfin', hflat', hcocomm', e', he'_add, he'_sign⟩ :=
    HopfAlgebra.exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare
      p hp2 d hd hd_nsq s hs H hfin hflat hcocomm e he_add he_act

  refine ⟨H', _, _, hfin', hflat', hcocomm', e'.trans φ.symm.toEquiv, ?_, ?_⟩
  ·
    intro f g
    simp only [Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
      he'_add f g, map_add]
  ·
    intro σ f g hfg
    simp only [Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv]
    obtain ⟨hpos, hneg⟩ := he'_sign σ f g hfg
    rcases eq_or_ne (σ s) s with hσs | hσs
    ·
      rw [hpos hσs]
      refine φ.injective ?_
      rw [AddEquiv.apply_symm_apply, (hφ σ).1 hσs, AddEquiv.apply_symm_apply]
    ·
      rw [hneg hσs]
      refine φ.injective ?_
      rw [AddEquiv.apply_symm_apply, (hφ σ).2 hσs, AddEquiv.apply_symm_apply]

end S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare
end P2MW
export P2MW.S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare (solution)
