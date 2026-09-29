-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3595d4b7-0a97-5a2c-a460-41ce08ba0b1c

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero
import Theorems.Thm_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option maxHeartbeats 6400000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (hW : ¬ W.IsElliptic)
    (hc4 : W.c₄ ≠ 0) (n : ℕ) [Fact n.Prime] :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _

  obtain ⟨c, hc, C, hCW⟩ :=
    WeierstrassCurve.exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero
      W hW hc4

  obtain ⟨A, _, _, hFin, hCocomm, eA₀, heA₀_mul, heA₀_gal⟩ :=
    WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero K c hc n

  obtain ⟨eVC, heVC_gal⟩ :=
    WeierstrassCurve.VariableChange.exists_addEquiv_affine_point_baseChange_gal_equiv K W C
  refine ⟨A, ‹_›, ‹_›, hFin, hCocomm, ?_⟩

  revert eVC heVC_gal
  generalize hW'' : C • W = W'' at hCW
  subst hCW
  intro eVC heVC_gal

  let eVCt : Submodule.torsionBy ℤ
             ((⟨0, c, 0, 0, 0⟩ : WeierstrassCurve K)⁄(AlgebraicClosure K)).Point (n:ℤ)
           ≃ Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point (n:ℤ) :=
    { toFun := fun ⟨P, hP⟩ => ⟨eVC P, by
        rw [Submodule.mem_torsionBy_iff] at hP ⊢
        rw [← map_zsmul eVC, hP, _root_.map_zero]⟩
      invFun := fun ⟨Q, hQ⟩ => ⟨eVC.symm Q, by
        rw [Submodule.mem_torsionBy_iff] at hQ ⊢
        rw [← map_zsmul eVC.symm, hQ, _root_.map_zero]⟩
      left_inv := fun ⟨P, _⟩ => by simp
      right_inv := fun ⟨Q, _⟩ => by simp }
  refine ⟨eA₀.trans eVCt, ?_, ?_⟩
  · intro f g
    simp only [Equiv.trans_apply]
    rw [heA₀_mul]
    apply Subtype.ext
    exact eVC.map_add _ _
  · intro σ f g hfg
    simp only [Equiv.trans_apply]
    rw [heA₀_gal σ f g hfg]
    apply Subtype.ext
    exact heVC_gal σ _

end S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero (solution)
