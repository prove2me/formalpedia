-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ord_norm_eq_length_b38d6a2def59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:14.782174+00:00
-- url     : https://prove2.me/submissions/e3009b3b-1cd8-45f2-a032-50fcebaa17f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ord_prod_e2b9c1e6a97e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module
noncomputable section
variable {R B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B]
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {b : B} (hb : Function.Injective (fun x : B => b * x)) :
    Ring.ord R (Algebra.norm R b) = Module.length R (B ⧸ Ideal.span {b}) := by
  classical
  let bs := Module.Free.chooseBasis R B
  let ι := Module.Free.ChooseBasisIndex R B
  let N : Submodule R B := (Ideal.span {b}).restrictScalars R
  let m : B →ₗ[R] B := Algebra.lmul R B b
  have hm : Function.Injective m := hb
  have hrange : LinearMap.range m = N := by
    ext x
    simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton', N, m]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm y b⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm b y⟩
  let φ : B ≃ₗ[R] N := (LinearEquiv.ofInjective m hm).trans (LinearEquiv.ofEq _ _ hrange)
  have h : Module.finrank R N = Module.finrank R B := φ.finrank_eq.symm
  let a := Submodule.smithNormalFormCoeffs bs h
  let b' := Submodule.smithNormalFormTopBasis bs h
  let ab := Submodule.smithNormalFormBotBasis bs h
  have ab_eq : ∀ i, (ab i : B) = a i • b' i := Submodule.smithNormalFormBotBasis_def bs h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero bs h

  have hlen : Module.length R (B ⧸ Ideal.span {b}) = ∑ i, Ring.ord R (a i) := by
    rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {b})).length_eq,
      (Submodule.quotientEquivPiSpan N bs h).length_eq, Module.length_pi_of_fintype]
    rfl

  let E : B ≃ₗ[R] N := b'.equiv ab (Equiv.refl ι)
  let D : B →ₗ[R] B := N.subtype ∘ₗ E.toLinearMap
  let u : B ≃ₗ[R] B := φ.trans E.symm
  have hmDu : m = D ∘ₗ u.toLinearMap := by
    ext x
    simp [D, u, φ]
  have hDb : ∀ j, D (b' j) = a j • b' j := fun j => by
    simp only [D, E, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, Basis.equiv_apply]
    exact ab_eq j
  have hD : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hDb, map_smul, Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hdet : Algebra.norm R b = (∏ i, a i) * LinearMap.det (u : B →ₗ[R] B) := by
    rw [Algebra.norm_apply, show Algebra.lmul R B b = m from rfl, hmDu, LinearMap.det_comp,
      ← LinearMap.det_toMatrix b' D, hD, Matrix.det_diagonal]
  rw [hdet, Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' u), ord_prod _ _ fun i _ => ha i,
    hlen]
end GroundTheory.Heights₂.Heights.Vertical
