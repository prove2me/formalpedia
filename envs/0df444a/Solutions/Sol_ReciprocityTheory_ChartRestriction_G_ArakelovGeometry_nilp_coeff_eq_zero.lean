-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.nilp_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:02.997003+00:00
-- url     : https://prove2.me/submissions/498ab023-8cc9-49d2-8dfb-c37078e868c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isReduced_tensor_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eq_zero_of_sum_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ} {s : Fin r → Ω}
    (hs : LinearIndependent ℚ s) {c : Fin r → ℂ}
    (h : IsNilpotent (∑ k, c k ⊗ₜ[ℚ] s k : ℂ ⊗[ℚ] Ω)) : c = 0 := by
  classical
  let A : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ((Finset.univ.image c : Finset ℂ) : Set ℂ)
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset _)
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ) (B := A)
  have hcA : ∀ k, c k ∈ A := fun k => Algebra.subset_adjoin (by simp)
  let cA : Fin r → A := fun k => ⟨c k, hcA k⟩
  let tA : A ⊗[ℚ] Ω := ∑ k, cA k ⊗ₜ[ℚ] s k
  let ι : A ⊗[ℚ] Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω := Algebra.TensorProduct.map A.val (AlgHom.id ℚ Ω)
  have hι : Function.Injective ι := by
    have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω) (A.val.toLinearMap)
      Subtype.val_injective
    have heq : ∀ x, ι x = LinearMap.rTensor Ω A.val.toLinearMap x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [ι, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    intro x y hxy
    apply hinj
    rw [← heq, ← heq, hxy]
  have hιt : ι tA = ∑ k, c k ⊗ₜ[ℚ] s k := by
    simp [tA, ι, map_sum, Algebra.TensorProduct.map_tmul, cA]
  have hnA : IsNilpotent tA := by
    obtain ⟨m, hm⟩ := h
    refine ⟨m, hι ?_⟩
    rw [map_pow, hιt, hm, map_zero]
  have key : ∀ (E : Type) [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E] (φ : A →ₐ[ℚ] E),
      ∀ k, φ (cA k) = 0 := by
    intro E _ _ _ φ
    let π : A ⊗[ℚ] Ω →ₐ[ℚ] E ⊗[ℚ] Ω := Algebra.TensorProduct.map φ (AlgHom.id ℚ Ω)
    haveI : IsReduced (E ⊗[ℚ] Ω) := isReduced_tensor_finite Ω E
    have h0 : π tA = 0 := (hnA.map π).eq_zero
    have h1 : ∑ k, φ (cA k) ⊗ₜ[ℚ] s k = 0 := by
      rw [← h0]
      simp [tA, π, map_sum, Algebra.TensorProduct.map_tmul]
    exact congrFun (eq_zero_of_sum_tmul hs h1)
  have hmax : ∀ M : Ideal A, M.IsMaximal → ∀ k, cA k ∈ M := by
    intro M hM k
    letI hF : Field (A ⧸ M) := Ideal.Quotient.field M
    haveI : Algebra.FiniteType ℚ (A ⧸ M) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ M) Ideal.Quotient.mk_surjective
    haveI : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
    exact Ideal.Quotient.eq_zero_iff_mem.1 (key (A ⧸ M) (Ideal.Quotient.mkₐ ℚ M) k)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance Ideal.bot_prime.isRadical
  funext k
  have hk : cA k ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.2 (fun J hJ => hmax J hJ.2 k)
  rw [hjac] at hk
  have h0 : cA k = 0 := (Submodule.mem_bot _).1 hk
  exact congrArg Subtype.val h0
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
