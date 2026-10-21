-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.lemma6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:35:34.679573+00:00
-- url     : https://prove2.me/submissions/900dfb7c-1845-45f9-9e1a-b9118ef70c27

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

open QAlgorithms.Papers.Independent.Next46.P22
open scoped TensorProduct

namespace G61P

variable {F A B X : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup X] [Module F X]

theorem ts_lift (z : A ⊗[F] B) (Φ : A →ₗ[F] B →ₗ[F] X) :
    tensorSum z (fun a b => Φ a b) = TensorProduct.lift Φ z := by
  unfold tensorSum
  conv_rhs => rw [(TensorProduct.exists_finset z).choose_spec]
  simp [map_sum]

theorem ts_eq (z : A ⊗[F] B) (f : A → B → X) (Φ : A →ₗ[F] B →ₗ[F] X)
    (h : ∀ a b, f a b = Φ a b) : tensorSum z f = TensorProduct.lift Φ z := by
  have : f = fun a b => Φ a b := funext fun a => funext fun b => h a b
  subst this; exact ts_lift z Φ

theorem ts_mem (z : A ⊗[F] B) (f : A → B → X) (U : Submodule F X) (h : ∀ a b, f a b ∈ U) :
    tensorSum z f ∈ U := by
  unfold tensorSum; exact Submodule.sum_mem _ (fun p _ => h _ _)

variable {H L : Type*} [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- bilinear map (x, w) ↦ ⁅α x u, α w v⁆ -/
def lam (alpha : H →ₐ[F] Module.End F L) (u v : L) : H →ₗ[F] H →ₗ[F] L :=
  LinearMap.mk₂ F (fun x w => ⁅alpha x u, alpha w v⁆)
    (by intro a b c; simp [add_lie]) (by intro c a b; simp [smul_lie])
    (by intro a b c; simp [lie_add]) (by intro c a b; simp [lie_smul])

theorem key (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) (h : H) (u v : L) :
    ⁅alpha h u, v⁆ = tensorSum (Coalgebra.comul (R := F) h)
      (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆) := by
  -- Φ h1 h2 = α h1 ⁅u, α (S h2) v⁆
  let Φ : H →ₗ[F] H →ₗ[F] L := LinearMap.mk₂ F
    (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆)
    (by intro a b c; simp) (by intro c a b; simp)
    (by intro a b c; simp) (by intro c a b; simp)
  rw [ts_eq _ (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆) Φ (fun _ _ => rfl)]
  -- Θ' : H ⊗ (H ⊗ H) → L
  let Θ' : H ⊗[F] (H ⊗[F] H) →ₗ[F] L :=
    TensorProduct.lift (lam alpha u v) ∘ₗ
      (LinearMap.lTensor H (LinearMap.mul' F H ∘ₗ (HopfAlgebra.antipode F (A := H)).lTensor H))
  have hΦ : TensorProduct.lift Φ = Θ' ∘ₗ (TensorProduct.assoc F H H H).toLinearMap ∘ₗ
      (Coalgebra.comul (R := F) (A := H)).rTensor H := by
    apply TensorProduct.ext'
    intro h1 h2
    simp only [TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
    show alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆ = _
    rw [ha h1 u _]
    rw [ts_eq _ (fun x y => ⁅alpha x u, alpha y (alpha (HopfAlgebra.antipode F h2) v)⁆) (lam alpha u (alpha (HopfAlgebra.antipode F h2) v)) (fun _ _ => rfl)]
    induction (Coalgebra.comul (R := F) h1) using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [Θ', lam, TensorProduct.assoc_tmul, Module.End.mul_apply]
    | add p q hp hq => rw [map_add, hp, hq, TensorProduct.add_tmul, map_add, map_add]
  rw [hΦ]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [Coalgebra.coassoc_apply]
  have hΘ : Θ' ∘ₗ (Coalgebra.comul (R := F) (A := H)).lTensor H =
      TensorProduct.lift (lam alpha u v) ∘ₗ
        LinearMap.lTensor H ((Algebra.linearMap F H) ∘ₗ Coalgebra.counit) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul]
    simp only [Θ', LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
  have := congrArg (fun f => f (Coalgebra.comul (R := F) h)) hΘ
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [this]
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp [lam]

end G61P

open QAlgorithms.Papers.Independent.Next46.P22
open Classical

theorem solution {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
    (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha)
    (M : Submodule F L) (hM : ActionStable alpha M) :
    ActionStable alpha (Centralizer M) := by
  intro h a haC b hb
  rw [G61P.key alpha ha h a b]
  unfold tensorSum
  refine Finset.sum_eq_zero (fun p _ => ?_)
  show alpha p.1 ⁅a, _⁆ = 0
  rw [haC _ (hM _ _ hb), map_zero]
