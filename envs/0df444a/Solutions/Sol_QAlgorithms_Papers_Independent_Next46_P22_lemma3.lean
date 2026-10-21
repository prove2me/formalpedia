-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.lemma3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:48:13.702992+00:00
-- url     : https://prove2.me/submissions/0ccd6cbf-e5c7-45b2-b0a0-017cc9576df9

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

theorem ts_bil {C D : Type*} [AddCommGroup C] [Module F C] [AddCommGroup D] [Module F D]
    (z : A ⊗[F] B) (G : A →ₗ[F] B →ₗ[F] X) (f : A → B → X) (hf : ∀ a b, f a b = G a b)
    (z' : C ⊗[F] D) (u : C → D → A) (w : C → D → B)
    (hz : z = tensorSum z' (fun x y => u x y ⊗ₜ[F] w x y)) :
    tensorSum z f = tensorSum z' (fun x y => G (u x y) (w x y)) := by
  rw [ts_eq z f G hf, hz]
  unfold tensorSum
  rw [map_sum]
  simp

theorem map_ts {Y : Type*} [AddCommGroup Y] [Module F Y] (T : X →ₗ[F] Y) (z : A ⊗[F] B) (f : A → B → X) :
    T (tensorSum z f) = tensorSum z (fun a b => T (f a b)) := by
  unfold tensorSum; rw [map_sum]

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

theorem ts_lam (alpha : H →ₐ[F] Module.End F L) (u v : L) (z : H ⊗[F] H) :
    tensorSum z (fun h1 h2 => ⁅alpha h1 u, alpha h2 v⁆) = TensorProduct.lift (lam alpha u v) z :=
  ts_eq z (fun h1 h2 => ⁅alpha h1 u, alpha h2 v⁆) (lam alpha u v) (fun _ _ => rfl)

end G61P

open QAlgorithms.Papers.Independent.Next46.P22
open Classical

theorem solution {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
    {V : Type*} [AddCommGroup V] [Module F V] [LieRingModule L V] [LieModule F L V]
    (rhoL : RightComodule F H L) (hr : ComoduleLie rhoL)
    (rhoV : RightComodule F H V) (hs : SymmetricComodule rhoL rhoV)
    (omega : L →ₗ[F] V) (ho : Colinear rhoL rhoV omega) :
    ColinearTwo rhoL rhoV (LieModule.Cohomology.d₁₂ F L V omega) := by
  intro a b
  -- bilinear maps
  let G1 : L → H → V →ₗ[F] H →ₗ[F] V ⊗[F] H := fun a0 a1 => LinearMap.mk₂ F
    (fun v0 v1 => ⁅a0, v0⁆ ⊗ₜ[F] (a1 * v1))
    (by intro x y z; simp [lie_add, TensorProduct.add_tmul]) (by intro c x y; simp [lie_smul, TensorProduct.smul_tmul'])
    (by intro x y z; simp [mul_add, TensorProduct.tmul_add]) (by intro c x y; simp [TensorProduct.tmul_smul])
  let G2 : L → H → V →ₗ[F] H →ₗ[F] V ⊗[F] H := fun b0 b1 => LinearMap.mk₂ F
    (fun v0 v1 => ⁅b0, v0⁆ ⊗ₜ[F] (v1 * b1))
    (by intro x y z; simp [lie_add, TensorProduct.add_tmul]) (by intro c x y; simp [lie_smul, TensorProduct.smul_tmul'])
    (by intro x y z; simp [add_mul, TensorProduct.tmul_add]) (by intro c x y; simp [TensorProduct.tmul_smul])
  let G3 : L →ₗ[F] H →ₗ[F] V ⊗[F] H := LinearMap.mk₂ F
    (fun x h => omega x ⊗ₜ[F] h)
    (by intro x y z; simp [TensorProduct.add_tmul]) (by intro c x y; simp [TensorProduct.smul_tmul'])
    (by intro x y z; simp [TensorProduct.tmul_add]) (by intro c x y; simp [TensorProduct.tmul_smul])
  have h1 : rhoV.rho ⁅a, omega b⁆ = tensorSum (rhoL.rho a) (fun a0 a1 =>
      tensorSum (rhoL.rho b) (fun b0 b1 => ⁅a0, omega b0⁆ ⊗ₜ[F] (a1 * b1))) := by
    rw [hs.1 a (omega b)]
    unfold tensorSum
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have := G61P.ts_bil (rhoV.rho (omega b)) (G1 p.1 p.2) (fun v0 v1 => ⁅p.1, v0⁆ ⊗ₜ[F] (p.2 * v1))
      (fun _ _ => rfl) (rhoL.rho b) (fun x _ => omega x) (fun _ y => y) (ho b)
    unfold tensorSum at this
    exact this
  have h2 : rhoV.rho ⁅b, omega a⁆ = tensorSum (rhoL.rho a) (fun a0 a1 =>
      tensorSum (rhoL.rho b) (fun b0 b1 => ⁅b0, omega a0⁆ ⊗ₜ[F] (a1 * b1))) := by
    rw [hs.2 b (omega a)]
    have e : ∀ b0 b1, tensorSum (rhoV.rho (omega a)) (fun v0 v1 => ⁅b0, v0⁆ ⊗ₜ[F] (v1 * b1)) =
        tensorSum (rhoL.rho a) (fun a0 a1 => ⁅b0, omega a0⁆ ⊗ₜ[F] (a1 * b1)) := fun b0 b1 =>
      G61P.ts_bil (rhoV.rho (omega a)) (G2 b0 b1) _ (fun _ _ => rfl) (rhoL.rho a)
        (fun x _ => omega x) (fun _ y => y) (ho a)
    simp only [e]
    unfold tensorSum
    rw [Finset.sum_comm]
  have h3 : rhoV.rho (omega ⁅a, b⁆) = tensorSum (rhoL.rho a) (fun a0 a1 =>
      tensorSum (rhoL.rho b) (fun b0 b1 => omega ⁅a0, b0⁆ ⊗ₜ[F] (a1 * b1))) := by
    rw [ho, G61P.ts_eq _ (fun x h => omega x ⊗ₜ[F] h) G3 (fun _ _ => rfl), hr a b]
    rw [G61P.map_ts]
    unfold tensorSum
    refine Finset.sum_congr rfl (fun p _ => ?_)
    dsimp only
    rw [map_sum]
    rfl
  rw [LieModule.Cohomology.d₁₂_apply_apply, map_sub, map_sub, h1, h2, h3]
  unfold tensorSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  dsimp only
  rw [LieModule.Cohomology.d₁₂_apply_apply, TensorProduct.sub_tmul, TensorProduct.sub_tmul]
