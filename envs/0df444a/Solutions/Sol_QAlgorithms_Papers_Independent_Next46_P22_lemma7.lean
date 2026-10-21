-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.lemma7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:56:10.084215+00:00
-- url     : https://prove2.me/submissions/e3f8fdc9-56bc-44fe-854b-7264f22324cf

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

namespace G61Q

variable {F H V X : Type*} [Field F] [Ring H] [HopfAlgebra F H]
  [AddCommGroup V] [Module F V] [AddCommGroup X] [Module F X]

/-- comodule antipode collapse: Σ Λ(y0, y1 S(k)) = Λ(b, 1). -/
theorem coll (ρ : RightComodule F H V) (Λ : V →ₗ[F] H →ₗ[F] X) (b : V) :
    tensorSum (ρ.rho b) (fun y k => tensorSum (ρ.rho y)
      (fun y0 y1 => Λ y0 (y1 * HopfAlgebra.antipode F k))) = Λ b 1 := by
  let Θ' : V ⊗[F] (H ⊗[F] H) →ₗ[F] X := TensorProduct.lift Λ ∘ₗ
      LinearMap.lTensor V (LinearMap.mul' F H ∘ₗ (HopfAlgebra.antipode F (A := H)).lTensor H)
  let Θ : (V ⊗[F] H) ⊗[F] H →ₗ[F] X := Θ' ∘ₗ (TensorProduct.assoc F V H H).toLinearMap
  have hin : ∀ y k, tensorSum (ρ.rho y) (fun y0 y1 => Λ y0 (y1 * HopfAlgebra.antipode F k)) =
      Θ (ρ.rho y ⊗ₜ[F] k) := by
    intro y k
    let Λk : V →ₗ[F] H →ₗ[F] X := LinearMap.mk₂ F (fun y0 y1 => Λ y0 (y1 * HopfAlgebra.antipode F k))
      (by intro a b c; simp) (by intro c a b; simp)
      (by intro a b c; simp [add_mul]) (by intro c a b; simp)
    rw [G61P.ts_eq _ (fun y0 y1 => Λ y0 (y1 * HopfAlgebra.antipode F k)) Λk (fun _ _ => rfl)]
    induction (ρ.rho y) using TensorProduct.induction_on with
    | zero => simp
    | tmul x z => simp [Θ, Θ', Λk]
    | add p q hp hq => rw [map_add, hp, hq, TensorProduct.add_tmul, map_add]
  simp only [hin]
  let Φ : V →ₗ[F] H →ₗ[F] X := ((TensorProduct.mk F (V ⊗[F] H) H).compl₁₂ ρ.rho LinearMap.id).compr₂ Θ
  rw [G61P.ts_eq _ (fun y k => Θ (ρ.rho y ⊗ₜ[F] k))
    Φ (fun _ _ => rfl)]
  have h1 : TensorProduct.lift Φ (ρ.rho b) = Θ (TensorProduct.map ρ.rho LinearMap.id (ρ.rho b)) := by
    induction (ρ.rho b) using TensorProduct.induction_on with
    | zero => simp
    | tmul x z => simp; rfl
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
  rw [h1]
  simp only [Θ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [ρ.coassoc b]
  have h2 : Θ' (TensorProduct.map LinearMap.id (Coalgebra.comul (R := F)) (ρ.rho b)) =
      TensorProduct.lift Λ (LinearMap.lTensor V ((Algebra.linearMap F H) ∘ₗ Coalgebra.counit) (ρ.rho b)) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul]
    simp only [Θ', LinearMap.coe_comp, Function.comp_apply]
    rw [← LinearMap.lTensor_def, ← LinearMap.comp_apply (LinearMap.lTensor V _) (LinearMap.lTensor V _),
      ← LinearMap.lTensor_comp]
    simp only [LinearMap.comp_assoc]
  rw [h2]
  conv_rhs => rw [← ρ.counital b]
  induction (ρ.rho b) using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    simp
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add, map_add, LinearMap.add_apply]

end G61Q

theorem solution {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
    (rho : RightComodule F H L) (hr : ComoduleLie rho)
    (M : Submodule F L) (hM : CoStable rho M) :
    CoStable rho (Centralizer M) := by
  intro a ha
  -- Step A
  have hA : ∀ b ∈ M, tensorSum (rho.rho a) (fun a0 a1 => ⁅a0, b⁆ ⊗ₜ[F] a1) = 0 := by
    intro b hb
    let Λ : L → H → L →ₗ[F] H →ₗ[F] L ⊗[F] H := fun a0 a1 => LinearMap.mk₂ F
      (fun y0 w => ⁅a0, y0⁆ ⊗ₜ[F] (a1 * w))
      (by intro x y z; simp [lie_add, TensorProduct.add_tmul]) (by intro c x y; simp [lie_smul, TensorProduct.smul_tmul'])
      (by intro x y z; simp [mul_add, TensorProduct.tmul_add]) (by intro c x y; simp [TensorProduct.tmul_smul])
    have e1 : ∀ (a0 : L) (a1 : H), ⁅a0, b⁆ ⊗ₜ[F] a1 = tensorSum (rho.rho b) (fun y k => tensorSum (rho.rho y)
        (fun y0 y1 => ⁅a0, y0⁆ ⊗ₜ[F] (a1 * (y1 * HopfAlgebra.antipode F k)))) := by
      intro a0 a1
      have h := G61Q.coll rho (Λ a0 a1) b
      rw [show ((Λ a0 a1) b) 1 = ⁅a0, b⁆ ⊗ₜ[F] a1 from (show ⁅a0, b⁆ ⊗ₜ[F] (a1 * 1) = ⁅a0, b⁆ ⊗ₜ[F] a1 by rw [mul_one])] at h
      exact h.symm
    simp only [e1]
    let R : H → L ⊗[F] H →ₗ[F] L ⊗[F] H := fun k =>
      LinearMap.lTensor L ((LinearMap.mul F H).flip (HopfAlgebra.antipode F k))
    have e2 : ∀ (y : L) (k : H), tensorSum (rho.rho a) (fun a0 a1 => tensorSum (rho.rho y)
        (fun y0 y1 => ⁅a0, y0⁆ ⊗ₜ[F] (a1 * (y1 * HopfAlgebra.antipode F k)))) = R k (rho.rho ⁅a, y⁆) := by
      intro y k
      rw [hr a y, G61P.map_ts]
      unfold tensorSum
      refine Finset.sum_congr rfl (fun p _ => ?_)
      dsimp only
      rw [map_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp [R, mul_assoc]
    unfold tensorSum
    rw [Finset.sum_comm]
    have e3 := fun (q : L × H) => e2 q.1 q.2
    unfold tensorSum at e3
    simp only [e3]
    let Ψ : L →ₗ[F] H →ₗ[F] L ⊗[F] H := LinearMap.mk₂ F (fun y k => R k (rho.rho ⁅a, y⁆))
      (by intro x y z; simp [lie_add]) (by intro c x y; simp [lie_smul])
      (by intro x y z; simp [R, LinearMap.lTensor_add]) (by intro c x y; simp [R, LinearMap.lTensor_smul])
    have e4 := G61P.ts_lift (rho.rho b) Ψ
    unfold tensorSum at e4
    simp only [Ψ, LinearMap.mk₂_apply] at e4
    rw [e4]
    have hb' := hM b hb
    unfold coactionTensorImage at hb'
    generalize rho.rho b = z at hb' ⊢
    induction hb' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, h, rfl⟩ := hx
      simp [Ψ, ha v hv]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  -- Step B
  let e := Module.Free.chooseBasis F H
  let E := TensorProduct.equivFinsuppOfBasisRight (M := L) e
  set c := E (rho.rho a) with hc
  have hρ : rho.rho a = c.sum (fun i m => m ⊗ₜ[F] e i) := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, hc, LinearEquiv.symm_apply_apply]
  have hci : ∀ i, c i ∈ Centralizer M := by
    intro i b hb
    have h0 := hA b hb
    let Φb : L →ₗ[F] H →ₗ[F] L ⊗[F] H := LinearMap.mk₂ F (fun x h => ⁅x, b⁆ ⊗ₜ[F] h)
      (by intro x y z; simp [add_lie, TensorProduct.add_tmul]) (by intro c x y; simp [smul_lie, TensorProduct.smul_tmul'])
      (by intro x y z; simp [TensorProduct.tmul_add]) (by intro c x y; simp [TensorProduct.tmul_smul])
    rw [G61P.ts_eq _ (fun a0 a1 => ⁅a0, b⁆ ⊗ₜ[F] a1) Φb (fun _ _ => rfl), hρ] at h0
    have h1 : E.symm (c.mapRange (fun x => ⁅x, b⁆) (by simp)) = 0 := by
      rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_mapRange_index (by simp)]
      rw [← h0, Finsupp.sum, Finsupp.sum, map_sum]
      exact Finset.sum_congr rfl (fun _ _ => rfl)
    have h2 := congrArg (fun f => f i) (E.symm.injective (h1.trans (map_zero E.symm).symm))
    simpa using h2
  rw [hρ]
  unfold coactionTensorImage
  exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨c i, hci i, e i, rfl⟩)
