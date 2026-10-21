-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.theorem8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:46:41.032607+00:00
-- url     : https://prove2.me/submissions/876ca904-332a-4c1d-86df-8c3dca0ee95b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

open QAlgorithms.Papers.Independent.Next46.P22
open scoped TensorProduct

namespace G61S

variable {F A B X : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup X] [Module F X]

theorem ts_self (z : A ⊗[F] B) : tensorSum z (fun a b => a ⊗ₜ[F] b) = z :=
  (TensorProduct.exists_finset z).choose_spec.symm

/-- trilinear map from a function with linearity proofs -/
def tri {C : Type*} [AddCommGroup C] [Module F C] (f : A → B → C → X)
    (a1 : ∀ a a' b c, f (a + a') b c = f a b c + f a' b c) (s1 : ∀ (r : F) a b c, f (r • a) b c = r • f a b c)
    (a2 : ∀ a b b' c, f a (b + b') c = f a b c + f a b' c) (s2 : ∀ (r : F) a b c, f a (r • b) c = r • f a b c)
    (a3 : ∀ a b c c', f a b (c + c') = f a b c + f a b c') (s3 : ∀ (r : F) a b c, f a b (r • c) = r • f a b c) :
    A →ₗ[F] B →ₗ[F] C →ₗ[F] X :=
  LinearMap.mk₂ F (fun a b => { toFun := fun c => f a b c, map_add' := a3 a b, map_smul' := fun r c => s3 r a b c })
    (fun a a' b => by ext c; exact a1 a a' b c) (fun r a b => by ext c; exact s1 r a b c)
    (fun a b b' => by ext c; exact a2 a b b' c) (fun r a b => by ext c; exact s2 r a b c)

theorem ts_uncurry0 (z : A ⊗[F] B) (Φ : A →ₗ[F] B →ₗ[F] X) :
    tensorSum z (fun a b => Φ a b) = TensorProduct.lift Φ z := by
  unfold tensorSum
  conv_rhs => rw [(TensorProduct.exists_finset z).choose_spec]
  simp [map_sum]

theorem ts_uncurry (z : A ⊗[F] B) {f : A → B → X} (Φ : A →ₗ[F] B →ₗ[F] X) (hf : ∀ a b, f a b = Φ a b) :
    tensorSum z f = TensorProduct.lift Φ z := by
  have : f = fun a b => Φ a b := funext fun a => funext fun b => hf a b
  subst this; exact ts_uncurry0 z Φ

theorem map_ts {Y : Type*} [AddCommGroup Y] [Module F Y] (T : X →ₗ[F] Y) (z : A ⊗[F] B) (f : A → B → X) :
    T (tensorSum z f) = tensorSum z (fun a b => T (f a b)) := by
  unfold tensorSum; rw [map_sum]

variable {H : Type*} [Ring H] [HopfAlgebra F H]

local notation "δ" => (Coalgebra.comul (R := F) (A := H))
local notation "S" => (HopfAlgebra.antipode F (A := H))

theorem coassoc_ts (h : H) (Φ : H →ₗ[F] H →ₗ[F] H →ₗ[F] X) :
    tensorSum (δ h) (fun a x => tensorSum (δ x) (fun b y => Φ a b y)) =
    tensorSum (δ h) (fun p y => tensorSum (δ p) (fun a b => Φ a b y)) := by
  let T : (H ⊗[F] H) ⊗[F] H →ₗ[F] X := TensorProduct.lift (TensorProduct.lift Φ)
  have L1 : ∀ z : H ⊗[F] H, tensorSum z (fun a x => tensorSum (δ x) (fun b y => Φ a b y)) =
      T ((TensorProduct.assoc F H H H).symm (LinearMap.lTensor H δ z)) := by
    intro z
    have e : ∀ a x, tensorSum (δ x) (fun b y => Φ a b y) =
        T ((TensorProduct.assoc F H H H).symm (a ⊗ₜ[F] δ x)) := by
      intro a x
      rw [ts_uncurry _ (Φ a) (fun _ _ => by rfl)]
      induction (δ x) using TensorProduct.induction_on with
      | zero => simp
      | tmul b y => simp [T]
      | add p q hp hq => rw [map_add, hp, hq, TensorProduct.tmul_add, map_add, map_add]
    simp only [e]
    let Ψ : H →ₗ[F] H →ₗ[F] X :=
      ((TensorProduct.mk F H (H ⊗[F] H)).compl₂ δ).compr₂
        (T ∘ₗ (TensorProduct.assoc F H H H).symm.toLinearMap)
    rw [ts_uncurry z Ψ (fun _ _ => by rfl)]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, map_add]
  have L2 : ∀ z : H ⊗[F] H, tensorSum z (fun p y => tensorSum (δ p) (fun a b => Φ a b y)) =
      T (LinearMap.rTensor H δ z) := by
    intro z
    have e : ∀ p y, tensorSum (δ p) (fun a b => Φ a b y) = T (δ p ⊗ₜ[F] y) := by
      intro p y
      rw [ts_uncurry _ (LinearMap.mk₂ F (fun a b => Φ a b y) (by simp) (by simp) (by simp) (by simp)) (fun _ _ => by rfl)]
      induction (δ p) using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [T]
      | add p q hp hq => rw [map_add, hp, hq, TensorProduct.add_tmul, map_add]
    simp only [e]
    let Ψ : H →ₗ[F] H →ₗ[F] X :=
      ((TensorProduct.mk F (H ⊗[F] H) H).compl₁₂ δ LinearMap.id).compr₂ T
    rw [ts_uncurry z Ψ (fun _ _ => by rfl)]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add p q hp hq => simp only [map_add, hp, hq]
  rw [L1, L2, Coalgebra.coassoc_symm_apply]

open TensorProduct in
theorem comul_antipode (c : H) :
    δ (S c) = TensorProduct.map S S (TensorProduct.comm F H H (δ c)) := by
  let G : H →ₗ[F] H ⊗[F] H := TensorProduct.map S S ∘ₗ (TensorProduct.comm F H H).toLinearMap ∘ₗ δ
  let μ := LinearMap.mul' F (H ⊗[F] H)
  let K : H ⊗[F] H →ₗ[F] H ⊗[F] H := LinearMap.lTensor H (LinearMap.mul' F H ∘ₗ LinearMap.rTensor H S) ∘ₗ
    (TensorProduct.assoc F H H H).toLinearMap ∘ₗ LinearMap.rTensor H δ
  let Bil : H ⊗[F] H →ₗ[F] H →ₗ[F] H ⊗[F] H := LinearMap.mk₂ F
    (fun w y => TensorProduct.comm F H H (LinearMap.rTensor H ((LinearMap.mul F H).flip y ∘ₗ S) w))
    (by intro a b y; simp) (by intro r a y; simp)
    (by intro w y y'; rw [map_add, LinearMap.add_comp, LinearMap.rTensor_add, LinearMap.add_apply, map_add])
    (by intro r w y; rw [map_smul, LinearMap.smul_comp, LinearMap.rTensor_smul, LinearMap.smul_apply, map_smul])
  let Ω' : (H ⊗[F] H) ⊗[F] H →ₗ[F] H ⊗[F] H := TensorProduct.lift Bil
  have hΩ'v : ∀ w1 w2 y, Ω' ((w1 ⊗ₜ[F] w2) ⊗ₜ[F] y) = w2 ⊗ₜ[F] (S w1 * y) := by
    intro w1 w2 y; simp [Ω', Bil]
  have hi : μ ∘ₗ TensorProduct.map G LinearMap.id ∘ₗ (TensorProduct.assoc F H H H).toLinearMap =
      Ω' ∘ₗ LinearMap.rTensor H K := by
    apply TensorProduct.ext_threefold
    intro u v y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.rTensor_tmul]
    simp only [G, K, μ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul]
    induction (δ u) using TensorProduct.induction_on with
    | zero => simp
    | tmul u1 u2 =>
      simp [hΩ'v, Algebra.TensorProduct.tmul_mul_tmul]
    | add p q hp hq =>
      simp only [map_add, TensorProduct.add_tmul, LinearMap.mul'_apply, add_mul] at hp hq ⊢
      rw [hp, hq]
  have hii : K ∘ₗ δ = LinearMap.lTensor H (Algebra.linearMap F H ∘ₗ Coalgebra.counit) ∘ₗ δ := by
    rw [← HopfAlgebra.mul_antipode_rTensor_comul]
    simp only [K, LinearMap.comp_assoc]
    rw [Coalgebra.coassoc]
    simp only [LinearMap.lTensor_comp, LinearMap.comp_assoc]
  have hiii : Ω' ∘ₗ LinearMap.rTensor H (LinearMap.lTensor H (Algebra.linearMap F H ∘ₗ Coalgebra.counit) ∘ₗ δ) =
      (TensorProduct.mk F H H 1) ∘ₗ LinearMap.mul' F H ∘ₗ LinearMap.rTensor H S := by
    apply TensorProduct.ext'
    intro p y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul]
    rw [LinearMap.lTensor_comp_apply, Coalgebra.lTensor_counit_comul]
    simp [hΩ'v]
  have hG : (WithConv.toConv G * WithConv.toConv δ : WithConv (H →ₗ[F] H ⊗[F] H)) = 1 := by
    apply WithConv.ext
    apply LinearMap.ext
    intro x
    have e1 : TensorProduct.map G δ (δ x) =
        TensorProduct.map G LinearMap.id (LinearMap.lTensor H δ (δ x)) := by
      rw [← LinearMap.comp_apply (TensorProduct.map G LinearMap.id), LinearMap.map_comp_lTensor]
      rfl
    show μ (TensorProduct.map G δ (δ x)) = _
    rw [e1, ← Coalgebra.coassoc_apply]
    have := congrArg (fun f => f (LinearMap.rTensor H δ (δ x))) hi
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, ← LinearMap.comp_apply (LinearMap.rTensor H K), ← LinearMap.rTensor_comp]
    rw [hii]
    rw [← LinearMap.comp_apply Ω', hiii]
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply]
    rw [HopfAlgebra.mul_antipode_rTensor_comul_apply]
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rfl
  have hF := LinearMap.comul_right_inv (R := F) (C := H)
  have := left_inv_eq_right_inv hG hF
  have := congrArg (fun f : WithConv (H →ₗ[F] H ⊗[F] H) => (WithConv.ofConv f) c) this
  simpa [G] using this.symm

theorem anti_ts (z : H) (g : H →ₗ[F] X) :
    tensorSum (δ z) (fun v w => g (S v * w)) = Coalgebra.counit (R := F) z • g 1 := by
  rw [ts_uncurry _ ((LinearMap.mul F H).compl₁₂ S LinearMap.id |>.compr₂ g) (fun _ _ => by rfl)]
  have : TensorProduct.lift ((LinearMap.mul F H).compl₁₂ S LinearMap.id |>.compr₂ g) =
      g ∘ₗ LinearMap.mul' F H ∘ₗ LinearMap.rTensor H S := by
    apply TensorProduct.ext'; intro a b; simp
  rw [this]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [HopfAlgebra.mul_antipode_rTensor_comul_apply, Algebra.algebraMap_eq_smul_one, map_smul]

theorem counit_ts (z : H) (g : H →ₗ[F] X) :
    tensorSum (δ z) (fun u w => Coalgebra.counit (R := F) w • g u) = g z := by
  rw [ts_uncurry _ (LinearMap.mk₂ F (fun u w => Coalgebra.counit (R := F) w • g u)
    (by intro a b c; simp) (by intro r a b; simp [smul_comm r])
    (by intro a b c; simp [add_smul]) (by intro r a b; simp [mul_smul])) (fun _ _ => by rfl)]
  have h := Coalgebra.lTensor_counit_comul (R := F) z
  have : ∀ w : H ⊗[F] H, TensorProduct.lift (LinearMap.mk₂ F (fun u w => Coalgebra.counit (R := F) w • g u)
    (by intro a b c; simp) (by intro r a b; simp [smul_comm r])
    (by intro a b c; simp [add_smul]) (by intro r a b; simp [mul_smul])) w =
      TensorProduct.lift ((LinearMap.lsmul F X).flip.compl₁₂ g LinearMap.id) (LinearMap.lTensor H Coalgebra.counit w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
  rw [this, h]
  simp

theorem prod_expand (t : H →ₗ[F] F) (z w : H ⊗[F] H) :
    TensorProduct.lift (LinearMap.mk₂ F (fun c1 c2 => t c2 • c1)
      (by intro a b c; simp [add_smul]) (by intro r a b; simp [smul_comm r])
      (by intro a b c; simp [add_smul]) (by intro r a b; simp [mul_smul]))
      (z * TensorProduct.map S S (TensorProduct.comm F H H w)) =
    tensorSum z (fun p1 p2 => tensorSum w (fun q1 q2 => t (p2 * S q1) • (p1 * S q2))) := by
  conv_lhs => rw [(TensorProduct.exists_finset z).choose_spec, (TensorProduct.exists_finset w).choose_spec]
  unfold tensorSum
  simp [Finset.sum_mul, Finset.mul_sum, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  rw [Finset.sum_comm]

theorem KI (t : H →ₗ[F] F) (ht : LeftIntegral t) (a y : H) :
    tensorSum (δ a) (fun a1 a2 => t (a2 * S y) • a1) =
      tensorSum (δ y) (fun y1 y2 => t (a * S y1) • y2) := by
  have e1 : ∀ y1, t (a * S y1) • (1 : H) = tensorSum (δ a) (fun p1 p2 =>
      tensorSum (δ y1) (fun q1 q2 => t (p2 * S q1) • (p1 * S q2))) := by
    intro y1
    rw [← ht (a * S y1), ts_uncurry _ (LinearMap.mk₂ F (fun c1 c2 => t c2 • c1)
      (by intro a b c; simp [add_smul]) (by intro r a b; simp [smul_comm r])
      (by intro a b c; simp [add_smul]) (by intro r a b; simp [mul_smul])) (fun _ _ => by rfl),
      Bialgebra.comul_mul, comul_antipode, prod_expand]
  have e2 : tensorSum (δ y) (fun y1 y2 => t (a * S y1) • y2) =
      tensorSum (δ y) (fun y1 y2 => (t (a * S y1) • (1 : H)) * y2) := by
    unfold tensorSum; simp
  rw [e2]
  simp only [e1]
  unfold tensorSum
  simp only [Finset.sum_mul, smul_mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  -- for fixed p: coassoc
  let Φ : H →ₗ[F] H →ₗ[F] H →ₗ[F] H := tri (fun q1 q2 y2 => t (p.2 * S q1) • (p.1 * S q2 * y2))
    (by intro a a' b c; simp [mul_add, add_smul]) (by intro r a b c; simp [mul_smul])
    (by intro a b b' c; simp [mul_add, add_mul]) (by intro r a b c; simp [smul_comm r])
    (by intro a b c c'; simp [mul_add]) (by intro r a b c; simp [smul_comm r])
  have hc := coassoc_ts (X := H) y Φ
  unfold tensorSum at hc
  simp only [Φ, tri, LinearMap.mk₂_apply, LinearMap.coe_mk, AddHom.coe_mk] at hc
  rw [← hc]
  have e3 : ∀ u z, tensorSum (δ z) (fun v w => t (p.2 * S u) • (p.1 * S v * w)) =
      Coalgebra.counit (R := F) z • (t (p.2 * S u) • p.1) := by
    intro u z
    have := anti_ts z (LinearMap.mulLeft F (t (p.2 * S u) • p.1))
    simp only [LinearMap.mulLeft_apply, mul_one] at this
    rw [← this]; unfold tensorSum; simp [mul_assoc, smul_mul_assoc]
  show _ = tensorSum (δ y) (fun u z => tensorSum (δ z) (fun v w => t (p.2 * S u) • (p.1 * S v * w)))
  simp only [e3]
  have := counit_ts y ((t ∘ₗ LinearMap.mulLeft F p.2 ∘ₗ S).smulRight p.1)
  simp only [LinearMap.smulRight_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply] at this
  exact this.symm

theorem anti_r_ts (z : H) (g : H →ₗ[F] X) :
    tensorSum (δ z) (fun v w => g (v * S w)) = Coalgebra.counit (R := F) z • g 1 := by
  rw [ts_uncurry _ ((LinearMap.mul F H).compl₁₂ LinearMap.id S |>.compr₂ g) (fun _ _ => by rfl)]
  have : TensorProduct.lift ((LinearMap.mul F H).compl₁₂ LinearMap.id S |>.compr₂ g) =
      g ∘ₗ LinearMap.mul' F H ∘ₗ LinearMap.lTensor H S := by
    apply TensorProduct.ext'; intro a b; simp
  rw [this]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [HopfAlgebra.mul_antipode_lTensor_comul_apply, Algebra.algebraMap_eq_smul_one, map_smul]

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem comod_coassoc_ts (ρ : RightComodule F H V) (x : V) (Φ : V →ₗ[F] H →ₗ[F] H →ₗ[F] X) :
    tensorSum (ρ.rho x) (fun x0 x1 => tensorSum (ρ.rho x0) (fun y k => Φ y k x1)) =
    tensorSum (ρ.rho x) (fun y p => tensorSum (δ p) (fun k x1 => Φ y k x1)) := by
  let T : (V ⊗[F] H) ⊗[F] H →ₗ[F] X := TensorProduct.lift (TensorProduct.lift Φ)
  have L1 : ∀ z : V ⊗[F] H, tensorSum z (fun x0 x1 => tensorSum (ρ.rho x0) (fun y k => Φ y k x1)) =
      T (TensorProduct.map ρ.rho LinearMap.id z) := by
    intro z
    have e : ∀ x0 x1, tensorSum (ρ.rho x0) (fun y k => Φ y k x1) = T (ρ.rho x0 ⊗ₜ[F] x1) := by
      intro x0 x1
      rw [ts_uncurry _ (LinearMap.mk₂ F (fun y k => Φ y k x1) (by simp) (by simp) (by simp) (by simp))
        (fun _ _ => by rfl)]
      induction (ρ.rho x0) using TensorProduct.induction_on with
      | zero => simp
      | tmul y k => simp [T]
      | add p q hp hq => rw [map_add, hp, hq, TensorProduct.add_tmul, map_add]
    simp only [e]
    let Ψ : V →ₗ[F] H →ₗ[F] X :=
      ((TensorProduct.mk F (V ⊗[F] H) H).compl₁₂ ρ.rho LinearMap.id).compr₂ T
    rw [ts_uncurry z Ψ (fun _ _ => by rfl)]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add p q hp hq => simp only [map_add, hp, hq]
  have L2 : ∀ z : V ⊗[F] H, tensorSum z (fun y p => tensorSum (δ p) (fun k x1 => Φ y k x1)) =
      T ((TensorProduct.assoc F V H H).symm (TensorProduct.map LinearMap.id δ z)) := by
    intro z
    have e : ∀ y p, tensorSum (δ p) (fun k x1 => Φ y k x1) =
        T ((TensorProduct.assoc F V H H).symm (y ⊗ₜ[F] δ p)) := by
      intro y p
      rw [ts_uncurry _ (Φ y) (fun _ _ => by rfl)]
      induction (δ p) using TensorProduct.induction_on with
      | zero => simp
      | tmul k x1 => simp [T]
      | add p q hp hq => rw [map_add, hp, hq, TensorProduct.tmul_add, map_add, map_add]
    simp only [e]
    let Ψ : V →ₗ[F] H →ₗ[F] X :=
      ((TensorProduct.mk F V (H ⊗[F] H)).compl₂ δ).compr₂
        (T ∘ₗ (TensorProduct.assoc F V H H).symm.toLinearMap)
    rw [ts_uncurry z Ψ (fun _ _ => by rfl)]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add p q hp hq => simp only [map_add, hp, hq]
  rw [L1, L2, ← ρ.coassoc x, LinearEquiv.symm_apply_apply]

theorem comod_counit_ts (ρ : RightComodule F H V) (x : V) (g : V →ₗ[F] X) :
    tensorSum (ρ.rho x) (fun y k => Coalgebra.counit (R := F) k • g y) = g x := by
  rw [ts_uncurry _ (LinearMap.mk₂ F (fun y k => Coalgebra.counit (R := F) k • g y)
    (by intro a b c; simp) (by intro r a b; simp [smul_comm r])
    (by intro a b c; simp [add_smul]) (by intro r a b; simp [mul_smul])) (fun _ _ => by rfl)]
  conv_rhs => rw [← ρ.counital x]
  induction (ρ.rho x) using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, map_add]

end G61S

open QAlgorithms.Papers.Independent.Next46.P22
open Classical

namespace G61L4
open G61S

variable {F H V W : Type*} [Field F] [Ring H] [HopfAlgebra F H]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

local notation "δ" => (Coalgebra.comul (R := F) (A := H))
local notation "S" => (HopfAlgebra.antipode F (A := H))

/-- Λ0 h w k = t(k S h) • w -/
def Λ0 (t : H →ₗ[F] F) (h : H) : W →ₗ[F] H →ₗ[F] W :=
  LinearMap.mk₂ F (fun w k => t (k * S h) • w)
    (by intro a b c; simp) (by intro r a b; simp [smul_comm r])
    (by intro a b c; simp [add_mul, add_smul]) (by intro r a b; simp [mul_smul])

def B (rhoW : RightComodule F H W) (t : H →ₗ[F] F) (r : V →ₗ[F] W) : V →ₗ[F] H →ₗ[F] W :=
  LinearMap.mk₂ F (fun v h => TensorProduct.lift (Λ0 t h) (rhoW.rho (r v)))
    (by intro a b c; simp) (by intro c a b; simp)
    (by
      intro v h h'
      induction (rhoW.rho (r v)) using TensorProduct.induction_on with
      | zero => simp
      | tmul w k => simp [Λ0, mul_add, add_smul]
      | add p q hp hq => simp only [map_add, hp, hq]; abel)
    (by
      intro c v h
      induction (rhoW.rho (r v)) using TensorProduct.induction_on with
      | zero => simp
      | tmul w k => simp [Λ0, mul_smul]
      | add p q hp hq => simp only [map_add, hp, hq, smul_add])

theorem avg_eq (rhoV : RightComodule F H V) (rhoW : RightComodule F H W) (t : H →ₗ[F] F)
    (r : V →ₗ[F] W) (x : V) :
    hopfAverage rhoV rhoW t r x = TensorProduct.lift (B rhoW t r) (rhoV.rho x) := by
  unfold hopfAverage averageFromCoactions
  rw [ts_uncurry _ (B rhoW t r) (fun v h => ts_uncurry _ (Λ0 t h) (fun _ _ => by rfl))]

end G61L4

open G61S

theorem G61L4.main {F H : Type*} [Field F] [Ring H] [HopfAlgebra F H]
    {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (rhoV : RightComodule F H V) (rhoW : RightComodule F H W)
    (r : V →ₗ[F] W) (t : H →ₗ[F] F) (ht : LeftIntegral t) :
    LinearFunction (F := F) (hopfAverage rhoV rhoW t r) ∧ Colinear rhoV rhoW (hopfAverage rhoV rhoW t r) ∧
    ∀ pi : W →ₗ[F] V, Colinear rhoW rhoV pi → (∀ x, pi (r x) = x) → t 1 = 1 →
      ∀ x, pi (hopfAverage rhoV rhoW t r x) = x := by
  refine ⟨⟨fun x y => ?_, fun c x => ?_⟩, ?_, ?_⟩
  · simp only [G61L4.avg_eq, map_add]
  · simp only [G61L4.avg_eq, map_smul]
  · intro x
    set Bm := G61L4.B rhoW t r
    have hB : ∀ v0 v1, Bm v0 v1 = tensorSum (rhoW.rho (r v0)) (fun w k => t (k * HopfAlgebra.antipode F v1) • w) :=
      fun v0 v1 => (ts_uncurry _ (G61L4.Λ0 t v1) (fun _ _ => by rfl)).symm
    -- RHS
    have hR : ∀ v (h : H), hopfAverage rhoV rhoW t r v ⊗ₜ[F] h =
        tensorSum (rhoV.rho v) (fun v0 v1 => Bm v0 v1 ⊗ₜ[F] h) := by
      intro v h
      rw [G61L4.avg_eq, ← ts_uncurry (rhoV.rho v) Bm (fun _ _ => rfl)]
      exact map_ts ((TensorProduct.mk F W H).flip h) _ _
    simp only [hR]
    have hc := comod_coassoc_ts rhoV x (tri (fun v0 v1 h => Bm v0 v1 ⊗ₜ[F] h)
      (by intro a a' b c; simp [TensorProduct.add_tmul]) (by intro r a b c; simp [TensorProduct.smul_tmul'])
      (by intro a b b' c; simp [TensorProduct.add_tmul]) (by intro r a b c; simp [TensorProduct.smul_tmul'])
      (by intro a b c c'; simp [TensorProduct.tmul_add]) (by intro r a b c; simp [TensorProduct.tmul_smul]))
    simp only [tri, LinearMap.mk₂_apply, LinearMap.coe_mk, AddHom.coe_mk] at hc
    rw [hc]
    -- LHS
    unfold hopfAverage averageFromCoactions
    rw [map_ts]
    have P : ∀ x0 x1, rhoW.rho (tensorSum (rhoW.rho (r x0)) (fun w k => t (k * HopfAlgebra.antipode F x1) • w)) =
        tensorSum (Coalgebra.comul (R := F) x1) (fun v1 h => Bm x0 v1 ⊗ₜ[F] h) := by
      intro x0 x1
      rw [map_ts]
      have e1 : ∀ w k, rhoW.rho (t (k * HopfAlgebra.antipode F x1) • w) =
          tensorSum (rhoW.rho w) (fun w0 w1 => t (k * HopfAlgebra.antipode F x1) • (w0 ⊗ₜ[F] w1)) := by
        intro w k
        rw [map_smul]
        conv_lhs => rw [← ts_self (rhoW.rho w)]
        unfold tensorSum
        rw [Finset.smul_sum]
      simp only [e1]
      have hc2 := comod_coassoc_ts rhoW (r x0) (tri (fun w0 w1 k => t (k * HopfAlgebra.antipode F x1) • (w0 ⊗ₜ[F] w1))
        (by intro a a' b c; simp [TensorProduct.add_tmul]) (by intro r a b c; simp [TensorProduct.smul_tmul', smul_comm r])
        (by intro a b b' c; simp [TensorProduct.tmul_add]) (by intro r a b c; simp [TensorProduct.tmul_smul, smul_comm r])
        (by intro a b c c'; simp [add_mul, add_smul]) (by intro r a b c; simp [mul_smul]))
      simp only [tri, LinearMap.mk₂_apply, LinearMap.coe_mk, AddHom.coe_mk] at hc2
      rw [hc2]
      simp only [hB]
      have e2 : ∀ (v1 h : H), tensorSum (rhoW.rho (r x0)) (fun w k => t (k * HopfAlgebra.antipode F v1) • w) ⊗ₜ[F] h =
          tensorSum (rhoW.rho (r x0)) (fun w k => (t (k * HopfAlgebra.antipode F v1) • w) ⊗ₜ[F] h) :=
        fun v1 h => map_ts ((TensorProduct.mk F W H).flip h) _ _
      simp only [e2]
      unfold tensorSum
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      have k := KI t ht q.2 x1
      have k2 := congrArg (TensorProduct.mk F W H q.1) k
      rw [map_ts (TensorProduct.mk F W H q.1), map_ts (TensorProduct.mk F W H q.1)] at k2
      unfold tensorSum at k2
      simp only [TensorProduct.mk_apply, TensorProduct.tmul_smul] at k2
      dsimp only
      simp only [TensorProduct.smul_tmul']
      exact k2
    simp only [P]
  · intro pi hpi hpr ht1 x
    unfold hopfAverage averageFromCoactions
    rw [map_ts]
    have e : ∀ v h, pi (tensorSum (rhoW.rho (r v)) (fun w k => t (k * HopfAlgebra.antipode F h) • w)) =
        tensorSum (rhoV.rho v) (fun y k => t (k * HopfAlgebra.antipode F h) • y) := by
      intro v h
      conv_rhs => rw [← hpr v]
      rw [ts_uncurry (rhoV.rho (pi (r v))) (G61L4.Λ0 t h) (fun _ _ => by rfl), hpi (r v), map_ts]
      unfold tensorSum
      rw [map_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp [G61L4.Λ0]
    simp only [e]
    have hc := comod_coassoc_ts rhoV x (tri (fun y k h => t (k * HopfAlgebra.antipode F h) • y)
      (by intro a a' b c; simp) (by intro r a b c; simp [smul_comm r])
      (by intro a b b' c; simp [add_mul, add_smul]) (by intro r a b c; simp [mul_smul])
      (by intro a b c c'; simp [mul_add, add_smul]) (by intro r a b c; simp [mul_smul]))
    simp only [tri, LinearMap.mk₂_apply, LinearMap.coe_mk, AddHom.coe_mk] at hc
    rw [hc]
    have e2 : ∀ (y : V) (p : H), tensorSum (Coalgebra.comul (R := F) p)
        (fun k h => t (k * HopfAlgebra.antipode F h) • y) = Coalgebra.counit (R := F) p • y := by
      intro y p
      have := anti_r_ts p (t.smulRight y)
      simp only [LinearMap.smulRight_apply, ht1, one_smul] at this
      exact this
    simp only [e2]
    exact comod_counit_ts rhoV x LinearMap.id



open G61S in
theorem G61L8.lie {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
    {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [LieRingModule L V] [LieModule F L V] [LieRingModule L W] [LieModule F L W]
    (rhoL : RightComodule F H L)
    (rhoV : RightComodule F H V) (hV : CoCompatible rhoL rhoV)
    (rhoW : RightComodule F H W) (hW : CoCompatible rhoL rhoW)
    (pi : V →ₗ[F] W) (hpi : LieIntertwiner (L := L) pi)
    (t : H →ₗ[F] F) (had : AdInvariant t) :
    LieIntertwiner (L := L) (hopfAverage rhoV rhoW t pi) := by
  intro a v
  set Bm := G61L4.B rhoW t pi
  have hB : ∀ v0 v1, Bm v0 v1 = tensorSum (rhoW.rho (pi v0)) (fun w k => t (k * HopfAlgebra.antipode F v1) • w) :=
    fun v0 v1 => (ts_uncurry _ (G61L4.Λ0 t v1) (fun _ _ => by rfl)).symm
  let ad : W →ₗ[F] W := LieModule.toEnd F L W a
  -- RHS
  have hR : ⁅a, hopfAverage rhoV rhoW t pi v⁆ = tensorSum (rhoV.rho v) (fun v0 v1 =>
      tensorSum (rhoW.rho (pi v0)) (fun w0 w1 => t (w1 * HopfAlgebra.antipode F v1) • ⁅a, w0⁆)) := by
    rw [G61L4.avg_eq, ← ts_uncurry (rhoV.rho v) Bm (fun _ _ => rfl)]
    unfold tensorSum
    rw [lie_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    dsimp only
    rw [hB]
    unfold tensorSum
    rw [lie_sum]
    refine Finset.sum_congr rfl (fun q' _ => ?_)
    rw [lie_smul]
  rw [hR, G61L4.avg_eq, hV a v, map_ts]
  have e1 : ∀ (a0 : L) (a1 : H), TensorProduct.lift (G61L4.B rhoW t pi)
      (tensorSum (rhoV.rho v) (fun v0 v1 => ⁅a0, v0⁆ ⊗ₜ[F] (a1 * v1))) =
      tensorSum (rhoV.rho v) (fun v0 v1 => G61L4.B rhoW t pi ⁅a0, v0⁆ (a1 * v1)) := by
    intro a0 a1; rw [map_ts]; rfl
  simp only [e1]
  have Q : ∀ (v0 : V) (v1 : H), tensorSum (rhoL.rho a) (fun a0 a1 => G61L4.B rhoW t pi ⁅a0, v0⁆ (a1 * v1)) =
      tensorSum (rhoW.rho (pi v0)) (fun w0 w1 => t (w1 * HopfAlgebra.antipode F v1) • ⁅a, w0⁆) := by
    intro v0 v1
    have e2 : ∀ (a0 : L) (a1 : H), G61L4.B rhoW t pi ⁅a0, v0⁆ (a1 * v1) =
        tensorSum (rhoL.rho a0) (fun b0 b1 => tensorSum (rhoW.rho (pi v0)) (fun w0 w1 =>
          t (b1 * w1 * HopfAlgebra.antipode F (a1 * v1)) • ⁅b0, w0⁆)) := by
      intro a0 a1
      show TensorProduct.lift (G61L4.Λ0 t (a1 * v1)) (rhoW.rho (pi ⁅a0, v0⁆)) = _
      rw [hpi a0 v0, hW a0 (pi v0)]
      unfold tensorSum
      rw [map_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      dsimp only
      rw [map_sum]
      refine Finset.sum_congr rfl (fun p' _ => ?_)
      simp [G61L4.Λ0, mul_assoc]
    simp only [e2]
    have W1 : ∀ (w0 : W) (w1 : H), tensorSum (rhoL.rho a) (fun a0 a1 => tensorSum (rhoL.rho a0)
        (fun b0 b1 => t (b1 * w1 * HopfAlgebra.antipode F (a1 * v1)) • ⁅b0, w0⁆)) =
        t (w1 * HopfAlgebra.antipode F v1) • ⁅a, w0⁆ := by
      intro w0 w1
      set c := w1 * HopfAlgebra.antipode F v1 with hc
      have e3 : ∀ a1 b1 : H, b1 * w1 * HopfAlgebra.antipode F (a1 * v1) =
          b1 * c * HopfAlgebra.antipode F a1 := by
        intro a1 b1; rw [HopfAlgebra.antipode_mul_antidistrib, hc]; simp [mul_assoc]
      simp only [e3]
      have hcc := comod_coassoc_ts rhoL a (tri (fun y k x1 => t (k * c * HopfAlgebra.antipode F x1) • ⁅y, w0⁆)
        (by intro a a' b c; simp [add_lie]) (by intro r a b c; simp [smul_lie, smul_comm r])
        (by intro a b b' c; simp [add_mul, add_smul]) (by intro r a b c; simp [mul_smul])
        (by intro a b c c'; simp [mul_add, add_smul]) (by intro r a b c; simp [mul_smul]))
      simp only [tri, LinearMap.mk₂_apply, LinearMap.coe_mk, AddHom.coe_mk] at hcc
      rw [hcc]
      have e4 : ∀ (y : L) (p : H), tensorSum (Coalgebra.comul (R := F) p)
          (fun k x1 => t (k * c * HopfAlgebra.antipode F x1) • ⁅y, w0⁆) =
          Coalgebra.counit (R := F) p • (t c • ⁅y, w0⁆) := by
        intro y p
        have := had p c
        rw [← mul_smul, ← this]
        unfold tensorSum
        rw [Finset.sum_smul]
      simp only [e4]
      exact comod_counit_ts rhoL a
        { toFun := fun y => t c • ⁅y, w0⁆
          map_add' := by intro x y; simp [add_lie]
          map_smul' := by intro r x; simp [smul_lie, smul_comm r] }
    simp only [← W1]
    unfold tensorSum
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact Finset.sum_comm
  have swap : tensorSum (rhoL.rho a) (fun a0 a1 => tensorSum (rhoV.rho v)
      (fun v0 v1 => G61L4.B rhoW t pi ⁅a0, v0⁆ (a1 * v1))) =
      tensorSum (rhoV.rho v) (fun v0 v1 => tensorSum (rhoL.rho a)
      (fun a0 a1 => G61L4.B rhoW t pi ⁅a0, v0⁆ (a1 * v1))) := by
    unfold tensorSum; exact Finset.sum_comm
  rw [swap]
  simp only [Q]


namespace G61D

theorem insert_indep {α : Type*} [CompleteLattice α] [IsModularLattice α]
    (S' : Set α) (W : α) (h : sSupIndep S') (hd : Disjoint W (sSup S')) (hW : W ∉ S') :
    sSupIndep (insert W S') := by
  intro a ha
  rcases ha with rfl | ha
  · rw [Set.insert_sdiff_of_mem _ (Set.mem_singleton _), Set.sdiff_singleton_eq_self hW]; exact hd
  · have haW : a ≠ W := fun e => hW (e ▸ ha)
    rw [Set.insert_sdiff_of_notMem _ (by simpa using haW.symm), sSup_insert]
    have h1 : Disjoint a (sSup (S' \ {a})) := h ha
    have h2 : Disjoint (a ⊔ sSup (S' \ {a})) W := by
      refine Disjoint.symm (hd.mono_right (sup_le (le_sSup ha) (sSup_le_sSup Set.sdiff_subset)))
    rw [sup_comm]
    exact h1.disjoint_sup_right_of_disjoint_sup_left h2

theorem decomp_exists {F V L : Type*} [Field F] [AddCommGroup V] [Module F V] [LieRing L] [LieAlgebra F L]
    [LieRingModule L V] [LieModule F L V] [FiniteDimensional F V] (stable : Submodule F V → Prop)
    (hcompl : ∀ U W : Submodule F V, LieStable (L := L) U → stable U → W ≤ U → LieStable (L := L) W →
      stable W → ∃ W' : Submodule F V, W' ≤ U ∧ LieStable (L := L) W' ∧ stable W' ∧
        Disjoint W W' ∧ W ⊔ W' = U) :
    ∀ n (U : Submodule F V), Module.finrank F U = n → LieStable (L := L) U → stable U →
      ∃ S : Finset (Submodule F V), sSupIndep (S : Set (Submodule F V)) ∧ sSup (S : Set (Submodule F V)) = U ∧
        ∀ P ∈ S, IrreducibleIn (L := L) (stable) P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU hUg
  by_cases hU0 : U = ⊥
  · exact ⟨∅, by simp, by simp [hU0], by simp⟩
  -- minimal nonzero stable graded W ≤ U
  have hex : ∃ k, ∃ W : Submodule F V, W ≤ U ∧ W ≠ ⊥ ∧ LieStable (L := L) W ∧ stable W ∧
      Module.finrank F W = k := ⟨_, U, le_rfl, hU0, hU, hUg, rfl⟩
  obtain ⟨W, hWU, hW0, hW, hWg, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ W2 : Submodule F V, W2 ≤ U → W2 ≠ ⊥ → LieStable (L := L) W2 → stable W2 →
      Nat.find hex ≤ Module.finrank F W2 := fun W2 a b c d => Nat.find_min' hex ⟨W2, a, b, c, d, rfl⟩
  have hirr : IrreducibleIn (L := L) (stable) W := by
    refine ⟨hW, hWg, fun W2 h2 hs hg => ?_⟩
    by_cases h20 : W2 = ⊥
    · exact Or.inl h20
    · right
      exact Submodule.eq_of_le_of_finrank_le h2 (hWk ▸ hmin W2 (h2.trans hWU) h20 hs hg)
  obtain ⟨W', hW'U, hW', hW'g, hdis, hsup⟩ := hcompl U W hU hUg hWU hW hWg
  have hdim : Module.finrank F W' < n := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W W'
    rw [hsup, hdis.eq_bot, finrank_bot, add_zero] at this
    have hpos : 0 < Module.finrank F W :=
      Nat.pos_of_ne_zero (fun h => hW0 (Submodule.finrank_eq_zero.mp h))
    omega
  obtain ⟨S', hS'i, hS's, hS'irr⟩ := ih _ hdim W' rfl hW' hW'g
  have hWS' : W ∉ S' := by
    intro hm
    have : W ≤ W' := hS's ▸ le_sSup (Finset.mem_coe.mpr hm)
    exact hW0 (by rw [← inf_eq_left.mpr this, hdis.eq_bot])
  refine ⟨insert W S', ?_, ?_, ?_⟩
  · rw [Finset.coe_insert]
    exact insert_indep _ W hS'i (hS's ▸ hdis) (by simpa using hWS')
  · rw [Finset.coe_insert, sSup_insert, hS's, hsup]
  · intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hirr
    · exact hS'irr P hP


end G61D

namespace G61C
open G61S

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
  {V : Type*} [AddCommGroup V] [Module F V] [LieRingModule L V] [LieModule F L V]

theorem costable_iff (rho : RightComodule F H V) (X : Submodule F V) (z : V ⊗[F] H)
    (hz : z ∈ coactionTensorImage X) (Φ : V →ₗ[F] H →ₗ[F] V) (hΦ : ∀ x ∈ X, ∀ h, Φ x h ∈ X) :
    TensorProduct.lift Φ z ∈ X := by
  unfold coactionTensorImage at hz
  induction hz using Submodule.span_induction with
  | mem y hy => obtain ⟨x, hx, h, rfl⟩ := hy; simpa using hΦ x hx h
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact X.add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact X.smul_mem c ha

theorem proj (rhoL : RightComodule F H L) (rhoV : RightComodule F H V) (hV : CoCompatible rhoL rhoV)
    (t : H →ₗ[F] F) (ht : NormalizedAdIntegral t) (hcr : CompletelyReducible F L V)
    (X : Submodule F V) (hX : LieStable (L := L) X) (hXc : CoStable rhoV X) :
    ∃ q : V →ₗ[F] V, (∀ v, rhoV.rho (q v) = TensorProduct.map q LinearMap.id (rhoV.rho v)) ∧
      (∀ (a : L) v, q ⁅a, v⁆ = ⁅a, q v⁆) ∧ (∀ v, q v ∈ X) ∧ (∀ x ∈ X, q x = x) := by
  obtain ⟨C, hC, hXC⟩ := hcr X hX
  let p : V →ₗ[F] V := X.projection C hXC
  have hp_mem : ∀ v, p v ∈ X := fun v => Submodule.projection_apply_mem hXC v
  have hp_id : ∀ w ∈ X, p w = w := fun w hw => Submodule.projection_apply_of_mem_left hXC hw
  have hp_C : ∀ c ∈ C, p c = 0 := fun c hc => Submodule.projection_apply_of_mem_right hXC hc
  have hp_lie : ∀ (a : L) v, p ⁅a, v⁆ = ⁅a, p v⁆ := by
    intro a v
    have hs : v - p v ∈ C := Submodule.sub_projection_mem hXC v
    have : ⁅a, v⁆ = ⁅a, p v⁆ + ⁅a, v - p v⁆ := by rw [← lie_add]; congr 1; abel
    rw [this, map_add, hp_id _ (hX a _ (hp_mem v)), hp_C _ (hC a _ hs), add_zero]
  let q : V →ₗ[F] V := TensorProduct.lift (G61L4.B rhoV t p) ∘ₗ rhoV.rho
  have hq : ∀ v, q v = hopfAverage rhoV rhoV t p v := fun v => (G61L4.avg_eq rhoV rhoV t p v).symm
  obtain ⟨-, hcol, -⟩ := G61L4.main rhoV rhoV p t ht.1
  have hlie := G61L8.lie (L := L) rhoL rhoV hV rhoV hV p hp_lie t ht.2.1
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [hq, hcol v, ts_uncurry _ ((TensorProduct.mk F V H).compl₁₂ q LinearMap.id)
      (fun a b => by simp [hq])]
    rfl
  · intro a v; rw [hq, hq, hlie a v]
  · intro v
    show TensorProduct.lift (G61L4.B rhoV t p) (rhoV.rho v) ∈ X
    induction (rhoV.rho v) using TensorProduct.induction_on with
    | zero => simp
    | tmul v0 v1 =>
      simp only [TensorProduct.lift.tmul]
      show TensorProduct.lift (G61L4.Λ0 t v1) (rhoV.rho (p v0)) ∈ X
      exact costable_iff rhoV X _ (hXc _ (hp_mem v0)) _ (fun x hx h => by
        simp only [G61L4.Λ0, LinearMap.mk₂_apply]; exact X.smul_mem _ hx)
    | add a b ha hb => rw [map_add]; exact X.add_mem ha hb
  · intro x hx
    have hid := (G61L4.main rhoV rhoV LinearMap.id t ht.1).2.2 LinearMap.id
      (fun v => by
        show rhoV.rho v = tensorSum (rhoV.rho v) (fun a b => a ⊗ₜ[F] b)
        exact (ts_self _).symm) (fun _ => rfl) ht.2.2 x
    rw [LinearMap.id_apply, G61L4.avg_eq] at hid
    show TensorProduct.lift (G61L4.B rhoV t p) (rhoV.rho x) = x
    conv_rhs => rw [← hid]
    have hz := hXc x hx
    unfold coactionTensorImage at hz
    generalize rhoV.rho x = z at hz ⊢
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x', hx', h, rfl⟩ := hy
      simp only [TensorProduct.lift.tmul]
      show TensorProduct.lift (G61L4.Λ0 t h) (rhoV.rho (p x')) =
        TensorProduct.lift (G61L4.Λ0 t h) (rhoV.rho (LinearMap.id x'))
      rw [hp_id x' hx', LinearMap.id_apply]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ha]

end G61C

open G61S in
theorem solution {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
    {V : Type*} [AddCommGroup V] [Module F V] [LieRingModule L V] [LieModule F L V]
    [CharZero F] [FiniteDimensional F V]
    (rhoL : RightComodule F H L) (hr : ComoduleLie rhoL)
    (rhoV : RightComodule F H V) (hV : CoCompatible rhoL rhoV)
    (t : H →ₗ[F] F) (ht : NormalizedAdIntegral t)
    (hcr : CompletelyReducible F L V) :
    IrreducibleDecomposition (L := L) (CoStable rhoV) := by
  have hcompl : ∀ U W : Submodule F V, LieStable (L := L) U → CoStable rhoV U → W ≤ U →
      LieStable (L := L) W → CoStable rhoV W → ∃ W' : Submodule F V, W' ≤ U ∧
        LieStable (L := L) W' ∧ CoStable rhoV W' ∧ Disjoint W W' ∧ W ⊔ W' = U := by
    intro U W hU hUc hWU hW hWc
    obtain ⟨qU, cU, lU, mU, iU⟩ := G61C.proj rhoL rhoV hV t ht hcr U hU hUc
    obtain ⟨qW, cW, lW, mW, iW⟩ := G61C.proj rhoL rhoV hV t ht hcr W hW hWc
    let f : V →ₗ[F] V := (LinearMap.id - qW) ∘ₗ qU
    have hf : ∀ v, f v = qU v - qW (qU v) := fun v => rfl
    refine ⟨LinearMap.range f, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨v, rfl⟩
      rw [hf]; exact U.sub_mem (mU v) (hWU (mW _))
    · rintro a _ ⟨v, rfl⟩
      refine ⟨⁅a, v⁆, ?_⟩
      rw [hf, hf, lU, lW, lie_sub]
    · rintro _ ⟨v, rfl⟩
      have hcf : rhoV.rho (f v) = TensorProduct.map f LinearMap.id (rhoV.rho v) := by
        rw [hf, map_sub, cW, cU]
        induction (rhoV.rho v) using TensorProduct.induction_on with
        | zero => simp
        | tmul y h => simp [hf, TensorProduct.sub_tmul]
        | add a b ha hb => simp only [map_add] at ha hb ⊢; rw [← ha, ← hb]; abel
      rw [hcf]
      unfold coactionTensorImage
      induction (rhoV.rho v) using TensorProduct.induction_on with
      | zero => simp
      | tmul y h => exact Submodule.subset_span ⟨f y, ⟨y, rfl⟩, h, by simp⟩
      | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    · rw [Submodule.disjoint_def]
      rintro x hx ⟨v, rfl⟩
      have h1 : qW (f v) = 0 := by rw [hf, map_sub, iW _ (mW _), sub_self]
      rw [← iW _ hx, h1]
    · apply le_antisymm
      · refine sup_le hWU ?_
        rintro _ ⟨v, rfl⟩
        rw [hf]; exact U.sub_mem (mU v) (hWU (mW _))
      · intro u hu
        rw [Submodule.mem_sup]
        refine ⟨qW u, mW u, f u, ⟨u, rfl⟩, ?_⟩
        rw [hf, iU u hu]; abel
  have htop : CoStable rhoV ⊤ := by
    intro v _
    unfold coactionTensorImage
    have : Submodule.span F {z : V ⊗[F] H | ∃ v ∈ (⊤ : Submodule F V), ∃ h : H, z = v ⊗ₜ[F] h} = ⊤ := by
      rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top]
      apply Submodule.span_mono
      rintro _ ⟨a, b, rfl⟩
      exact ⟨a, Submodule.mem_top, b, rfl⟩
    rw [this]; exact Submodule.mem_top
  obtain ⟨S, hSi, hSs, hSirr⟩ := G61D.decomp_exists (CoStable rhoV) hcompl _ ⊤ rfl
    (fun a v _ => Submodule.mem_top) htop
  let e := S.equivFin
  refine ⟨S.card, fun i => (e.symm i).1, ?_, ?_, fun i => hSirr _ (e.symm i).2⟩
  · exact ((sSupIndep_iff _).mp hSi).comp e.symm.injective
  · rw [← hSs, sSup_eq_iSup']
    exact (e.symm.iSup_comp (g := fun x : (S : Set (Submodule F V)) => x.1))
