-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.example6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:58:17.837522+00:00
-- url     : https://prove2.me/submissions/3fd5b565-4f0f-474f-99da-fa8ea7f801ae

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

theorem g61a_ts_sum {F A B X : Type*} [Field F]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup X] [Module F X]
    (f : A → B → X)
    (h1 : ∀ a a' b, f (a + a') b = f a b + f a' b) (h2 : ∀ (c : F) a b, f (c • a) b = c • f a b)
    (h3 : ∀ a b b', f a (b + b') = f a b + f a b') (h4 : ∀ (c : F) a b, f a (c • b) = c • f a b)
    {ι : Type*} (s : Finset ι) (a : ι → A) (b : ι → B) :
    tensorSum (∑ i ∈ s, a i ⊗ₜ[F] b i) f = ∑ i ∈ s, f (a i) (b i) := by
  rw [G61P.ts_eq _ f (LinearMap.mk₂ F f h1 h2 h3 h4) (fun _ _ => rfl)]
  simp [map_sum]

theorem g61a_homog_single {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (D : Grading F G V) (g : G) (v : V) (hv : Homogeneous D g v) : D.decomp v = Finsupp.single g v := by
  ext h
  rw [Finsupp.single_apply]
  split_ifs with hgh
  · subst hgh; exact hv
  · have := D.offDiagonal v g h (Ne.symm hgh)
    rw [hv] at this; exact this

theorem g61a_gc_homog {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (D : Grading F G V) (g : G) (v : V) (hv : Homogeneous D g v) :
    gradedCoaction D v = v ⊗ₜ[F] MonoidAlgebra.single g 1 := by
  unfold gradedCoaction
  rw [g61a_homog_single D g v hv, Finsupp.sum_single_index (by simp)]

/-- graded coaction as a linear map -/
noncomputable def g61a_gcL {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (D : Grading F G V) : V →ₗ[F] V ⊗[F] MonoidAlgebra F G where
  toFun := gradedCoaction D
  map_add' x y := by
    unfold gradedCoaction
    rw [map_add, Finsupp.sum_add_index']
    · intro g; simp
    · intro g a b; simp [TensorProduct.add_tmul]
  map_smul' c x := by
    unfold gradedCoaction
    rw [map_smul, Finsupp.sum_smul_index', Finsupp.smul_sum]
    · simp [TensorProduct.smul_tmul']
    · intro g; simp

theorem g61a_gc_sum {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (D : Grading F G V) (v : V) :
    gradedCoaction D v = ∑ g ∈ (D.decomp v).support,
      D.decomp v g ⊗ₜ[F] MonoidAlgebra.single g (1 : F) := rfl

theorem solution {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    {G : Type*} [Group G] (D : Grading F G L) (hD : GradedLie D) :
    ∃ rho : RightComodule F (MonoidAlgebra F G) L,
      (∀ v, rho.rho v = gradedCoaction D v) ∧ ComoduleLie rho ∧
      ∀ g a, Homogeneous D g a → rho.rho a = a ⊗ₜ[F] MonoidAlgebra.single g 1 := by
  have hom : ∀ v g, Homogeneous D g (D.decomp v g) := fun v g => D.diagonal v g
  refine ⟨⟨g61a_gcL D, ?_, ?_⟩, fun v => rfl, ?_, fun g a ha => g61a_gc_homog D g a ha⟩
  · intro x
    show TensorProduct.assoc F L _ _ (TensorProduct.map (g61a_gcL D) LinearMap.id
      (gradedCoaction D x)) = TensorProduct.map LinearMap.id (Coalgebra.comul (R := F)) (gradedCoaction D x)
    simp only [g61a_gc_sum D x, map_sum, TensorProduct.map_tmul, LinearMap.id_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    show TensorProduct.assoc F _ _ _ (gradedCoaction D (D.decomp x g) ⊗ₜ[F] _) = _
    rw [g61a_gc_homog D g _ (hom x g)]
    simp
  · intro x
    show TensorProduct.rid F L (TensorProduct.map LinearMap.id (Coalgebra.counit (R := F))
      (gradedCoaction D x)) = x
    simp only [g61a_gc_sum D x, map_sum, TensorProduct.map_tmul, LinearMap.id_apply]
    simp
    conv_rhs => rw [← D.total x]
    rfl
  · intro a b
    show gradedCoaction D ⁅a, b⁆ = tensorSum (gradedCoaction D a) (fun a0 a1 =>
      tensorSum (gradedCoaction D b) (fun b0 b1 => ⁅a0, b0⁆ ⊗ₜ[F] (a1 * b1)))
    have inner : ∀ (a0 : L) (a1 : MonoidAlgebra F G),
        tensorSum (gradedCoaction D b) (fun b0 b1 => ⁅a0, b0⁆ ⊗ₜ[F] (a1 * b1)) =
        ∑ h ∈ (D.decomp b).support, ⁅a0, D.decomp b h⁆ ⊗ₜ[F] (a1 * MonoidAlgebra.single h 1) := by
      intro a0 a1
      rw [g61a_gc_sum D b, g61a_ts_sum]
      · intro x y z; simp [lie_add, TensorProduct.add_tmul]
      · intro c x y; simp [lie_smul, TensorProduct.smul_tmul']
      · intro x y z; simp [mul_add, TensorProduct.tmul_add]
      · intro c x y; simp [mul_smul_comm, TensorProduct.tmul_smul]
    simp_rw [inner]
    rw [g61a_gc_sum D a, g61a_ts_sum]
    · have hab : ⁅a, b⁆ = ∑ g ∈ (D.decomp a).support, ∑ h ∈ (D.decomp b).support,
          ⁅D.decomp a g, D.decomp b h⁆ := by
        conv_lhs => rw [← D.total a, ← D.total b]
        simp only [Finsupp.sum, sum_lie, lie_sum]
        exact Finset.sum_comm
      rw [hab]
      change g61a_gcL D _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      change gradedCoaction D _ = _
      rw [g61a_gc_homog D (g * h) _ (hD g h _ _ (hom a g) (hom b h)),
        MonoidAlgebra.single_mul_single, mul_one]
    · intro x y z; simp [add_lie, TensorProduct.add_tmul, Finset.sum_add_distrib]
    · intro c x y; simp [smul_lie, TensorProduct.smul_tmul', Finset.smul_sum]
    · intro x y z; simp [add_mul, TensorProduct.tmul_add, Finset.sum_add_distrib]
    · intro c x y; simp [smul_mul_assoc, TensorProduct.tmul_smul, Finset.smul_sum]
