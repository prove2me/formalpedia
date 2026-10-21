-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.remark_graded_average
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:49:35.33898+00:00
-- url     : https://prove2.me/submissions/a16448a7-dd46-4754-a800-e0a9407e3092

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

theorem g61a_idc {F G : Type*} [Field F] [Group G] (g : G) (c : F) :
    identityCoefficient (F := F) (G := G) (MonoidAlgebra.single g c) = if g = 1 then c else 0 := by
  simp [identityCoefficient, MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- inner contraction for the graded coaction -/
theorem g61a_inner {F G W : Type*} [Field F] [Group G] [AddCommGroup W] [Module F W]
    (E : Grading F G W) (w : W) (h : MonoidAlgebra F G) :
    tensorSum (gradedCoaction E w) (fun w' k =>
        identityCoefficient (F := F) (G := G) (k * HopfAlgebra.antipode F h) • w') =
      (E.decomp w).sum (fun k x =>
        identityCoefficient (F := F) (G := G) (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F h) • x) := by
  unfold gradedCoaction Finsupp.sum
  rw [g61a_ts_sum]
  · intro a a' b; rw [smul_add]
  · intro c a b; rw [smul_comm]
  · intro a b b'; rw [add_mul, map_add, add_smul]
  · intro c a b; rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_smul]

theorem g61a_avg_add {F G V W : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (D : Grading F G V) (E : Grading F G W) (r : V →ₗ[F] W) :
    LinearFunction (F := F) (gradedAverage D E r) := by
  constructor
  · intro x y
    unfold gradedAverage
    rw [map_add, Finsupp.sum_add_index']
    · intro g; simp
    · intro g a b; simp
  · intro c x
    unfold gradedAverage
    rw [map_smul, Finsupp.sum_smul_index', Finsupp.smul_sum]
    · simp
    · intro g; simp

theorem g61a_homog_single {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (D : Grading F G V) (g : G) (v : V) (hv : Homogeneous D g v) : D.decomp v = Finsupp.single g v := by
  ext h
  rw [Finsupp.single_apply]
  split_ifs with hgh
  · subst hgh; exact hv
  · have := D.offDiagonal v g h (Ne.symm hgh)
    rw [hv] at this; exact this

theorem solution {F : Type*} [Field F] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {G : Type*} [Group G]
    (D : Grading F G V) (E : Grading F G W) (r : V →ₗ[F] W) :
    (∀ x, averageFromCoactions (gradedCoaction D) (gradedCoaction E)
      (identityCoefficient (F := F) (G := G)) r x = gradedAverage D E r x) ∧
    LinearFunction (F := F) (gradedAverage D E r) ∧ GradedMap D E (gradedAverage D E r) := by
  refine ⟨fun x => ?_, g61a_avg_add D E r, ?_⟩
  · unfold averageFromCoactions
    simp_rw [g61a_inner]
    let t := identityCoefficient (F := F) (G := G)
    have h1 : ∀ (a a' : V) (b : MonoidAlgebra F G),
        (E.decomp (r (a + a'))).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F b) • x)
        = (E.decomp (r a)).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F b) • x)
          + (E.decomp (r a')).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F b) • x) := by
      intro a a' b
      rw [map_add, map_add, Finsupp.sum_add_index']
      · intro g; simp
      · intro g a b; simp [smul_add]
    have h2 : ∀ (c : F) (a : V) (b : MonoidAlgebra F G),
        (E.decomp (r (c • a))).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F b) • x)
        = c • (E.decomp (r a)).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F b) • x) := by
      intro c a b
      rw [map_smul, map_smul, Finsupp.sum_smul_index', Finsupp.smul_sum]
      · exact Finsupp.sum_congr fun k _ => smul_comm _ _ _
      · intro g; simp
    have h3 : ∀ (a : V) (b b' : MonoidAlgebra F G),
        (E.decomp (r a)).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F (b + b')) • x)
        = (E.decomp (r a)).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F b) • x)
          + (E.decomp (r a)).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F b') • x) := by
      intro a b b'
      rw [← Finsupp.sum_add]
      exact Finsupp.sum_congr fun k _ => by rw [map_add, mul_add, map_add, add_smul]
    have h4 : ∀ (c : F) (a : V) (b : MonoidAlgebra F G),
        (E.decomp (r a)).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F (c • b)) • x)
        = c • (E.decomp (r a)).sum (fun k x => t (MonoidAlgebra.single k 1 * HopfAlgebra.antipode F b) • x) := by
      intro c a b
      rw [Finsupp.smul_sum]
      exact Finsupp.sum_congr fun k _ => by rw [map_smul, mul_smul_comm, map_smul, smul_eq_mul, mul_smul]
    unfold gradedCoaction gradedAverage
    rw [Finsupp.sum, Finsupp.sum, g61a_ts_sum _ h1 h2 h3 h4]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [MonoidAlgebra.single_mul_single, g61a_idc, t, Finsupp.sum]
    simp_rw [mul_inv_eq_one]
    rw [Finset.sum_ite_eq']
    split_ifs with hg
    · rfl
    · exact (Finsupp.notMem_support_iff.mp hg).symm
  · intro g v hv
    unfold gradedAverage
    rw [g61a_homog_single D g v hv, Finsupp.sum_single_index (by simp)]
    exact E.diagonal _ _
