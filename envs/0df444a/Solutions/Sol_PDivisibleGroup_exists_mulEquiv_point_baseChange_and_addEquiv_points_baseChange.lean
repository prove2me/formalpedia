-- Prove2me | solution 1 for PDivisibleGroup.exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/88247dfc-0457-5f6a-9342-c3f9af583d74

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange

set_option autoImplicit false

open scoped TensorProduct

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "transition level Point Point.toAlgHom Point.ofAlgHom Point.ext Point.mul_apply pointIncl pointIncl_apply pointInclLE pointInclLE_self pointInclLE_succ pointsDirectedSystemMap Points pointsMkAdd Points.induction_on pointMap toAlgHom_pointMap Points.smul_pointsMkAdd baseChange"
namespace PointsBC
p2m_open "PDivisibleGroup"

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
  (S : Type) [CommRing S] [Algebra R S] [Nontrivial S]
  (L : Type) [CommRing L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]

noncomputable def toAlgHom' {v : ℕ} (y : (G.baseChange S).Point L v) : S ⊗[R] G.level v →ₐ[S] L := Point.toAlgHom y

noncomputable def ofAlgHom' {v : ℕ} (g : S ⊗[R] G.level v →ₐ[S] L) : (G.baseChange S).Point L v := Point.ofAlgHom g

@[scoped simp] theorem toAlgHom'_ofAlgHom' {v : ℕ} (g : S ⊗[R] G.level v →ₐ[S] L) : toAlgHom' G S L (ofAlgHom' G S L g) = g := rfl
@[scoped simp] theorem ofAlgHom'_toAlgHom' {v : ℕ} (y : (G.baseChange S).Point L v) : ofAlgHom' G S L (toAlgHom' G S L y) = y := rfl

theorem ext' {v : ℕ} {y y' : (G.baseChange S).Point L v} (hyy : ∀ z, toAlgHom' G S L y z = toAlgHom' G S L y' z) : y = y' :=
  Point.ext hyy

noncomputable def fwd (v : ℕ) (x : G.Point L v) : (G.baseChange S).Point L v :=
  ofAlgHom' G S L (Algebra.TensorProduct.lift (Algebra.ofId S L) (Point.toAlgHom x) (fun _ _ => Commute.all _ _))

noncomputable def bwd (v : ℕ) (y : (G.baseChange S).Point L v) : G.Point L v :=
  Point.ofAlgHom (((toAlgHom' G S L y).restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : G.level v →ₐ[R] S ⊗[R] G.level v))

variable {S L}

@[scoped simp] theorem fwd_apply_tmul (v : ℕ) (x : G.Point L v) (s : S) (a : G.level v) :
    toAlgHom' G S L (fwd G S L v x) (s ⊗ₜ[R] a) = s • Point.toAlgHom x a := by
  simp [fwd, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]

@[scoped simp] theorem bwd_apply (v : ℕ) (y : (G.baseChange S).Point L v) (a : G.level v) :
    Point.toAlgHom (bwd G S L v y) a = toAlgHom' G S L y ((1 : S) ⊗ₜ[R] a) := by
  simp [bwd]

theorem tmul_eq_algebraMap_mul (s : S) {v : ℕ} (a : G.level v) :
    s ⊗ₜ[R] a = algebraMap S (S ⊗[R] G.level v) s * ((1 : S) ⊗ₜ[R] a) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

theorem bwd_fwd (v : ℕ) (x : G.Point L v) : bwd G S L v (fwd G S L v x) = x :=
  Point.ext fun a => by simp

theorem fwd_bwd (v : ℕ) (y : (G.baseChange S).Point L v) : fwd G S L v (bwd G S L v y) = y := by
  refine ext' G S L fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s a =>
    rw [fwd_apply_tmul, bwd_apply, tmul_eq_algebraMap_mul G s a, map_mul, AlgHom.commutes, Algebra.smul_def]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem bwd_mul (v : ℕ) (y y' : (G.baseChange S).Point L v) :
    bwd G S L v (y * y') = bwd G S L v y * bwd G S L v y' := by
  refine Point.ext fun a => ?_
  rw [bwd_apply, Point.mul_apply]
  change Point.toAlgHom (y * y') ((1 : S) ⊗ₜ[R] a) = _
  rw [Point.mul_apply]
  change Algebra.TensorProduct.lift (toAlgHom' G S L y) (toAlgHom' G S L y') _
      (Coalgebra.comul (R := S) (A := S ⊗[R] G.level v) ((1 : S) ⊗ₜ[R] a)) = _

  let ℛ := Coalgebra.Repr.arbitrary R a
  have hΔ : Coalgebra.comul (R := S) (A := S ⊗[R] G.level v) ((1 : S) ⊗ₜ[R] a) =
      ∑ i ∈ ℛ.index, ((1 : S) ⊗ₜ[R] ℛ.left i) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] ℛ.right i) := by
    rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def, ← ℛ.eq,
      TensorProduct.tmul_sum, map_sum]
    simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  conv_rhs => rw [← ℛ.eq]
  rw [hΔ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, bwd_apply, bwd_apply]

variable (S L)

noncomputable def pointEquiv (v : ℕ) : G.Point L v ≃* (G.baseChange S).Point L v :=
  MulEquiv.symm
    { toFun := bwd G S L v
      invFun := fwd G S L v
      left_inv := fwd_bwd G v
      right_inv := bwd_fwd G v
      map_mul' := bwd_mul G v }

variable {S L}

@[scoped simp] theorem pointEquiv_apply (v : ℕ) (x : G.Point L v) : pointEquiv G S L v x = fwd G S L v x := rfl

noncomputable def trans' (v : ℕ) : S ⊗[R] G.level (v + 1) →ₐc[S] S ⊗[R] G.level v := (G.baseChange S).transition v

@[scoped simp] theorem trans'_tmul (v : ℕ) (s : S) (a : G.level (v + 1)) : trans' G v (s ⊗ₜ[R] a) = s ⊗ₜ[R] G.transition v a := rfl

theorem pointEquiv_pointIncl (v : ℕ) (x : G.Point L v) :
    pointEquiv G S L (v + 1) (G.pointIncl L v x) = (G.baseChange S).pointIncl L v (pointEquiv G S L v x) := by
  refine ext' G S L fun z => ?_
  rw [pointEquiv_apply, pointEquiv_apply]
  change _ = toAlgHom' G S L (fwd G S L v x) (trans' G v z)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s a => rw [fwd_apply_tmul, pointIncl_apply, trans'_tmul, fwd_apply_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem pointEquiv_pointInclLE {v w : ℕ} (hvw : v ≤ w) (x : G.Point L v) :
    pointEquiv G S L w (G.pointInclLE L hvw x) = (G.baseChange S).pointInclLE L hvw (pointEquiv G S L v x) := by
  induction hvw with
  | refl => rw [G.pointInclLE_self, (G.baseChange S).pointInclLE_self]
  | step hvw ih => rw [G.pointInclLE_succ hvw, (G.baseChange S).pointInclLE_succ hvw, pointEquiv_pointIncl, ih]

theorem pointEquiv_pointMap (σ : L ≃ₐ[S] L) (v : ℕ) (x : G.Point L v) :
    pointEquiv G S L v (G.pointMap ((σ.restrictScalars R : L ≃ₐ[R] L) : L →ₐ[R] L) v x) =
      (G.baseChange S).pointMap (σ : L →ₐ[S] L) v (pointEquiv G S L v x) := by
  refine ext' G S L fun z => ?_
  rw [pointEquiv_apply, pointEquiv_apply]
  change _ = (σ : L →ₐ[S] L) (toAlgHom' G S L (fwd G S L v x) z)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s a =>
    rw [fwd_apply_tmul, fwd_apply_tmul, toAlgHom_pointMap, AlgHom.comp_apply, map_smul]
    rfl
  | add z w hz hw => simp only [map_add, hz, hw]

variable (S L)

noncomputable def pointsEquiv : G.Points L ≃+ (G.baseChange S).Points L :=
  AddCommGroup.DirectLimit.congr (G := fun v => Additive (G.Point L v))
    (G' := fun v => Additive ((G.baseChange S).Point L v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => (G.baseChange S).pointsDirectedSystemMap v w hvw)
    (fun v => MulEquiv.toAdditive (pointEquiv G S L v))
    (fun v w hvw => AddMonoidHom.ext fun x => congrArg Additive.ofMul (pointEquiv_pointInclLE G hvw (Additive.toMul x)))

variable {S L}

theorem pointsEquiv_pointsMkAdd (v : ℕ) (x : G.Point L v) :
    pointsEquiv G S L (G.pointsMkAdd L v (Additive.ofMul x)) =
      (G.baseChange S).pointsMkAdd L v (Additive.ofMul (pointEquiv G S L v x)) :=
  AddCommGroup.DirectLimit.congr_apply_of (G := fun v => Additive (G.Point L v))
    (G' := fun v => Additive ((G.baseChange S).Point L v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => (G.baseChange S).pointsDirectedSystemMap v w hvw)
    (fun v => MulEquiv.toAdditive (pointEquiv G S L v)) _ (Additive.ofMul x)

theorem pointsEquiv_smul (σ : L ≃ₐ[S] L) (z : G.Points L) :
    pointsEquiv G S L ((σ.restrictScalars R : L ≃ₐ[R] L) • z) = σ • pointsEquiv G S L z := by
  induction z using Points.induction_on with
  | ih v x =>
    rw [Points.smul_pointsMkAdd, pointsEquiv_pointsMkAdd, pointsEquiv_pointsMkAdd, Points.smul_pointsMkAdd,
      pointEquiv_pointMap]

end PDivisibleGroup.PointsBC
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange.PDivisibleGroup P2MW.S_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange.PDivisibleGroup.PointsBC"
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange.PDivisibleGroup"

open PDivisibleGroup.PointsBC in
theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [CommRing S] [Algebra R S] [Nontrivial S]
    (L : Type) [CommRing L] [Algebra R L] [Algebra S L] [IsScalarTower R S L] :
    ∃ (e : ∀ v : ℕ, G.Point L v ≃* (G.baseChange S).Point L v)
      (E : G.Points L ≃+ (G.baseChange S).Points L),
      (∀ (v : ℕ) (x : G.Point L v) (s : S) (a : G.level v),
        PDivisibleGroup.Point.toAlgHom (e v x) (s ⊗ₜ[R] a) = s • PDivisibleGroup.Point.toAlgHom x a) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        E (G.pointsMkAdd L v (Additive.ofMul x)) = (G.baseChange S).pointsMkAdd L v (Additive.ofMul (e v x))) ∧
      (∀ (σ : L ≃ₐ[S] L) (v : ℕ) (x : G.Point L v),
        e v (G.pointMap ((σ.restrictScalars R : L ≃ₐ[R] L) : L →ₐ[R] L) v x) =
          (G.baseChange S).pointMap (σ : L →ₐ[S] L) v (e v x)) ∧
      (∀ (σ : L ≃ₐ[S] L) (z : G.Points L), E ((σ.restrictScalars R : L ≃ₐ[R] L) • z) = σ • E z) :=
  ⟨pointEquiv G S L, pointsEquiv G S L, fun v x s a => fwd_apply_tmul G v x s a,
    fun v x => pointsEquiv_pointsMkAdd G v x, fun σ v x => pointEquiv_pointMap G σ v x,
    fun σ z => pointsEquiv_smul G σ z⟩

namespace AlgEquiv p2m_export "AlgEquiv" "ext ofAlgHom mul_apply trans restrictScalars ofRingEquiv refl commutes symm toAlgHom toRingEquiv" end AlgEquiv
p2m_open_scoped "AlgEquiv" in
theorem AlgEquiv.exists_unique_restrictScalars_eq_of_isFractionRing
    (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    (τ : L ≃ₐ[R] L) :
    ∃! σ : L ≃ₐ[K] L, σ.restrictScalars R = τ := by

  have hK : τ.toAlgHom.toRingHom.comp (algebraMap K L) = algebraMap K L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) ?_
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R K L]
    exact τ.commutes r
  let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun k => RingHom.congr_fun hK k)
  refine ⟨σ, AlgEquiv.ext fun x => rfl, fun σ' hσ' => AlgEquiv.ext fun x => ?_⟩
  exact (AlgEquiv.congr_fun hσ' x).trans rfl

end S_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange
end P2MW
export P2MW.S_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange (solution)
