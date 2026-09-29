-- Prove2me | solution 1 for PDivisibleGroup.exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8940333b-518c-5460-b839-ad7af1395fdb

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped TensorProduct

noncomputable section

namespace PDivC8

open PDivisibleGroup Coalgebra

variable {O : Type} [CommRing O] {p h : ℕ} (H : PDivisibleGroup O p h)
variable (S : Type) [CommRing S] [Algebra O S] [Nontrivial S]
variable {L : Type} [CommRing L] [Algebra O L]
variable (L' : Type) [CommRing L'] [Algebra S L'] [Algebra O L'] [IsScalarTower O S L']
variable (ι : L →ₐ[O] L')

def bcAlgHom (v : ℕ) (g : H.level v →ₐ[O] L') : S ⊗[O] H.level v →ₐ[S] L' :=
  Algebra.TensorProduct.lift (Algebra.ofId S L') g (fun _ _ => Commute.all _ _)

theorem bcAlgHom_tmul (v : ℕ) (g : H.level v →ₐ[O] L') (s : S) (a : H.level v) :
    bcAlgHom H S L' v g (s ⊗ₜ[O] a) = algebraMap S L' s * g a :=
  Algebra.TensorProduct.lift_tmul _ _ _ s a

def bcFun (v : ℕ) (x : H.Point L v) : (H.baseChange S).Point L' v :=
  Point.ofAlgHom (bcAlgHom H S L' v (ι.comp (Point.toAlgHom x)))

theorem toAlgHom_bcFun (v : ℕ) (x : H.Point L v) :
    Point.toAlgHom (bcFun H S L' ι v x) = bcAlgHom H S L' v (ι.comp (Point.toAlgHom x)) := rfl

theorem bcFun_tmul (v : ℕ) (x : H.Point L v) (s : S) (a : H.level v) :
    Point.toAlgHom (bcFun H S L' ι v x) (s ⊗ₜ[O] a) = algebraMap S L' s * ι (Point.toAlgHom x a) :=
  Algebra.TensorProduct.lift_tmul (Algebra.ofId S L') (ι.comp (Point.toAlgHom x)) (fun _ _ => Commute.all _ _) s a

theorem bcPointExt {v : ℕ} {z z' : (H.baseChange S).Point L' v}
    (hzz : ∀ (s : S) (a : H.level v), Point.toAlgHom z (s ⊗ₜ[O] a) = Point.toAlgHom z' (s ⊗ₜ[O] a)) :
    z = z' := by
  have key : (Point.toAlgHom z : S ⊗[O] H.level v →ₐ[S] L') = (Point.toAlgHom z' : S ⊗[O] H.level v →ₐ[S] L') :=
    Algebra.TensorProduct.ext' hzz
  exact Point.ext fun b => DFunLike.congr_fun key b

theorem bcFun_mul (v : ℕ) (x y : H.Point L v) :
    bcFun H S L' ι v (x * y) = bcFun H S L' ι v x * bcFun H S L' ι v y := by
  show (WithConv.toConv (bcAlgHom H S L' v (ι.comp (Point.toAlgHom (x * y)))) :
        WithConv (S ⊗[O] H.level v →ₐ[S] L')) =
      WithConv.toConv (bcAlgHom H S L' v (ι.comp (Point.toAlgHom x))) *
        WithConv.toConv (bcAlgHom H S L' v (ι.comp (Point.toAlgHom y)))
  apply WithConv.ofConv_injective
  refine Algebra.TensorProduct.ext' fun s a => ?_
  rw [WithConv.ofConv_toConv, AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    TensorProduct.comul_tmul, CommSemiring.comul_apply, bcAlgHom_tmul, AlgHom.comp_apply, Point.mul_apply]
  obtain ⟨idx, t, f, g, hrep⟩ :=
    (⟨_, _, _, _, (Coalgebra.Repr.arbitrary O a).eq⟩ :
      ∃ (idx : Type) (t : Finset idx) (f g : idx → H.level v), ∑ i ∈ t, f i ⊗ₜ[O] g i = comul (R := O) a)
  rw [← hrep]
  simp only [TensorProduct.tmul_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul, bcAlgHom_tmul, bcAlgHom_tmul, AlgHom.comp_apply, AlgHom.comp_apply,
    map_mul, map_one, one_mul]
  ring

def bcPoint (v : ℕ) : H.Point L v →* (H.baseChange S).Point L' v :=
  MonoidHom.mk' (bcFun H S L' ι v) (bcFun_mul H S L' ι v)

theorem bcPoint_apply (v : ℕ) (x : H.Point L v) : bcPoint H S L' ι v x = bcFun H S L' ι v x := rfl

theorem bcPoint_tmul (v : ℕ) (x : H.Point L v) (s : S) (a : H.level v) :
    Point.toAlgHom (bcPoint H S L' ι v x) (s ⊗ₜ[O] a) = algebraMap S L' s * ι (Point.toAlgHom x a) :=
  bcFun_tmul H S L' ι v x s a

theorem bcPoint_pointIncl (v : ℕ) (x : H.Point L v) :
    bcPoint H S L' ι (v + 1) (H.pointIncl L v x) = (H.baseChange S).pointIncl L' v (bcPoint H S L' ι v x) := by
  refine bcPointExt H S L' fun s a => ?_
  rw [bcPoint_tmul, pointIncl_apply, pointIncl_apply, baseChange_transition_tmul, bcPoint_tmul]

theorem bcPoint_pointInclLE {v w : ℕ} (hvw : v ≤ w) (x : H.Point L v) :
    bcPoint H S L' ι w (H.pointInclLE L hvw x) = (H.baseChange S).pointInclLE L' hvw (bcPoint H S L' ι v x) := by
  induction hvw with
  | refl => rw [H.pointInclLE_self, (H.baseChange S).pointInclLE_self]
  | step hvw ih => rw [H.pointInclLE_succ hvw, (H.baseChange S).pointInclLE_succ hvw, bcPoint_pointIncl, ih]

def bcPoints : H.Points L →+ (H.baseChange S).Points L' :=
  AddCommGroup.DirectLimit.map (G := fun v => Additive (H.Point L v))
    (G' := fun v => Additive ((H.baseChange S).Point L' v))
    (f := fun v w hvw => H.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => (H.baseChange S).pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (bcPoint H S L' ι v))
    (fun _ _ hvw => AddMonoidHom.ext fun x =>
      congrArg Additive.ofMul (bcPoint_pointInclLE H S L' ι hvw (Additive.toMul x)))

@[scoped simp] theorem bcPoints_pointsMkAdd (v : ℕ) (x : H.Point L v) :
    bcPoints H S L' ι (H.pointsMkAdd L v (Additive.ofMul x)) =
      (H.baseChange S).pointsMkAdd L' v (Additive.ofMul (bcPoint H S L' ι v x)) :=
  AddCommGroup.DirectLimit.map_apply_of (G := fun v => Additive (H.Point L v))
    (G' := fun v => Additive ((H.baseChange S).Point L' v))
    (f := fun v w hvw => H.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => (H.baseChange S).pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (bcPoint H S L' ι v)) _ (Additive.ofMul x)

theorem bcPoint_injective (hι : Function.Injective ι) (v : ℕ) : Function.Injective (bcPoint H S L' ι v) := by
  intro x y hxy
  refine Point.ext fun a => hι ?_
  have := congrArg (fun z => Point.toAlgHom z ((1 : S) ⊗ₜ[O] a)) hxy
  simpa only [bcPoint_tmul, map_one, one_mul] using this

theorem bcPoints_injective (hι : Function.Injective ι) : Function.Injective (bcPoints H S L' ι) := by
  intro z w hzw
  induction z using Points.induction_on with
  | ih v x =>
    induction w using Points.induction_on with
    | ih w y =>
      rw [← H.pointsMkAdd_pointInclLE (le_max_left v w) x, ← H.pointsMkAdd_pointInclLE (le_max_right v w) y]
        at hzw ⊢
      rw [bcPoints_pointsMkAdd, bcPoints_pointsMkAdd, pointsMkAdd_eq_pointsMkAdd_iff] at hzw
      rw [pointsMkAdd_eq_pointsMkAdd_iff]
      exact bcPoint_injective H S L' ι hι _ hzw

theorem bcPoint_bijective (hι : Function.Injective ι) (v : ℕ)
    [Finite ((H.baseChange S).Point L' v)]
    (hcard : Nat.card ((H.baseChange S).Point L' v) ≤ Nat.card (H.Point L v)) :
    Function.Bijective (bcPoint H S L' ι v) :=
  (bcPoint_injective H S L' ι hι v).bijective_of_nat_card_le hcard

theorem bcPoints_surjective (hsurj : ∀ v, Function.Surjective (bcPoint H S L' ι v)) :
    Function.Surjective (bcPoints H S L' ι) := by
  intro z
  obtain ⟨v, g', rfl⟩ := Points.exists_mkAdd (H.baseChange S) z
  obtain ⟨g, rfl⟩ := hsurj v g'
  exact ⟨H.pointsMkAdd L v (Additive.ofMul g), bcPoints_pointsMkAdd H S L' ι v g⟩

theorem bcPoint_pointMap (v : ℕ) (σ : L ≃ₐ[O] L) (σ' : L' ≃ₐ[S] L')
    (hσ : ∀ t, ι (σ t) = σ' (ι t)) (x : H.Point L v) :
    bcPoint H S L' ι v (H.pointMap (σ : L →ₐ[O] L) v x) =
      (H.baseChange S).pointMap (σ' : L' →ₐ[S] L') v (bcPoint H S L' ι v x) := by
  refine bcPointExt H S L' fun s a => ?_
  rw [bcPoint_tmul, toAlgHom_pointMap, AlgHom.comp_apply, toAlgHom_pointMap, AlgHom.comp_apply,
    bcPoint_tmul]
  change algebraMap S L' s * ι (σ (Point.toAlgHom x a)) = σ' (algebraMap S L' s * ι (Point.toAlgHom x a))
  rw [map_mul, AlgEquiv.commutes, hσ]

theorem bcPoints_smul (σ : L ≃ₐ[O] L) (σ' : L' ≃ₐ[S] L')
    (hσ : ∀ t, ι (σ t) = σ' (ι t)) (z : H.Points L) :
    bcPoints H S L' ι (σ • z) = σ' • bcPoints H S L' ι z := by
  induction z using Points.induction_on with
  | ih v x =>
    rw [Points.smul_pointsMkAdd, bcPoints_pointsMkAdd, bcPoints_pointsMkAdd, Points.smul_pointsMkAdd,
      bcPoint_pointMap H S L' ι v σ σ' hσ]

section Tate

variable {M M' : Type} [AddCommGroup M] [AddCommGroup M'] (q : ℕ) [Fact q.Prime]

def tateMapOf (e : M →+ M') : TateModule q M →ₗ[ℤ_[q]] TateModule q M' where
  toFun x := ⟨fun n => e ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    change e (((x + y : TateModule q M) : ℕ → M) n) = e ((x : ℕ → M) n) + e ((y : ℕ → M) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    change e (((a • x : TateModule q M) : ℕ → M) n) =
      ((a • (⟨fun n => e ((x : ℕ → M) n), _⟩ : TateModule q M') : TateModule q M') : ℕ → M') n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem tateMapOf_apply (e : M →+ M') (x : TateModule q M) (n : ℕ) :
    ((tateMapOf q e x : TateModule q M') : ℕ → M') n = e ((x : ℕ → M) n) := rfl

theorem tateMapOf_injective (e : M →+ M') (he : Function.Injective e) :
    Function.Injective (tateMapOf q e) := by
  intro x y hxy
  refine Subtype.ext (funext fun n => he ?_)
  exact congrArg (fun z : TateModule q M' => (z : ℕ → M') n) hxy

theorem tateMapOf_surjective (e : M →+ M') (he : Function.Bijective e) :
    Function.Surjective (tateMapOf q e) := by
  intro y
  choose x hx using fun n => he.2 ((y : ℕ → M') n)
  refine ⟨⟨x, fun n => ⟨?_, ?_⟩⟩, Subtype.ext (funext fun n => hx n)⟩
  · apply he.1
    rw [map_zsmul, hx, map_zero, TateModule.torsion]
  · apply he.1
    rw [map_zsmul, hx, hx, TateModule.compat]

def tateEquivOf (e : M →+ M') (he : Function.Bijective e) : TateModule q M ≃ₗ[ℤ_[q]] TateModule q M' :=
  LinearEquiv.ofBijective (tateMapOf q e) ⟨tateMapOf_injective q e he.1, tateMapOf_surjective q e he⟩

@[scoped simp] theorem tateEquivOf_apply (e : M →+ M') (he : Function.Bijective e) (x : TateModule q M) (n : ℕ) :
    ((tateEquivOf q e he x : TateModule q M') : ℕ → M') n = e ((x : ℕ → M) n) := rfl

end Tate

end PDivC8
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl.PDivC8"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl.PDivC8"

open PDivC8 PDivisibleGroup in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] [Algebra O (PadicAlgCl.ringOfIntegers p K)]
    (ι : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (hι : ∀ x : O, ((algebraMap O (PadicAlgCl.ringOfIntegers p K) x : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) = ι (algebraMap O (AlgebraicClosure ℚ) x))
    (hιP : ∀ t : AlgebraicClosure ℚ, P.valuation t < 1 ↔ ‖ι t‖ < 1)
    (hιP' : ∀ t : AlgebraicClosure ℚ, t ∈ P ↔ ‖ι t‖ ≤ 1)
    {h : ℕ} (H : PDivisibleGroup O p h) :
    ∃ Θ : TateModule p (H.Points (AlgebraicClosure ℚ)) ≃ₗ[ℤ_[p]] TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p)),
      (∀ (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ) (τl : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : AlgebraicClosure ℚ, ι (τ' t) = τl (ι t)) →
        ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
          Θ (H.tateModuleRep (AlgebraicClosure ℚ) τ' y) = (H.baseChange (PadicAlgCl.ringOfIntegers p K)).tateModuleRep (PadicAlgCl p) τl (Θ y)) ∧
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
        (∀ n : ℕ, ∃ (w : ℕ) (g : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul g) =
        (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom g a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
        ∀ n : ℕ, ∃ (w : ℕ) (g : (H.baseChange (PadicAlgCl.ringOfIntegers p K)).Point (PadicAlgCl p) w),
          (H.baseChange (PadicAlgCl.ringOfIntegers p K)).pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
            ((Θ y : TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p))) : ℕ → (H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p)) n ∧
          ∀ a : (H.baseChange (PadicAlgCl.ringOfIntegers p K)).level w, ‖PDivisibleGroup.Point.toAlgHom g a -
            algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) := by
  classical

  let S := PadicAlgCl.ringOfIntegers p K

  letI algO : Algebra O (PadicAlgCl p) :=
    ((algebraMap S (PadicAlgCl p)).comp (algebraMap O S)).toAlgebra
  haveI : IsScalarTower O S (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halgO : ∀ x : O, algebraMap O (PadicAlgCl p) x = ((algebraMap O S x : S) : PadicAlgCl p) := fun _ => rfl

  let ιₐ : AlgebraicClosure ℚ →ₐ[O] PadicAlgCl p :=
    { ι with commutes' := fun x => by rw [halgO, hι]; rfl }
  have hιₐ : ∀ t, ιₐ t = ι t := fun _ => rfl
  have hιinj : Function.Injective ιₐ := ι.injective

  have hcnt : ∀ v, Finite ((H.baseChange S).Point (PadicAlgCl p) v) ∧
      Nat.card ((H.baseChange S).Point (PadicAlgCl p) v) ≤ Nat.card (H.Point (AlgebraicClosure ℚ) v) := by
    intro v
    obtain ⟨hf1, hc1⟩ := PDivisibleGroup.finite_point_and_natCard_point_eq_pow p H (AlgebraicClosure ℚ) v
    obtain ⟨hf2, hc2⟩ := PDivisibleGroup.finite_point_and_natCard_point_eq_pow p (H.baseChange S) (PadicAlgCl p) v
    exact ⟨hf2, by rw [hc1, hc2]⟩
  have hbij : ∀ v, Function.Bijective (bcPoint H S (PadicAlgCl p) ιₐ v) := fun v => by
    haveI := (hcnt v).1
    exact bcPoint_bijective H S (PadicAlgCl p) ιₐ hιinj v (hcnt v).2
  have hBij : Function.Bijective (bcPoints H S (PadicAlgCl p) ιₐ) :=
    ⟨bcPoints_injective H S (PadicAlgCl p) ιₐ hιinj, bcPoints_surjective H S (PadicAlgCl p) ιₐ fun v => (hbij v).2⟩
  let Θ := tateEquivOf p (bcPoints H S (PadicAlgCl p) ιₐ) hBij
  refine ⟨Θ, ?_, ?_⟩
  ·
    intro τ' τl hτ y
    refine Subtype.ext (funext fun n => ?_)
    rw [tateEquivOf_apply, tateModuleRep_apply, tateModuleRep_apply, tateEquivOf_apply]
    exact bcPoints_smul H S (PadicAlgCl p) ιₐ τ' τl (fun t => hτ t) _
  ·
    intro y hy n
    obtain ⟨w, g, hg, hred⟩ := hy n
    refine ⟨w, bcPoint H S (PadicAlgCl p) ιₐ w g, ?_, ?_⟩
    · rw [tateEquivOf_apply, ← hg, bcPoints_pointsMkAdd]
    · have h1 : ∀ b, algebraMap S (PadicAlgCl p) (Coalgebra.counit b) =
          Point.toAlgHom (bcPoint H S (PadicAlgCl p) ιₐ w 1) b := fun b => by
        rw [map_one]; rfl
      let D : S ⊗[O] H.level w →ₗ[S] PadicAlgCl p :=
        (Point.toAlgHom (bcPoint H S (PadicAlgCl p) ιₐ w g)).toLinearMap -
          (Point.toAlgHom (bcPoint H S (PadicAlgCl p) ιₐ w 1)).toLinearMap
      have hD : ∀ b, D b = Point.toAlgHom (bcPoint H S (PadicAlgCl p) ιₐ w g) b -
          Point.toAlgHom (bcPoint H S (PadicAlgCl p) ιₐ w 1) b := fun b => rfl
      suffices hDn : ∀ b : S ⊗[O] H.level w, ‖D b‖ < 1 by
        intro b; rw [h1, ← hD]; exact hDn b
      intro b
      induction b using TensorProduct.induction_on with
      | zero => rw [map_zero, norm_zero]; exact one_pos
      | add b c hb hc =>
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hb hc)
      | tmul s a =>
        rw [hD, bcPoint_tmul, bcPoint_tmul, ← mul_sub, ← map_sub, hιₐ, norm_mul, Point.one_apply]
        have hs : ‖algebraMap S (PadicAlgCl p) s‖ ≤ 1 := PadicAlgCl.ringOfIntegers.norm_coe_le_one p K s
        have hlt : ‖ι (Point.toAlgHom g a - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a))‖ < 1 :=
          (hιP _).1 (hred a)
        calc ‖algebraMap S (PadicAlgCl p) s‖ *
              ‖ι (Point.toAlgHom g a - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a))‖
            ≤ 1 * ‖ι (Point.toAlgHom g a - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a))‖ := by
              gcongr
          _ < 1 := by rw [one_mul]; exact hlt

end S_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl
end P2MW
export P2MW.S_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl (solution)
