-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.exists_points_tateModule_pairing_eq_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/73d057de-9277-5151-8e21-4f4f1c19d5b1

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_PrimaryTorsion
import Theorems.Thm_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair

set_option autoImplicit false
set_option linter.unusedSectionVars false

open PDivisibleGroup
open scoped TensorProduct
open Coalgebra WithConv

namespace PDivAlphaZero

variable {R : Type} [CommRing R] {p h : ℕ}

section Lift

variable (G : PDivisibleGroup R p h) {L : Type} [CommRing L] [Algebra R L]

theorem exists_point_of_nsmul_eq_zero (v : ℕ) (z : G.Points L) (hz : (p ^ v) • z = 0) :
    ∃ f : G.Point L v, G.pointsMkAdd L v (Additive.ofMul f) = z := by
  obtain ⟨m, y, rfl⟩ := Points.exists_mkAdd G z
  set w := max m v
  have hy : G.pointsMkAdd L w (Additive.ofMul (G.pointInclLE L (le_max_left m v) y)) =
      G.pointsMkAdd L m (Additive.ofMul y) := G.pointsMkAdd_pointInclLE _ y
  rw [← hy] at hz ⊢
  set y' := G.pointInclLE L (le_max_left m v) y
  have hpow : y' ^ (p ^ v) = 1 := by
    apply G.pointsMkAdd_injective w
    change G.pointsMkAdd L w (Additive.ofMul (y' ^ p ^ v)) = G.pointsMkAdd L w (Additive.ofMul 1)
    rw [ofMul_pow, map_nsmul, hz, ofMul_one, map_zero]
  obtain ⟨x, hx⟩ := G.exists_pointInclLE_eq_of_pow_eq_one (le_max_right m v) y' hpow
  exact ⟨x, by rw [← hx, pointsMkAdd_pointInclLE]⟩

variable [Fact p.Prime]

theorem natCast_pow_zsmul_eq_nsmul (v : ℕ) (z : G.Points L) :
    ((p ^ v : ℕ) : ℤ) • z = (p ^ v) • z := natCast_zsmul z (p ^ v)

noncomputable def lift (x : TateModule p (G.Points L)) (v : ℕ) : G.Point L v :=
  Classical.choose (exists_point_of_nsmul_eq_zero G v ((x : ℕ → G.Points L) v)
    (by rw [← natCast_pow_zsmul_eq_nsmul]; exact TateModule.torsion x v))

theorem pointsMkAdd_lift (x : TateModule p (G.Points L)) (v : ℕ) :
    G.pointsMkAdd L v (Additive.ofMul (lift G x v)) = (x : ℕ → G.Points L) v :=
  Classical.choose_spec (exists_point_of_nsmul_eq_zero G v ((x : ℕ → G.Points L) v)
    (by rw [← natCast_pow_zsmul_eq_nsmul]; exact TateModule.torsion x v))

theorem lift_unique {x : TateModule p (G.Points L)} {v : ℕ} {f : G.Point L v}
    (hf : G.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → G.Points L) v) : f = lift G x v :=
  (G.pointsMkAdd_eq_pointsMkAdd_iff _ _).1 (by rw [hf, pointsMkAdd_lift])

theorem lift_add (x y : TateModule p (G.Points L)) (v : ℕ) :
    lift G (x + y) v = lift G x v * lift G y v := by
  symm
  apply lift_unique
  rw [ofMul_mul, map_add, pointsMkAdd_lift, pointsMkAdd_lift]
  rfl

theorem lift_smul (a : ℤ_[p]) (x : TateModule p (G.Points L)) (v : ℕ) :
    lift G (a • x) v = lift G x v ^ (a.appr v) := by
  symm
  apply lift_unique
  rw [ofMul_pow, map_nsmul, pointsMkAdd_lift, TateModule.smul_apply, natCast_zsmul]

theorem lift_succ_pow (x : TateModule p (G.Points L)) (v : ℕ) :
    lift G x (v + 1) ^ p = G.pointIncl L v (lift G x v) := by
  apply (G.pointsMkAdd_eq_pointsMkAdd_iff _ _).1
  rw [ofMul_pow, map_nsmul, pointsMkAdd_lift, pointsMkAdd_pointIncl, pointsMkAdd_lift, ← natCast_zsmul]
  exact TateModule.compat x v

theorem lift_rep (σ : L ≃ₐ[R] L) (x : TateModule p (G.Points L)) (v : ℕ) :
    lift G (G.tateModuleRep L σ x) v = G.pointMap (σ : L →ₐ[R] L) v (lift G x v) := by
  symm
  apply lift_unique
  rw [tateModuleRep_apply, ← Points.smul_pointsMkAdd, pointsMkAdd_lift]

end Lift

section Level

variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable {L : Type} [CommRing L] [Algebra R L]

noncomputable abbrev eS (v : ℕ) : CartierDual R (G.level v) →ₐc[R] G'.level v :=
  ((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v)

noncomputable def dualPt (v : ℕ) (ψ : G'.Point L v) : CartierDual R (G.level v) →ₐ[R] L :=
  (Point.toAlgHom ψ).comp (eS D v : CartierDual R (G.level v) →ₐ[R] G'.level v)

theorem dualPt_apply (v : ℕ) (ψ : G'.Point L v) (φ : CartierDual R (G.level v)) :
    dualPt D v ψ φ = Point.toAlgHom ψ ((D.equiv v).symm φ) := rfl

noncomputable abbrev bas (G : PDivisibleGroup R p h) (v : ℕ) :=
  Module.Free.chooseBasis R (G.level v)

theorem pair_eq (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ = ∑ i, (Point.toAlgHom f) (bas G v i) *
      dualPt D v ψ (CartierDual.ofDual R (G.level v) ((bas G v).coord i)) := by
  rw [CartierDuality.pair_def]
  rfl

theorem pair_eq_conv (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ = ∑ i, (Point.toConv f) (bas G v i) *
      dualPt D v ψ (CartierDual.ofDual R (G.level v) ((bas G v).coord i)) :=
  pair_eq D v f ψ

theorem pair_mul_left (v : ℕ) (f g : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v (f * g) ψ = D.pair L v f ψ * D.pair L v g ψ := by
  rw [pair_eq_conv, pair_eq_conv, pair_eq_conv]
  exact (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.2.2.1 (Point.toConv f) (Point.toConv g) (dualPt D v ψ)

theorem dualPt_mul (v : ℕ) (ψ ψ' : G'.Point L v) :
    dualPt D v (ψ * ψ') = WithConv.ofConv (WithConv.toConv (dualPt D v ψ) * WithConv.toConv (dualPt D v ψ')) := by
  unfold dualPt
  exact AlgHom.convMul_comp_bialgHom_distrib (Point.toConv ψ) (Point.toConv ψ') (eS D v)

theorem pair_mul_right (v : ℕ) (f : G.Point L v) (ψ ψ' : G'.Point L v) :
    D.pair L v f (ψ * ψ') = D.pair L v f ψ * D.pair L v f ψ' := by
  rw [pair_eq, pair_eq, pair_eq, dualPt_mul]
  exact (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.2.2.2.1 (Point.toAlgHom f)
    (WithConv.toConv (dualPt D v ψ)) (WithConv.toConv (dualPt D v ψ'))

theorem pair_one_left (v : ℕ) (ψ : G'.Point L v) : D.pair L v 1 ψ = 1 := by
  rw [pair_eq_conv]
  exact (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.2.2.2.2.1 (dualPt D v ψ)

theorem pair_one_right (v : ℕ) (f : G.Point L v) : D.pair L v f 1 = 1 := by
  rw [pair_eq]
  have h1 : ∀ φ : CartierDual R (G.level v),
      dualPt D v 1 φ = (1 : WithConv (CartierDual R (G.level v) →ₐ[R] L)) φ := by
    intro φ
    rw [dualPt_apply, Point.one_apply, AlgHom.convOne_apply]
    congr 1
    exact CoalgHomClass.counit_comp_apply (eS D v) φ
  simp_rw [h1]
  exact (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.2.2.2.2.2.1 (Point.toAlgHom f)

theorem pair_pow_left (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) (n : ℕ) :
    D.pair L v (f ^ n) ψ = D.pair L v f ψ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pair_one_left]
  | succ n ih => rw [pow_succ, pow_succ, pair_mul_left, ih]

theorem pair_pow_right (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) (n : ℕ) :
    D.pair L v f (ψ ^ n) = D.pair L v f ψ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pair_one_right]
  | succ n ih => rw [pow_succ, pow_succ, pair_mul_right, ih]

theorem pair_pow_card (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ ^ (p ^ v) = 1 := by
  rw [← pair_pow_left, Point.pow_card_eq_one, pair_one_left]

theorem pair_pointMap {L' : Type} [CommRing L'] [Algebra R L'] (φ : L →ₐ[R] L')
    (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L' v (G.pointMap φ v f) (G'.pointMap φ v ψ) = φ (D.pair L v f ψ) := by
  rw [pair_eq, pair_eq]
  have key := (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.1 φ (Point.toAlgHom f).toLinearMap
    ((dualPt D v ψ).toLinearMap.comp (CartierDual.ofDual R (G.level v)).toLinearMap)
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key.symm
  rfl

end Level

section Transpose

variable {A : Type} [CommRing A] [Bialgebra R A]

theorem cd_add_apply (φ ψ : CartierDual R A) (a : A) : (φ + ψ) a = φ a + ψ a := rfl

theorem mul'_apply_apply (w : CartierDual R A ⊗[R] CartierDual R A) (a : A) :
    LinearMap.mul' R (CartierDual R A) w a =
      TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap w)
        (comul (R := R) a) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]; rfl
  | tmul φ ψ =>
      rw [LinearMap.mul'_apply, TensorProduct.map_tmul]
      exact CartierDual.mul_apply φ ψ a
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [cd_add_apply, hx, hy]

noncomputable def tr (f : A →ₗ[R] A) : CartierDual R A →ₗ[R] CartierDual R A :=
  (CartierDual.ofDual R A).toLinearMap ∘ₗ f.dualMap ∘ₗ (CartierDual.toDual R A).toLinearMap

@[scoped simp] theorem tr_apply (f : A →ₗ[R] A) (φ : CartierDual R A) (a : A) : tr f φ a = φ (f a) := rfl

theorem tr_id : tr (LinearMap.id : A →ₗ[R] A) = LinearMap.id := by
  apply LinearMap.ext; intro φ; apply CartierDual.ext; intro a; rfl

theorem dualDistrib_map_tr (f g : A →ₗ[R] A) (u : CartierDual R A ⊗[R] CartierDual R A)
    (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap
          (TensorProduct.map (tr f) (tr g) u)) z =
      TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap u)
        (TensorProduct.map f g z) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul φ ψ =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

variable [Module.Finite R A] [Module.Free R A]

theorem comul_pairing' (φ : CartierDual R A) (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap
          (comul (R := R) φ)) z = φ (LinearMap.mul' R A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
      rw [LinearMap.mul'_apply]
      exact CartierDual.comul_pairing φ a b
  | add x y hx hy => simp only [map_add, hx, hy]

theorem convMul_tr_apply (f g : A →ₗ[R] A) (φ : CartierDual R A) (a : A) :
    (toConv (tr f) * toConv (tr g)).ofConv φ a = φ ((toConv f * toConv g).ofConv a) := by
  rw [LinearMap.convMul_apply, LinearMap.convMul_apply, ofConv_toConv, ofConv_toConv,
    ofConv_toConv, ofConv_toConv, mul'_apply_apply, dualDistrib_map_tr, comul_pairing']

theorem convPow_id_apply (n : ℕ) (φ : CartierDual R A) (a : A) :
    ((toConv (LinearMap.id : CartierDual R A →ₗ[R] CartierDual R A)) ^ n).ofConv φ a =
      φ (((toConv (LinearMap.id : A →ₗ[R] A)) ^ n).ofConv a) := by
  induction n generalizing φ a with
  | zero =>
      rw [pow_zero, pow_zero]
      change (algebraMap R (CartierDual R A) (counit (R := R) φ)) a =
        φ (algebraMap R A (counit (R := R) a))
      rw [CartierDual.algebraMap_apply, CartierDual.counit_apply, Algebra.algebraMap_eq_smul_one,
        map_smul, smul_eq_mul]
  | succ n ih =>
      have hT : ((toConv (LinearMap.id : CartierDual R A →ₗ[R] CartierDual R A)) ^ n).ofConv =
          tr (((toConv (LinearMap.id : A →ₗ[R] A)) ^ n).ofConv) := by
        apply LinearMap.ext; intro ψ; apply CartierDual.ext; intro b
        rw [tr_apply]
        exact ih ψ b
      rw [pow_succ, pow_succ]
      have key := convMul_tr_apply (((toConv (LinearMap.id : A →ₗ[R] A)) ^ n).ofConv)
        LinearMap.id φ a
      rw [tr_id, ← hT, toConv_ofConv, toConv_ofConv] at key
      exact key

theorem nsmulAlgHom_cartierDual_apply [Coalgebra.IsCocomm R A] (n : ℕ) (φ : CartierDual R A)
    (a : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R (CartierDual R A) n φ a =
      φ (PDivisibleGroup.Hopf.nsmulAlgHom R A n a) := by
  have h1 := congrArg (fun f => f φ a)
    (PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom R (CartierDual R A) n)
  have h2 := congrArg (fun f => f a) (PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom R A n)
  simp only [AlgHom.toLinearMap_apply] at h1 h2
  rw [h1, h2]
  exact convPow_id_apply n φ a

end Transpose

section Adjunction

variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable {L : Type} [CommRing L] [Algebra R L]

theorem sum_comp_eq_sum_dualMap {A A' : Type} [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (b : Module.Basis ι R A) (b' : Module.Basis ι' R A')
    (t : A' →ₗ[R] A) (fL : A →ₗ[R] L) (Φ : Module.Dual R A' →ₗ[R] L) :
    ∑ k, fL (t (b' k)) * Φ (b'.coord k) = ∑ i, fL (b i) * Φ (t.dualMap (b.coord i)) := by

  have hexp : ∀ i, t.dualMap (b.coord i) = ∑ k, (b.coord i (t (b' k))) • b'.coord k := by
    intro i
    rw [← Module.Basis.sum_dual_apply_smul_coord b' (t.dualMap (b.coord i))]
    rfl
  have hrhs : ∀ i, fL (b i) * Φ (t.dualMap (b.coord i)) =
      ∑ k, (b.coord i (t (b' k))) • (fL (b i) * Φ (b'.coord k)) := by
    intro i
    rw [hexp i, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smul, mul_smul_comm]
  simp_rw [hrhs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_

  have hrepr : ∑ i, (b.coord i) (t (b' k)) • b i = t (b' k) := by
    conv_rhs => rw [← b.sum_repr (t (b' k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.coord_apply]
  have hsum : ∑ i, (b.coord i) (t (b' k)) • (fL (b i) * Φ (b'.coord k)) =
      fL (∑ i, (b.coord i) (t (b' k)) • b i) * Φ (b'.coord k) := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, smul_mul_assoc]
  rw [hsum, hrepr]

theorem dualMap_transition_toDualEquiv (v : ℕ) (x' : G'.level (v + 1)) :
    (G.transitionAlgHom v).toLinearMap.dualMap (D.toDualEquiv v (G'.transition v x')) =
      D.toDualEquiv (v + 1) (Hopf.nsmulAlgHom R (G'.level (v + 1)) p x') := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.dualMap_apply, CartierDuality.toDualEquiv_apply, CartierDuality.toDualEquiv_apply]
  change D.equiv v (G'.transition v x') (G.transition v a) =
    ((D.equiv (v + 1) : G'.level (v + 1) →ₐc[R] CartierDual R (G.level (v + 1)))
      (Hopf.nsmulAlgHom R (G'.level (v + 1)) p x')) a
  rw [D.equiv_transition v x' a, ← Hopf.nsmulAlgHom_bialgHom_apply, nsmulAlgHom_cartierDual_apply]
  rfl

variable [Fact p.Prime]

theorem pair_pointIncl_left (v : ℕ) (f : G.Point L v) (Ψ : G'.Point L (v + 1)) (ψ : G'.Point L v)
    (hΨ : Ψ ^ p = G'.pointIncl L v ψ) :
    D.pair L (v + 1) (G.pointIncl L v f) Ψ = D.pair L v f ψ := by
  set t : G.level (v + 1) →ₗ[R] G.level v := (G.transitionAlgHom v).toLinearMap with ht

  set Φ : Module.Dual R (G.level (v + 1)) →ₗ[R] L :=
    (Point.toAlgHom Ψ).toLinearMap ∘ₗ (D.toDualEquiv (v + 1)).symm.toLinearMap with hΦ
  set φ : Module.Dual R (G.level v) →ₗ[R] L :=
    (Point.toAlgHom ψ).toLinearMap ∘ₗ (D.toDualEquiv v).symm.toLinearMap with hφ

  have hΦφ : ∀ θ : Module.Dual R (G.level v), Φ (t.dualMap θ) = φ θ := by
    intro θ
    obtain ⟨x', hx'⟩ := G'.transition_surjective v ((D.toDualEquiv v).symm θ)
    have hθ : θ = D.toDualEquiv v (G'.transition v x') := by
      rw [hx', LinearEquiv.apply_symm_apply]
    rw [hθ, ht, dualMap_transition_toDualEquiv D v x', hΦ, hφ]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
      AlgHom.toLinearMap_apply]
    rw [← AlgHom.comp_apply, ← Point.toAlgHom_pow, hΨ, pointIncl_apply]

  rw [pair_eq, pair_eq]
  have step := sum_comp_eq_sum_dualMap (L := L) (bas G v) (bas G (v + 1)) t (Point.toAlgHom f).toLinearMap Φ
  have lhs : D.pair L (v + 1) (G.pointIncl L v f) Ψ = ∑ k, (Point.toAlgHom f).toLinearMap (t (bas G (v + 1) k)) *
      Φ ((bas G (v + 1)).coord k) := by
    rw [pair_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rfl
  have rhs : D.pair L v f ψ = ∑ i, (Point.toAlgHom f).toLinearMap (bas G v i) * φ ((bas G v).coord i) := by
    rw [pair_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [← pair_eq, ← pair_eq, lhs, rhs, step]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hΦφ]

end Adjunction

section Values

variable [Fact p.Prime]
variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable {L : Type} [CommRing L] [Algebra R L]

noncomputable def pairUnit (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) : Lˣ :=
  (IsUnit.of_pow_eq_one (pair_pow_card D v f ψ) (pow_ne_zero v (Fact.out : p.Prime).ne_zero)).unit

@[scoped simp] theorem val_pairUnit (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    ((pairUnit D v f ψ : Lˣ) : L) = D.pair L v f ψ :=
  IsUnit.unit_spec _

theorem pairUnit_pow_card (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) : pairUnit D v f ψ ^ (p ^ v) = 1 := by
  ext; rw [Units.val_pow_eq_pow_val, val_pairUnit, pair_pow_card, Units.val_one]

noncomputable def pairPT (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) : PrimaryTorsion p (Additive Lˣ) :=
  ⟨Additive.ofMul (pairUnit D v f ψ), PrimaryTorsion.mem_of_nsmul_eq_zero (k := v)
    (by rw [← ofMul_pow, pairUnit_pow_card, ofMul_one])⟩

theorem coe_pairPT (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    ((pairPT D v f ψ : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) = Additive.ofMul (pairUnit D v f ψ) := rfl

theorem val_pairPT (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    ((Additive.toMul ((pairPT D v f ψ : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) =
      D.pair L v f ψ := by
  rw [coe_pairPT, toMul_ofMul, val_pairUnit]

theorem nsmul_pairPT_eq_zero (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    p ^ v • ((pairPT D v f ψ : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) = 0 := by
  rw [coe_pairPT, ← ofMul_pow, pairUnit_pow_card, ofMul_one]

theorem PT_ext {x y : PrimaryTorsion p (Additive Lˣ)}
    (hxy : ((Additive.toMul (x : Additive Lˣ) : Lˣ) : L) = ((Additive.toMul (y : Additive Lˣ) : Lˣ) : L)) :
    x = y :=
  Subtype.ext (Additive.toMul.injective (Units.ext hxy))

theorem val_add (x y : PrimaryTorsion p (Additive Lˣ)) :
    ((Additive.toMul ((x + y : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) =
      ((Additive.toMul (x : Additive Lˣ) : Lˣ) : L) * ((Additive.toMul (y : Additive Lˣ) : Lˣ) : L) := by
  rw [AddSubgroup.coe_add, toMul_add, Units.val_mul]

theorem val_nsmul (n : ℕ) (x : PrimaryTorsion p (Additive Lˣ)) :
    ((Additive.toMul ((n • x : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) =
      ((Additive.toMul (x : Additive Lˣ) : Lˣ) : L) ^ n := by
  rw [AddSubgroup.coe_nsmul, toMul_nsmul, Units.val_pow_eq_pow_val]

theorem pairPT_mul_left (v : ℕ) (f g : G.Point L v) (ψ : G'.Point L v) :
    pairPT D v (f * g) ψ = pairPT D v f ψ + pairPT D v g ψ :=
  PT_ext (by rw [val_add, val_pairPT, val_pairPT, val_pairPT, pair_mul_left])

theorem pairPT_mul_right (v : ℕ) (f : G.Point L v) (ψ ψ' : G'.Point L v) :
    pairPT D v f (ψ * ψ') = pairPT D v f ψ + pairPT D v f ψ' :=
  PT_ext (by rw [val_add, val_pairPT, val_pairPT, val_pairPT, pair_mul_right])

theorem pairPT_pow_right (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) (n : ℕ) :
    pairPT D v f (ψ ^ n) = n • pairPT D v f ψ :=
  PT_ext (by rw [val_nsmul, val_pairPT, val_pairPT, pair_pow_right])

theorem pairPT_pointIncl_lift (v : ℕ) (f : G.Point L v) (y : TateModule p (G'.Points L)) :
    pairPT D (v + 1) (G.pointIncl L v f) (lift G' y (v + 1)) = pairPT D v f (lift G' y v) :=
  PT_ext (by rw [val_pairPT, val_pairPT, pair_pointIncl_left D v f _ _ (lift_succ_pow G' y v)])

theorem pairPT_pointInclLE_lift {v w : ℕ} (hvw : v ≤ w) (f : G.Point L v) (y : TateModule p (G'.Points L)) :
    pairPT D w (G.pointInclLE L hvw f) (lift G' y w) = pairPT D v f (lift G' y v) := by
  induction hvw with
  | refl => rw [G.pointInclLE_self]
  | step hvw ih => rw [G.pointInclLE_succ hvw, pairPT_pointIncl_lift, ih]

theorem pairPT_lift_eq_of_pointsMkAdd_eq {v w : ℕ} (f : G.Point L v) (g : G.Point L w)
    (hfg : G.pointsMkAdd L v (Additive.ofMul f) = G.pointsMkAdd L w (Additive.ofMul g))
    (y : TateModule p (G'.Points L)) :
    pairPT D v f (lift G' y v) = pairPT D w g (lift G' y w) := by
  have hcommon : G.pointInclLE L (le_max_left v w) f = G.pointInclLE L (le_max_right v w) g := by
    apply (G.pointsMkAdd_eq_pointsMkAdd_iff _ _).1
    rw [pointsMkAdd_pointInclLE, pointsMkAdd_pointInclLE, hfg]
  rw [← pairPT_pointInclLE_lift D (le_max_left v w) f y, ← pairPT_pointInclLE_lift D (le_max_right v w) g y,
    hcommon]

end Values

section Alpha

variable [Fact p.Prime]
variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable {L : Type} [CommRing L] [Algebra R L]

noncomputable def lv (z : G.Points L) : ℕ := Classical.choose (Points.exists_mkAdd G z)

noncomputable def pt (z : G.Points L) : G.Point L (lv z) :=
  Classical.choose (Classical.choose_spec (Points.exists_mkAdd G z))

theorem pointsMkAdd_pt (z : G.Points L) : G.pointsMkAdd L (lv z) (Additive.ofMul (pt z)) = z :=
  Classical.choose_spec (Classical.choose_spec (Points.exists_mkAdd G z))

noncomputable def αFun (z : G.Points L) (y : TateModule p (G'.Points L)) : PrimaryTorsion p (Additive Lˣ) :=
  pairPT D (lv z) (pt z) (lift G' y (lv z))

theorem αFun_pointsMkAdd (v : ℕ) (f : G.Point L v) (y : TateModule p (G'.Points L)) :
    αFun D (G.pointsMkAdd L v (Additive.ofMul f)) y = pairPT D v f (lift G' y v) := by
  unfold αFun
  exact pairPT_lift_eq_of_pointsMkAdd_eq D _ _ (pointsMkAdd_pt _) y

theorem αFun_add_right (z : G.Points L) (y y' : TateModule p (G'.Points L)) :
    αFun D z (y + y') = αFun D z y + αFun D z y' := by
  unfold αFun
  rw [lift_add, pairPT_mul_right]

theorem αFun_smul_right (z : G.Points L) (a : ℤ_[p]) (y : TateModule p (G'.Points L)) :
    αFun D z (a • y) = a • αFun D z y := by
  unfold αFun
  rw [lift_smul, pairPT_pow_right]
  refine Subtype.ext ?_
  rw [PrimaryTorsion.coe_smul a _ (nsmul_pairPT_eq_zero D _ _ _), AddSubgroup.coe_nsmul, natCast_zsmul]

noncomputable def αLin (z : G.Points L) : TateModule p (G'.Points L) →ₗ[ℤ_[p]] PrimaryTorsion p (Additive Lˣ) where
  toFun := αFun D z
  map_add' := αFun_add_right D z
  map_smul' := αFun_smul_right D z

theorem αLin_apply (z : G.Points L) (y : TateModule p (G'.Points L)) : αLin D z y = αFun D z y := rfl

theorem αLin_add (z z' : G.Points L) : αLin D (z + z') = αLin D z + αLin D z' := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.add_apply, αLin_apply, αLin_apply, αLin_apply]
  induction z using Points.induction_on with
  | ih v f =>
    induction z' using Points.induction_on with
    | ih w g =>

      rw [← G.pointsMkAdd_pointInclLE (le_max_left v w) f, ← G.pointsMkAdd_pointInclLE (le_max_right v w) g,
        ← map_add, ← ofMul_mul, αFun_pointsMkAdd, αFun_pointsMkAdd, αFun_pointsMkAdd, pairPT_mul_left]

noncomputable def α : G.Points L →+ (TateModule p (G'.Points L) →ₗ[ℤ_[p]] PrimaryTorsion p (Additive Lˣ)) where
  toFun := αLin D
  map_zero' := by
    have h := αLin_add D (0 : G.Points L) 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  map_add' := αLin_add D

theorem α_apply (z : G.Points L) (y : TateModule p (G'.Points L)) : α D z y = αFun D z y := rfl

theorem α_level (v : ℕ) (f : G.Point L v) (y : TateModule p (G'.Points L)) (ψ : G'.Point L v)
    (hψ : G'.pointsMkAdd L v (Additive.ofMul ψ) = (y : ℕ → G'.Points L) v) :
    ((Additive.toMul ((α D (G.pointsMkAdd L v (Additive.ofMul f)) y :
        PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) = D.pair L v f ψ := by
  rw [α_apply, αFun_pointsMkAdd, val_pairPT, ← lift_unique G' hψ]

theorem α_smul_rep (σ : L ≃ₐ[R] L) (z : G.Points L) (y : TateModule p (G'.Points L)) :
    ((Additive.toMul ((α D (σ • z) (G'.tateModuleRep L σ y) :
        PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) =
      σ (((Additive.toMul ((α D z y : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L)) := by
  induction z using Points.induction_on with
  | ih v f =>
    rw [Points.smul_pointsMkAdd, α_apply, α_apply, αFun_pointsMkAdd, αFun_pointsMkAdd, val_pairPT, val_pairPT,
      lift_rep, pair_pointMap]
    rfl

end Alpha

end PDivAlphaZero
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair.PDivAlphaZero"

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (L : Type) [CommRing L] [Algebra R L] :
    ∃ α : G.Points L →+ (TateModule p (G'.Points L) →ₗ[ℤ_[p]] PrimaryTorsion p (Additive Lˣ)),
      (∀ (v : ℕ) (f : G.Point L v) (y : TateModule p (G'.Points L)) (ψ : G'.Point L v),
          G'.pointsMkAdd L v (Additive.ofMul ψ) = (y : ℕ → G'.Points L) v →
          ((Additive.toMul ((α (G.pointsMkAdd L v (Additive.ofMul f)) y :
              PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) = D.pair L v f ψ) ∧
      (∀ (σ : L ≃ₐ[R] L) (z : G.Points L) (y : TateModule p (G'.Points L)),
          ((Additive.toMul ((α (σ • z) (G'.tateModuleRep L σ y) :
              PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) =
            σ (((Additive.toMul ((α z y : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L))) :=
  ⟨PDivAlphaZero.α D, fun v f y ψ hψ => PDivAlphaZero.α_level D v f y ψ hψ,
    fun σ z y => PDivAlphaZero.α_smul_rep D σ z y⟩

end S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair (solution)
