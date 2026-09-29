-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9cb12c86-b3c6-55d8-8e66-dea8bb17c60c

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose
import Theorems.Thm_PDivisibleGroup_CartierDuality_eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open PDivisibleGroup Coalgebra WithConv
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

namespace PDivMTower

variable {R : Type} [CommRing R] {p h : ℕ}

section Level

variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable {L : Type} [CommRing L] [Algebra R L]

noncomputable abbrev eS (v : ℕ) : CartierDual R (G.level v) →ₐc[R] G'.level v :=
  ((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v)

def dualPt (v : ℕ) (ψ : G'.Point L v) : CartierDual R (G.level v) →ₐ[R] L :=
  (Point.toAlgHom ψ).comp (eS D v : CartierDual R (G.level v) →ₐ[R] G'.level v)

theorem dualPt_apply (v : ℕ) (ψ : G'.Point L v) (φ : CartierDual R (G.level v)) :
    dualPt D v ψ φ = Point.toAlgHom ψ ((D.equiv v).symm φ) := rfl

noncomputable abbrev bas (G : PDivisibleGroup R p h) (v : ℕ) := Module.Free.chooseBasis R (G.level v)

theorem pair_eq (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ = ∑ i, (Point.toAlgHom f) (bas G v i) *
      dualPt D v ψ (CartierDual.ofDual R (G.level v) ((bas G v).coord i)) := by
  rw [CartierDuality.pair_def]; rfl

theorem pair_eq_conv (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ = ∑ i, (Point.toConv f) (bas G v i) *
      dualPt D v ψ (CartierDual.ofDual R (G.level v) ((bas G v).coord i)) := pair_eq D v f ψ

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

theorem pair_pow_card (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) : D.pair L v f ψ ^ (p ^ v) = 1 := by
  rw [← pair_pow_left, Point.pow_card_eq_one, pair_one_left]

theorem pair_inv_right (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ * D.pair L v f ψ⁻¹ = 1 := by
  rw [← pair_mul_right, mul_inv_cancel, pair_one_right]

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

section Fin

variable [Fact p.Prime] (G : PDivisibleGroup R p h) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

theorem natCard_point (n : ℕ) : Nat.card (G.Point K n) = p ^ (n * h) := by
  rw [← G.finrank_level n]
  change Nat.card (WithConv (G.level n →ₐ[R] K)) = _
  rw [Nat.card_congr (WithConv.equiv (G.level n →ₐ[R] K))]
  exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R (G.level n) K

scoped instance finite_point (n : ℕ) : Finite (G.Point K n) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_point]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

private theorem _root_.PDivMTower.hasEnoughRootsOfUnity (Γ : Type) [CommGroup Γ] [Finite Γ] : HasEnoughRootsOfUnity K (Monoid.exponent Γ) := by
  haveI : NeZero ((Monoid.exponent Γ : ℕ) : K) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  exact IsSepClosed.hasEnoughRootsOfUnity K _

p2m_export "PDivMTower" "hasEnoughRootsOfUnity"
end Fin

section DoubleAnn

variable [Fact p.Prime] {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

theorem mem_of_forall_pair_eq_one (w : ℕ) (H : Subgroup (G.Point K w)) (z : G.Point K w)
    (hz : ∀ ψ : G'.Point K w, (∀ z' ∈ H, D.pair K w z' ψ = 1) → D.pair K w z ψ = 1) : z ∈ H := by
  haveI := hasEnoughRootsOfUnity K (G.Point K w)
  refine (CommGroup.forall_monoidHom_apply_eq_one_iff (G := G.Point K w) K H z).1 fun φ hφ => ?_
  obtain ⟨ψ, hψ⟩ := (D.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed K w).2.2.2 φ
  apply Units.ext
  rw [Units.val_one, ← hψ z]
  refine hz ψ fun z' hz' => ?_
  rw [hψ z', hφ z' hz', Units.val_one]

end DoubleAnn

section Lift

variable [Fact p.Prime] {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
variable (H : ∀ w : ℕ, Subgroup (G.Point K w))
  (hH : ∀ (w : ℕ) (z : G.Point K w), G.pointIncl K w z ∈ H (w + 1) → z ∈ H w)

def charR (w : ℕ) (ψ : G'.Point K w) : G.Point K w →* Kˣ where
  toFun f := ⟨D.pair K w f ψ, D.pair K w f⁻¹ ψ,
    by rw [← pair_mul_left, mul_inv_cancel, pair_one_left],
    by rw [← pair_mul_left, inv_mul_cancel, pair_one_left]⟩
  map_one' := Units.ext (pair_one_left D w ψ)
  map_mul' f g := Units.ext (pair_mul_left D w f g ψ)

theorem charR_apply (w : ℕ) (ψ : G'.Point K w) (f : G.Point K w) : ((charR D K w ψ f : Kˣ) : K) = D.pair K w f ψ := rfl

include hH in

theorem exists_lift (w : ℕ) (ψ : G'.Point K w) (hψ : ∀ z ∈ H w, D.pair K w z ψ = 1) :
    ∃ Ψ : G'.Point K (w + 1), Ψ ^ p = G'.pointIncl K w ψ ∧ ∀ z ∈ H (w + 1), D.pair K (w + 1) z Ψ = 1 := by

  set Q := G.Point K (w + 1) ⧸ H (w + 1) with hQ
  set π : G.Point K w →* Q := (QuotientGroup.mk' (H (w + 1))).comp (G.pointIncl K w) with hπ
  haveI : Finite Q := inferInstance
  haveI := hasEnoughRootsOfUnity K Q

  have hker : π.ker ≤ (charR D K w ψ).ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz ⊢
    rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
    exact Units.ext (hψ z (hH w z hz))

  set e := QuotientGroup.quotientKerEquivRange π with he
  set θ₁ : π.range →* Kˣ := (QuotientGroup.lift π.ker (charR D K w ψ) hker).comp e.symm.toMonoidHom with hθ₁
  have hθ₁ : ∀ z : G.Point K w, θ₁ ⟨π z, ⟨z, rfl⟩⟩ = charR D K w ψ z := by
    intro z
    have h1 : e (QuotientGroup.mk z) = ⟨π z, ⟨z, rfl⟩⟩ := rfl
    have h2 : e.symm ⟨π z, ⟨z, rfl⟩⟩ = QuotientGroup.mk z := by rw [← h1, MulEquiv.symm_apply_apply]
    rw [hθ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h2, QuotientGroup.lift_mk]

  obtain ⟨Θ, hΘ⟩ := MonoidHom.restrict_surjective K π.range θ₁
  have hΘπ : ∀ z : G.Point K w, Θ (π z) = charR D K w ψ z := by
    intro z
    rw [← hθ₁ z, ← hΘ, MonoidHom.restrictHom_apply]
    rfl

  obtain ⟨Ψ, hΨ⟩ := (D.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed K (w + 1)).2.2.2
    (Θ.comp (QuotientGroup.mk' (H (w + 1))))
  have hΨH : ∀ z ∈ H (w + 1), D.pair K (w + 1) z Ψ = 1 := by
    intro z hz
    rw [hΨ z, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one, Units.val_one]
  have hΨincl : ∀ z : G.Point K w, D.pair K (w + 1) (G.pointIncl K w z) Ψ = D.pair K w z ψ := by
    intro z
    rw [hΨ, MonoidHom.comp_apply]
    change ((Θ (π z) : Kˣ) : K) = _
    rw [hΘπ z, charR_apply]

  have hpow : (Ψ ^ p) ^ (p ^ w) = 1 := by rw [← pow_mul, ← pow_succ', Point.pow_card_eq_one]
  obtain ⟨ψ', hψ'⟩ := G'.exists_pointIncl_eq_of_pow_eq_one w (Ψ ^ p) hpow
  have hadj : ∀ z : G.Point K w, D.pair K w z ψ' = D.pair K w z ψ := by
    intro z
    rw [← hΨincl z, pair_pointIncl_left D w z Ψ ψ' hψ'.symm]
  have hψψ' : ψ' = ψ := by
    have h1 := (D.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed K w).2.1 (ψ' * ψ⁻¹) fun z => by
      rw [pair_mul_right, hadj z, pair_inv_right]
    rw [mul_inv_eq_one] at h1
    exact h1
  refine ⟨Ψ, ?_, hΨH⟩
  rw [← hψ', hψψ']

def seq (ψ₁ : G'.Point K 1) (hψ₁ : ∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) :
    ∀ n : ℕ, {ψ : G'.Point K (n + 1) // ∀ z ∈ H (n + 1), D.pair K (n + 1) z ψ = 1}
  | 0 => ⟨ψ₁, hψ₁⟩
  | n + 1 => ⟨(exists_lift D K H hH (n + 1) (seq ψ₁ hψ₁ n).1 (seq ψ₁ hψ₁ n).2).choose,
      (exists_lift D K H hH (n + 1) (seq ψ₁ hψ₁ n).1 (seq ψ₁ hψ₁ n).2).choose_spec.2⟩

theorem seq_succ_pow (ψ₁ : G'.Point K 1) (hψ₁ : ∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) (n : ℕ) :
    (seq D K H hH ψ₁ hψ₁ (n + 1)).1 ^ p = G'.pointIncl K (n + 1) (seq D K H hH ψ₁ hψ₁ n).1 :=
  (exists_lift D K H hH (n + 1) (seq D K H hH ψ₁ hψ₁ n).1 (seq D K H hH ψ₁ hψ₁ n).2).choose_spec.1

def yFun (ψ₁ : G'.Point K 1) (hψ₁ : ∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) : ℕ → G'.Points K
  | 0 => 0
  | n + 1 => G'.pointsMkAdd K (n + 1) (Additive.ofMul (seq D K H hH ψ₁ hψ₁ n).1)

theorem yFun_mem (ψ₁ : G'.Point K 1) (hψ₁ : ∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) :
    yFun D K H hH ψ₁ hψ₁ ∈ TateModule p (G'.Points K) := by
  intro n
  constructor
  · rw [natCast_zsmul]
    cases n with
    | zero => change p ^ 0 • (0 : G'.Points K) = 0; rw [smul_zero]
    | succ n =>
        change (p ^ (n + 1)) • G'.pointsMkAdd K (n + 1) (Additive.ofMul (seq D K H hH ψ₁ hψ₁ n).1) = 0
        exact G'.nsmul_pointsMkAdd_eq_zero (n + 1) _
  · rw [natCast_zsmul]
    cases n with
    | zero =>
        change p • G'.pointsMkAdd K 1 (Additive.ofMul ψ₁) = (0 : G'.Points K)
        have := G'.nsmul_pointsMkAdd_eq_zero 1 ψ₁
        rwa [pow_one] at this
    | succ n =>
        change p • G'.pointsMkAdd K (n + 1 + 1) (Additive.ofMul (seq D K H hH ψ₁ hψ₁ (n + 1)).1) =
          G'.pointsMkAdd K (n + 1) (Additive.ofMul (seq D K H hH ψ₁ hψ₁ n).1)
        rw [← map_nsmul, ← ofMul_pow, seq_succ_pow, pointsMkAdd_pointIncl]

def y (ψ₁ : G'.Point K 1) (hψ₁ : ∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) : TateModule p (G'.Points K) :=
  ⟨yFun D K H hH ψ₁ hψ₁, yFun_mem D K H hH ψ₁ hψ₁⟩

theorem y_one (ψ₁ : G'.Point K 1) (hψ₁ : ∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) :
    ((y D K H hH ψ₁ hψ₁ : TateModule p (G'.Points K)) : ℕ → G'.Points K) 1 = G'.pointsMkAdd K 1 (Additive.ofMul ψ₁) :=
  rfl

theorem y_spec (ψ₁ : G'.Point K 1) (hψ₁ : ∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) (w : ℕ) (ψ : G'.Point K w)
    (hψ : G'.pointsMkAdd K w (Additive.ofMul ψ) = ((y D K H hH ψ₁ hψ₁ : TateModule p (G'.Points K)) : ℕ → G'.Points K) w)
    (z : G.Point K w) (hz : z ∈ H w) : D.pair K w z ψ = 1 := by
  cases w with
  | zero =>
      have := pair_pow_card D (L := K) 0 z ψ
      rwa [pow_zero, pow_one] at this
  | succ n =>
      have h1 : ψ = (seq D K H hH ψ₁ hψ₁ n).1 :=
        G'.pointsMkAdd_injective (n + 1) hψ
      rw [h1]
      exact (seq D K H hH ψ₁ hψ₁ n).2 z hz

end Lift

end PDivMTower
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one.PDivMTower"

open PDivMTower in

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] :
    (∀ (w : ℕ) (H : Subgroup (G.Point K w)) (z : G.Point K w),
      (∀ ψ : G'.Point K w, (∀ z' ∈ H, D.pair K w z' ψ = 1) → D.pair K w z ψ = 1) → z ∈ H) ∧
    (∀ (H : ∀ w : ℕ, Subgroup (G.Point K w)),
      (∀ (w : ℕ) (z : G.Point K w), G.pointIncl K w z ∈ H (w + 1) → z ∈ H w) →
      ∀ ψ₁ : G'.Point K 1, (∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) →
        ∃ y : TateModule p (G'.Points K),
          (y : ℕ → G'.Points K) 1 = G'.pointsMkAdd K 1 (Additive.ofMul ψ₁) ∧
          ∀ (w : ℕ) (ψ : G'.Point K w),
            G'.pointsMkAdd K w (Additive.ofMul ψ) = (y : ℕ → G'.Points K) w →
            ∀ z ∈ H w, D.pair K w z ψ = 1) :=
  ⟨fun w H z hz => mem_of_forall_pair_eq_one D K w H z hz,
   fun H hH ψ₁ hψ₁ => ⟨y D K H hH ψ₁ hψ₁, y_one D K H hH ψ₁ hψ₁, fun w ψ hψ z hz => y_spec D K H hH ψ₁ hψ₁ w ψ hψ z hz⟩⟩

end
end S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one (solution)
