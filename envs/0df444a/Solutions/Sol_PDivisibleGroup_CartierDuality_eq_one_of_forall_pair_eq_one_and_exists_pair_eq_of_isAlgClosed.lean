-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d9fc8523-c838-52d1-bc42-d1e2f074808d

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_Algebra_Etale_eq_of_forall_algHom_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed

set_option autoImplicit false

open PDivisibleGroup
open scoped TensorProduct

namespace PDivLevelPerfect

variable {R : Type} [CommRing R] {p h : ℕ}

section Count

variable (G : PDivisibleGroup R p h) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

theorem natCard_point (n : ℕ) : Nat.card (G.Point K n) = p ^ (n * h) := by
  rw [← G.finrank_level n]
  change Nat.card (WithConv (G.level n →ₐ[R] K)) = _
  rw [Nat.card_congr (WithConv.equiv (G.level n →ₐ[R] K))]
  exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R (G.level n) K

theorem finite_point [Fact p.Prime] (n : ℕ) : Finite (G.Point K n) :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_point]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end Count

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
    dualPt D v (ψ * ψ') =
      WithConv.ofConv (WithConv.toConv (dualPt D v ψ) * WithConv.toConv (dualPt D v ψ')) := by
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
  have h1 := pair_mul_right D v f 1 1
  rw [mul_one] at h1

  have hunit : D.pair L v f 1 * D.pair L v f 1 = D.pair L v f 1 * 1 := by rw [mul_one, ← h1]

  have hu : IsUnit (D.pair L v f 1) := by
    refine isUnit_iff_exists_inv.mpr ⟨D.pair L v f⁻¹ 1, ?_⟩
    rw [← pair_mul_left, mul_inv_cancel, pair_one_left]
  exact hu.mul_left_cancel hunit

theorem pair_pow_left (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) (n : ℕ) :
    D.pair L v (f ^ n) ψ = D.pair L v f ψ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pair_one_left]
  | succ n ih => rw [pow_succ, pow_succ, pair_mul_left, ih]

theorem pair_pow_card (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ ^ (p ^ v) = 1 := by
  rw [← pair_pow_left, Point.pow_card_eq_one, pair_one_left]

variable [Fact p.Prime]

noncomputable def pairUnit (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) : Lˣ :=
  (IsUnit.of_pow_eq_one (pair_pow_card D v f ψ) (pow_ne_zero v (Fact.out : p.Prime).ne_zero)).unit

@[scoped simp] theorem val_pairUnit (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    ((pairUnit D v f ψ : Lˣ) : L) = D.pair L v f ψ :=
  IsUnit.unit_spec _

theorem pairUnit_mul_left (v : ℕ) (f g : G.Point L v) (ψ : G'.Point L v) :
    pairUnit D v (f * g) ψ = pairUnit D v f ψ * pairUnit D v g ψ := by
  ext; rw [Units.val_mul, val_pairUnit, val_pairUnit, val_pairUnit, pair_mul_left]

theorem pairUnit_mul_right (v : ℕ) (f : G.Point L v) (ψ ψ' : G'.Point L v) :
    pairUnit D v f (ψ * ψ') = pairUnit D v f ψ * pairUnit D v f ψ' := by
  ext; rw [Units.val_mul, val_pairUnit, val_pairUnit, val_pairUnit, pair_mul_right]

theorem pairUnit_one_left (v : ℕ) (ψ : G'.Point L v) : pairUnit D v 1 ψ = 1 := by
  ext; rw [val_pairUnit, pair_one_left, Units.val_one]

theorem pairUnit_one_right (v : ℕ) (f : G.Point L v) : pairUnit D v f 1 = 1 := by
  ext; rw [val_pairUnit, pair_one_right, Units.val_one]

noncomputable def charOf (v : ℕ) (ψ : G'.Point L v) : G.Point L v →* Lˣ where
  toFun f := pairUnit D v f ψ
  map_one' := pairUnit_one_left D v ψ
  map_mul' f g := pairUnit_mul_left D v f g ψ

theorem charOf_apply (v : ℕ) (ψ : G'.Point L v) (f : G.Point L v) :
    charOf D v ψ f = pairUnit D v f ψ := rfl

noncomputable def charOf' (v : ℕ) (f : G.Point L v) : G'.Point L v →* Lˣ where
  toFun ψ := pairUnit D v f ψ
  map_one' := pairUnit_one_right D v f
  map_mul' ψ ψ' := pairUnit_mul_right D v f ψ ψ'

theorem charOf'_apply (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    charOf' D v f ψ = pairUnit D v f ψ := rfl

end Level

section NondegRight

variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

noncomputable def lam (v : ℕ) (ψ : G'.Point K v) : Module.Dual R (G.level v) →ₗ[R] K :=
  (Point.toAlgHom ψ).toLinearMap ∘ₗ (D.toDualEquiv v).symm.toLinearMap

omit [IsAlgClosed K] [CharZero K] in
theorem lam_apply (v : ℕ) (ψ : G'.Point K v) (φ : Module.Dual R (G.level v)) :
    lam D K v ψ φ = Point.toAlgHom ψ ((D.toDualEquiv v).symm φ) := rfl

omit [IsAlgClosed K] [CharZero K] in
theorem pair_eq_sum_lam (v : ℕ) (f : G.Point K v) (ψ : G'.Point K v) :
    D.pair K v f ψ = ∑ i, Point.toAlgHom f (bas G v i) * lam D K v ψ ((bas G v).coord i) := rfl

theorem eq_one_of_forall_pair_eq_one (v : ℕ) (ψ : G'.Point K v)
    (hψ : ∀ f : G.Point K v, D.pair K v f ψ = 1) : ψ = 1 := by
  classical
  set A := G.level v
  set b := bas G v
  set lamψ := lam D K v ψ with hlam

  haveI : Algebra.Etale K (K ⊗[R] A) :=
    HopfAlgebra.algebra_etale_of_module_finite_of_charZero K (K ⊗[R] A)

  set g : K ⊗[R] A := ∑ i, lamψ (b.coord i) ⊗ₜ[R] b i with hg

  have hgχ : ∀ χ : K ⊗[R] A →ₐ[K] K, χ g = χ 1 := by
    intro χ
    let fa : A →ₐ[R] K := (χ.restrictScalars R).comp Algebra.TensorProduct.includeRight
    have hχ : ∀ (c : K) (a : A), χ (c ⊗ₜ[R] a) = c * fa a := by
      intro c a
      have : c ⊗ₜ[R] a = algebraMap K (K ⊗[R] A) c * ((1 : K) ⊗ₜ[R] a) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          Algebra.algebraMap_self, RingHom.id_apply, one_mul]
      rw [this, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      rfl
    rw [map_one, hg, map_sum]
    simp_rw [hχ]
    have := hψ (Point.ofAlgHom fa)
    rw [pair_eq_sum_lam] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    rfl

  have hg1 : g = 1 :=
    Algebra.Etale.eq_of_forall_algHom_apply_eq (K := K) (Ω := K) hgχ

  have hlamφ : ∀ φ : Module.Dual R A, lamψ φ = algebraMap R K (φ 1) := by
    intro φ
    let Tφ : K ⊗[R] A →ₗ[R] K := (TensorProduct.rid R K).toLinearMap ∘ₗ LinearMap.lTensor K φ
    have hT : ∀ (c : K) (a : A), Tφ (c ⊗ₜ[R] a) = φ a • c := by
      intro c a
      simp [Tφ]
    have h1 : Tφ g = lamψ φ := by
      rw [hg, map_sum]
      simp_rw [hT, ← map_smul lamψ]
      rw [← map_sum, Module.Basis.sum_dual_apply_smul_coord]
    have h2 : Tφ 1 = algebraMap R K (φ 1) := by
      rw [Algebra.TensorProduct.one_def, hT, Algebra.smul_def, mul_one]
    rw [← h1, hg1, h2]

  refine Point.ext fun x => ?_
  rw [Point.one_apply]
  have := hlamφ (D.toDualEquiv v x)
  rw [hlam, lam_apply, LinearEquiv.symm_apply_apply] at this
  rw [this, CartierDuality.toDualEquiv_apply, ← D.counit_eq_equiv_apply_one]

end NondegRight

section Counting

variable [Fact p.Prime]
variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

theorem charOf_injective (v : ℕ) : Function.Injective (charOf (L := K) D v) := by
  intro ψ ψ' hψψ'
  have key : ∀ g : G.Point K v, D.pair K v g (ψ * ψ'⁻¹) = 1 := by
    intro g
    have h1 : pairUnit D v g ψ = pairUnit D v g ψ' := DFunLike.congr_fun hψψ' g
    have h2 : pairUnit D v g (ψ * ψ'⁻¹) * pairUnit D v g ψ' = pairUnit D v g ψ := by
      rw [← pairUnit_mul_right, inv_mul_cancel_right]
    have h3 : pairUnit D v g (ψ * ψ'⁻¹) = 1 :=
      mul_right_cancel (h2.trans (h1.trans (one_mul _).symm))
    rw [← val_pairUnit, h3, Units.val_one]
  have := eq_one_of_forall_pair_eq_one D K v (ψ * ψ'⁻¹) key
  rwa [mul_inv_eq_one] at this

theorem charOf_bijective (v : ℕ) : Function.Bijective (charOf (L := K) D v) := by
  haveI := finite_point G K v
  haveI := finite_point G' K v
  haveI : NeZero ((Monoid.exponent (G.Point K v) : ℕ) : K) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  refine (charOf_injective D K v).bijective_of_nat_card_le (le_of_eq ?_)
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, natCard_point G K v, natCard_point G' K v]

theorem eq_one_of_forall_pair_eq_one_left (v : ℕ) (f : G.Point K v)
    (hf : ∀ ψ : G'.Point K v, D.pair K v f ψ = 1) : f = 1 := by
  haveI := finite_point G K v
  haveI : NeZero ((Monoid.exponent (G.Point K v) : ℕ) : K) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  by_contra hne
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G.Point K v) K hne
  obtain ⟨ψ, rfl⟩ := (charOf_bijective D K v).2 χ
  apply hχ
  ext
  rw [charOf_apply, val_pairUnit, hf, Units.val_one]

theorem charOf'_injective (v : ℕ) : Function.Injective (charOf' (L := K) D v) := by
  intro f f' hff'
  have key : ∀ ψ : G'.Point K v, D.pair K v (f * f'⁻¹) ψ = 1 := by
    intro ψ
    have h1 : pairUnit D v f ψ = pairUnit D v f' ψ := DFunLike.congr_fun hff' ψ
    have h2 : pairUnit D v (f * f'⁻¹) ψ * pairUnit D v f' ψ = pairUnit D v f ψ := by
      rw [← pairUnit_mul_left, inv_mul_cancel_right]
    have h3 : pairUnit D v (f * f'⁻¹) ψ = 1 :=
      mul_right_cancel (h2.trans (h1.trans (one_mul _).symm))
    rw [← val_pairUnit, h3, Units.val_one]
  have := eq_one_of_forall_pair_eq_one_left D K v (f * f'⁻¹) key
  rwa [mul_inv_eq_one] at this

theorem charOf'_bijective (v : ℕ) : Function.Bijective (charOf' (L := K) D v) := by
  haveI := finite_point G K v
  haveI := finite_point G' K v
  haveI : NeZero ((Monoid.exponent (G'.Point K v) : ℕ) : K) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  refine (charOf'_injective D K v).bijective_of_nat_card_le (le_of_eq ?_)
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, natCard_point G K v, natCard_point G' K v]

end Counting

end PDivLevelPerfect
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed.PDivLevelPerfect"

open PDivLevelPerfect in

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
    (v : ℕ) :
    (∀ f : G.Point K v, (∀ ψ : G'.Point K v, D.pair K v f ψ = 1) → f = 1) ∧
    (∀ ψ : G'.Point K v, (∀ f : G.Point K v, D.pair K v f ψ = 1) → ψ = 1) ∧
    (∀ χ : G'.Point K v →* Kˣ, ∃ f : G.Point K v, ∀ ψ : G'.Point K v, D.pair K v f ψ = χ ψ) ∧
    (∀ χ : G.Point K v →* Kˣ, ∃ ψ : G'.Point K v, ∀ f : G.Point K v, D.pair K v f ψ = χ f) := by
  refine ⟨eq_one_of_forall_pair_eq_one_left D K v, eq_one_of_forall_pair_eq_one D K v, ?_, ?_⟩
  · intro χ
    obtain ⟨f, rfl⟩ := (charOf'_bijective D K v).2 χ
    exact ⟨f, fun ψ => by rw [charOf'_apply, val_pairUnit]⟩
  · intro χ
    obtain ⟨ψ, rfl⟩ := (charOf_bijective D K v).2 χ
    exact ⟨ψ, fun f => by rw [charOf_apply, val_pairUnit]⟩

end S_PDivisibleGroup_CartierDuality_eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed (solution)
