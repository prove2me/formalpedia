-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.bijective_tateModule_pairing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f7310cab-736f-59a7-a56e-52b074289c69

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_Algebra_Etale_eq_of_forall_algHom_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false

open PDivisibleGroup
open scoped TensorProduct

namespace PDivPerfect

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

private theorem _root_.PDivPerfect.mem_torsionBy_iff (n : ℕ) (z : G.Points L) :
    z ∈ Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ) ↔
      ∃ x : G.Point L n, G.pointsMkAdd L n (Additive.ofMul x) = z := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  refine ⟨exists_point_of_nsmul_eq_zero G n z, ?_⟩
  rintro ⟨x, rfl⟩
  exact G.nsmul_pointsMkAdd_eq_zero n x

p2m_export "PDivPerfect" "mem_torsionBy_iff"

noncomputable def pointEquivTorsionBy (n : ℕ) :
    G.Point L n ≃ Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ) :=
  Equiv.ofBijective (fun x => ⟨G.pointsMkAdd L n (Additive.ofMul x), (mem_torsionBy_iff G n _).2 ⟨x, rfl⟩⟩)
    ⟨fun x y hxy => G.pointsMkAdd_injective n (congrArg Subtype.val hxy),
     fun z => by
      obtain ⟨x, hx⟩ := (mem_torsionBy_iff G n z.1).1 z.2
      exact ⟨x, Subtype.ext hx⟩⟩

section Count

variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

theorem natCard_point (n : ℕ) : Nat.card (G.Point K n) = p ^ (n * h) := by
  rw [← G.finrank_level n]
  change Nat.card (WithConv (G.level n →ₐ[R] K)) = _
  rw [Nat.card_congr (WithConv.equiv (G.level n →ₐ[R] K))]
  exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R (G.level n) K

theorem natCard_torsionBy (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (G.Points K) ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ h := by
  rw [← pow_mul, ← natCard_point G K n]
  exact (Nat.card_congr (pointEquivTorsionBy G n)).symm

scoped instance finite_point [Fact p.Prime] (n : ℕ) : Finite (G.Point K n) :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_point]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end Count

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

end Level

section NondegRight

variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

noncomputable def lam (v : ℕ) (ψ : G'.Point K v) : Module.Dual R (G.level v) →ₗ[R] K :=
  (Point.toAlgHom ψ).toLinearMap ∘ₗ (D.toDualEquiv v).symm.toLinearMap

theorem lam_apply (v : ℕ) (ψ : G'.Point K v) (φ : Module.Dual R (G.level v)) :
    lam D K v ψ φ = Point.toAlgHom ψ ((D.toDualEquiv v).symm φ) := rfl

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

section NondegLeft

variable [Fact p.Prime]
variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

noncomputable def charOf (v : ℕ) (ψ : G'.Point K v) : G.Point K v →* Kˣ where
  toFun f := pairUnit D v f ψ
  map_one' := pairUnit_one_left D v ψ
  map_mul' f g := pairUnit_mul_left D v f g ψ

theorem charOf_apply (v : ℕ) (ψ : G'.Point K v) (f : G.Point K v) : charOf D K v ψ f = pairUnit D v f ψ := rfl

theorem charOf_injective (v : ℕ) : Function.Injective (charOf D K v) := by
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

theorem charOf_bijective (v : ℕ) : Function.Bijective (charOf D K v) := by
  haveI : NeZero ((Monoid.exponent (G.Point K v) : ℕ) : K) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  refine (charOf_injective D K v).bijective_of_nat_card_le (le_of_eq ?_)
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, natCard_point G K v, natCard_point G' K v]

theorem eq_one_of_forall_pair_eq_one_left (v : ℕ) (f : G.Point K v)
    (hf : ∀ ψ : G'.Point K v, D.pair K v f ψ = 1) : f = 1 := by
  haveI : NeZero ((Monoid.exponent (G.Point K v) : ℕ) : K) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  by_contra hne
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G.Point K v) K hne
  obtain ⟨ψ, rfl⟩ := (charOf_bijective D K v).2 χ
  apply hχ
  ext
  rw [charOf_apply, val_pairUnit, hf, Units.val_one]

end NondegLeft

section TateLift

open Submodule TateModule

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] {r : ℕ}

theorem finite_torsionBy_of_card
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) (n : ℕ) :
    Finite (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :=
  Nat.finite_of_card_ne_zero (by
    rw [hcard n]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

theorem mulP_surjective_of_card
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) (n : ℕ) :
    Function.Surjective (mulP p M n) := by
  haveI := finite_torsionBy_of_card hcard (n + 1)
  haveI := finite_torsionBy_of_card hcard n
  have hker : Nat.card (mulP p M n).ker = p ^ r := by
    rw [Nat.card_congr (kerMulPEquiv p M n), hcard 1, pow_one]
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (mulP p M n).ker
  rw [hcard (n + 1), Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulP p M n)).toEquiv, hker] at h
  have hrange : Nat.card (mulP p M n).range = Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) := by
    rw [hcard n]
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos r) ?_
    rw [← h]; ring
  rw [← AddMonoidHom.range_eq_top]
  exact AddSubgroup.eq_top_of_card_eq _ hrange

theorem exists_proj_eq_of_card
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) (n : ℕ)
    (m : M) (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) : ∃ x : TateModule p M, proj p M n x = m := by
  choose next hnext using fun k (m : torsionBy ℤ M ((p ^ k : ℕ) : ℤ)) => mulP_surjective_of_card hcard k m
  refine ⟨⟨liftFun next n ⟨m, hm⟩, liftFun_mem (fun k m => congrArg Subtype.val (hnext k m)) n ⟨m, hm⟩⟩, ?_⟩
  rw [proj_apply]
  change liftFun next n ⟨m, hm⟩ n = m
  rw [liftFun_of_le le_rfl, coe_liftAux_congr (Nat.sub_self n)]
  rfl

theorem finite_quotient_of_card
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    Finite (TateModule p M ⧸
      ((IsLocalRing.maximalIdeal ℤ_[p]) • ⊤ : Submodule ℤ_[p] (TateModule p M))) := by
  haveI := finite_torsionBy_of_card hcard 1
  have hlift : ∀ m : torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ), ∃ x : TateModule p M, proj p M 1 x = m :=
    fun m => exists_proj_eq_of_card hcard 1 m m.2
  choose lift hlift using hlift
  refine Finite.of_surjective (fun m => Submodule.Quotient.mk (lift m)) fun z => ?_
  induction z using Submodule.Quotient.induction_on with
  | _ y =>
    refine ⟨⟨proj p M 1 y, proj_mem_torsionBy 1 y⟩, ?_⟩
    apply (Submodule.Quotient.eq _).2
    rw [← pow_one (IsLocalRing.maximalIdeal ℤ_[p]), ← proj_eq_zero_iff, map_sub, hlift, sub_self]

end TateLift

section RootsOfUnity

open Submodule

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] [CharZero K]

theorem natCard_torsionBy_units (n : ℕ) :
    Nat.card (torsionBy ℤ (Additive Kˣ) ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 1 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero ((p ^ n : ℕ) : K) := NeZero.charZero
  have e : torsionBy ℤ (Additive Kˣ) ((p ^ n : ℕ) : ℤ) ≃ rootsOfUnity (p ^ n) K :=
    ⟨fun u => ⟨Additive.toMul u.1, by
        have hu := u.2
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at hu
        rw [mem_rootsOfUnity]
        exact congrArg Additive.toMul hu⟩,
     fun ζ => ⟨Additive.ofMul ζ.1, by
        have hζ := ζ.2
        rw [mem_rootsOfUnity] at hζ
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
        exact congrArg Additive.ofMul hζ⟩,
     fun u => rfl, fun ζ => rfl⟩
  rw [pow_one, Nat.card_congr e, HasEnoughRootsOfUnity.natCard_rootsOfUnity K (p ^ n)]

theorem nonempty_basis_tate_units :
    Nonempty (Module.Basis (Fin 1) ℤ_[p] (TateModule p (Additive Kˣ))) :=
  TateModule.nonempty_basis_of_card_torsionBy p 1 (natCard_torsionBy_units p K)

end RootsOfUnity

section LocalCriterion

open Submodule

theorem bijective_of_forall_mem_smul_top {A : Type*} [CommRing A] {N P : Type*}
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] [Module.Finite A N]
    {I : Ideal A} (hI : I ≤ Ideal.jacobson ⊥)
    (hfin : Finite (N ⧸ (I • ⊤ : Submodule A N)))
    (g : P ≃ₗ[A] N) (f : N →ₗ[A] P)
    (hf : ∀ y : N, f y ∈ (I • ⊤ : Submodule A P) → y ∈ (I • ⊤ : Submodule A N)) :
    Function.Bijective f := by
  set e : N →ₗ[A] N := g.toLinearMap ∘ₗ f with he_def
  have he_apply : ∀ y, e y = g (f y) := fun y => rfl

  have hle : (I • ⊤ : Submodule A N) ≤ (I • ⊤ : Submodule A N).comap e := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top

  have he : ∀ y : N, e y ∈ (I • ⊤ : Submodule A N) → y ∈ (I • ⊤ : Submodule A N) := by
    intro y hy
    apply hf
    have hfy : f y = g.symm.toLinearMap (e y) := by
      rw [he_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hfy]
    have h2 : Submodule.map g.symm.toLinearMap (I • ⊤ : Submodule A N) ≤ I • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h2 (Submodule.mem_map_of_mem hy)

  set ebar := Submodule.mapQ (I • ⊤ : Submodule A N) (I • ⊤ : Submodule A N) e hle with hebar
  have hinj : Function.Injective ebar := by
    intro z z' hzz'
    induction z using Submodule.Quotient.induction_on with
    | _ y =>
      induction z' using Submodule.Quotient.induction_on with
      | _ y' =>
        rw [hebar, Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq, ← map_sub] at hzz'
        exact (Submodule.Quotient.eq _).2 (he _ hzz')
  have hsurj : Function.Surjective ebar := Finite.surjective_of_injective hinj

  have hsup : (⊤ : Submodule A N) ≤ LinearMap.range e ⊔ I • ⊤ := by
    intro z _
    obtain ⟨w, hw⟩ := hsurj (Submodule.Quotient.mk z)
    induction w using Submodule.Quotient.induction_on with
    | _ y =>
      rw [hebar, Submodule.mapQ_apply, Submodule.Quotient.eq] at hw
      refine Submodule.mem_sup.2 ⟨e y, LinearMap.mem_range_self e y, z - e y, ?_, by abel⟩
      have := Submodule.neg_mem _ hw
      rwa [neg_sub] at this

  have htop : (⊤ : Submodule A N) ≤ LinearMap.range e :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI hsup
  have hesurj : Function.Surjective e := LinearMap.range_eq_top.1 (top_le_iff.1 htop)
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, hy⟩ := hesurj (g z)
    exact ⟨y, g.injective (by rw [← he_apply, hy])⟩

  haveI : Module.Finite A P := Module.Finite.equiv g.symm
  exact OrzechProperty.bijective_of_surjective_of_injective g.symm.toLinearMap f g.symm.injective hfsurj

end LocalCriterion

section Abstract

open Submodule TateModule

variable {p : ℕ} [Fact p.Prime]

theorem bijective_of_level_one {M N : Type} [AddCommGroup M] [AddCommGroup N] {r : ℕ}
    (hM : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (hN : ∀ n : ℕ, Nat.card (torsionBy ℤ N ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    {P : Type} [AddCommGroup P] [Module ℤ_[p] P] [Module.Free ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (hP : Module.finrank ℤ_[p] P = 1)
    (F : TateModule p N →ₗ[ℤ_[p]] TateModule p M →ₗ[ℤ_[p]] P)
    (hF : ∀ y : TateModule p N,
      (∀ x : TateModule p M, F y x ∈ ((IsLocalRing.maximalIdeal ℤ_[p]) • ⊤ : Submodule ℤ_[p] P)) →
        proj p N 1 y = 0) :
    Function.Bijective F := by
  set 𝔪 := IsLocalRing.maximalIdeal ℤ_[p] with h𝔪

  obtain ⟨bM⟩ := TateModule.nonempty_basis_of_card_torsionBy p r hM
  obtain ⟨bN⟩ := TateModule.nonempty_basis_of_card_torsionBy p r hN
  haveI : Module.Free ℤ_[p] (TateModule p M) := Module.Free.of_basis bM
  haveI : Module.Finite ℤ_[p] (TateModule p M) := Module.Finite.of_basis bM
  haveI : Module.Free ℤ_[p] (TateModule p N) := Module.Free.of_basis bN
  haveI : Module.Finite ℤ_[p] (TateModule p N) := Module.Finite.of_basis bN
  have hrkM : Module.finrank ℤ_[p] (TateModule p M) = r := by
    rw [Module.finrank_eq_card_basis bM, Fintype.card_fin]
  have hrkN : Module.finrank ℤ_[p] (TateModule p N) = r := by
    rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]

  have hrkH : Module.finrank ℤ_[p] (TateModule p M →ₗ[ℤ_[p]] P) = Module.finrank ℤ_[p] (TateModule p N) := by
    rw [Module.finrank_linearMap, hP, mul_one, hrkM, hrkN]
  let g : (TateModule p M →ₗ[ℤ_[p]] P) ≃ₗ[ℤ_[p]] TateModule p N := LinearEquiv.ofFinrankEq _ _ hrkH

  have hF' : ∀ y : TateModule p N,
      F y ∈ (𝔪 • ⊤ : Submodule ℤ_[p] (TateModule p M →ₗ[ℤ_[p]] P)) →
        y ∈ (𝔪 • ⊤ : Submodule ℤ_[p] (TateModule p N)) := by
    intro y hy
    rw [h𝔪, PadicInt.maximalIdeal_eq_span_p, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨Φ, -, hΦ⟩ := hy
    have h1 : proj p N 1 y = 0 := by
      apply hF
      intro x
      rw [← hΦ, LinearMap.smul_apply]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [h𝔪, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    have := (proj_eq_zero_iff 1 y).1 h1
    rwa [pow_one] at this
  exact bijective_of_forall_mem_smul_top (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    (finite_quotient_of_card hN) g F hF'

end Abstract

section Assembly

open Submodule TateModule

variable [Fact p.Prime]
variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

theorem exists_tate_apply_eq (G : PDivisibleGroup R p h) (v : ℕ) (f : G.Point K v) :
    ∃ x : TateModule p (G.Points K), (x : ℕ → G.Points K) v = G.pointsMkAdd K v (Additive.ofMul f) := by
  obtain ⟨x, hx⟩ := exists_proj_eq_of_card (natCard_torsionBy G K) v
    (G.pointsMkAdd K v (Additive.ofMul f)) ((mem_torsionBy_iff G v _).2 ⟨f, rfl⟩)
  exact ⟨x, hx⟩

variable (B : TateModule p (G.Points K) →ₗ[ℤ_[p]] TateModule p (G'.Points K) →ₗ[ℤ_[p]]
  TateModule p (Additive Kˣ))
variable (hB : ∀ (x : TateModule p (G.Points K)) (y : TateModule p (G'.Points K)) (v : ℕ)
  (f : G.Point K v) (ψ : G'.Point K v),
  G.pointsMkAdd K v (Additive.ofMul f) = (x : ℕ → G.Points K) v →
  G'.pointsMkAdd K v (Additive.ofMul ψ) = (y : ℕ → G'.Points K) v →
  ((Additive.toMul ((B x y : ℕ → Additive Kˣ) v) : Kˣ) : K) = D.pair K v f ψ)

include hB

theorem pair_lift_one_eq_one (x : TateModule p (G.Points K)) (y : TateModule p (G'.Points K))
    (hxy : B x y ∈ ((IsLocalRing.maximalIdeal ℤ_[p]) • ⊤ : Submodule ℤ_[p] (TateModule p (Additive Kˣ)))) :
    D.pair K 1 (lift G x 1) (lift G' y 1) = 1 := by
  have h0 : proj p (Additive Kˣ) 1 (B x y) = 0 := by
    rw [proj_eq_zero_iff, pow_one]
    exact hxy
  rw [← hB x y 1 (lift G x 1) (lift G' y 1) (pointsMkAdd_lift G x 1) (pointsMkAdd_lift G' y 1)]
  rw [proj_apply] at h0
  rw [h0]
  rfl

theorem proj_one_eq_zero_right (y : TateModule p (G'.Points K))
    (hy : ∀ x : TateModule p (G.Points K),
      B.flip y x ∈ ((IsLocalRing.maximalIdeal ℤ_[p]) • ⊤ : Submodule ℤ_[p] (TateModule p (Additive Kˣ)))) :
    proj p (G'.Points K) 1 y = 0 := by
  have hψ : lift G' y 1 = 1 := by
    apply eq_one_of_forall_pair_eq_one D K 1
    intro f
    obtain ⟨x, hx⟩ := exists_tate_apply_eq K G 1 f
    have h := pair_lift_one_eq_one D K B hB x y (hy x)
    rwa [← lift_unique G hx.symm] at h
  rw [proj_apply, ← pointsMkAdd_lift G' y 1, hψ, ofMul_one, map_zero]

theorem proj_one_eq_zero_left (x : TateModule p (G.Points K))
    (hx : ∀ y : TateModule p (G'.Points K),
      B x y ∈ ((IsLocalRing.maximalIdeal ℤ_[p]) • ⊤ : Submodule ℤ_[p] (TateModule p (Additive Kˣ)))) :
    proj p (G.Points K) 1 x = 0 := by
  have hf : lift G x 1 = 1 := by
    apply eq_one_of_forall_pair_eq_one_left D K 1
    intro ψ
    obtain ⟨y, hy⟩ := exists_tate_apply_eq K G' 1 ψ
    have h := pair_lift_one_eq_one D K B hB x y (hx y)
    rwa [← lift_unique G' hy.symm] at h
  rw [proj_apply, ← pointsMkAdd_lift G x 1, hf, ofMul_one, map_zero]

theorem bijective_flip_and_bijective : Function.Bijective B.flip ∧ Function.Bijective B := by
  obtain ⟨bμ⟩ := nonempty_basis_tate_units p K
  haveI : Module.Free ℤ_[p] (TateModule p (Additive Kˣ)) := Module.Free.of_basis bμ
  haveI : Module.Finite ℤ_[p] (TateModule p (Additive Kˣ)) := Module.Finite.of_basis bμ
  have hrk : Module.finrank ℤ_[p] (TateModule p (Additive Kˣ)) = 1 := by
    rw [Module.finrank_eq_card_basis bμ, Fintype.card_fin]
  refine ⟨?_, ?_⟩
  · exact bijective_of_level_one (natCard_torsionBy G K) (natCard_torsionBy G' K) hrk B.flip
      (proj_one_eq_zero_right D K B hB)
  · exact bijective_of_level_one (natCard_torsionBy G' K) (natCard_torsionBy G K) hrk B
      (proj_one_eq_zero_left D K B hB)

end Assembly

end PDivPerfect
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed.PDivPerfect"

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (B : TateModule p (G.Points L) →ₗ[ℤ_[p]] TateModule p (G'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hB : ∀ (x : TateModule p (G.Points L)) (y : TateModule p (G'.Points L)) (v : ℕ)
      (f : G.Point L v) (ψ : G'.Point L v),
      G.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → G.Points L) v →
      G'.pointsMkAdd L v (Additive.ofMul ψ) = (y : ℕ → G'.Points L) v →
      ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f ψ) :
    Function.Bijective B.flip ∧ Function.Bijective B :=
  PDivPerfect.bijective_flip_and_bijective D L B hB

end S_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed (solution)
