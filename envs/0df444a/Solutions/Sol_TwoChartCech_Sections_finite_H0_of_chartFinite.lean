-- Prove2me | solution 1 for TwoChartCech.Sections.finite_H0_of_chartFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a209ba81-7ec9-5df4-aa3b-9eca2874bd3d

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_TwoChartCech_Sections_finite_H1_of_chartFinite
import Theorems.Thm_TwoChartCech_kerMap_injective_of_H0_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_Sections_finite_H0_of_chartFinite

set_option autoImplicit false

universe u

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Sections.finite_H1_of_chartFinite kerMap_injective_of_H0_eq_zero"
namespace SerreH0
p2m_open "TwoChartCech"

open Polynomial LaurentPolynomial

variable (R : Type u) [CommRing R]

@[reducible] noncomputable def P1Cover : TwoChartCech.Cover.{u, u} R where
  A0 := R[X]
  A1 := R[X]
  A01 := R[T;T⁻¹]
  ρ0 := Polynomial.toLaurentAlg
  ρ1 := (LaurentPolynomial.invert (R := R)).toAlgHom.comp Polynomial.toLaurentAlg

theorem P1Cover_ρ0_apply (p : R[X]) : (P1Cover R).ρ0 p = Polynomial.toLaurent p := rfl
theorem P1Cover_ρ1_apply (p : R[X]) :
    (P1Cover R).ρ1 p = LaurentPolynomial.invert (Polynomial.toLaurent p) := rfl

@[reducible] noncomputable def twistSections (m a : ℕ) : TwoChartCech.Sections.{u, u, u} (P1Cover R) where
  M0 := Fin m → R[X]
  M1 := Fin m → R[X]
  M01 := Fin m → R[T;T⁻¹]
  r0 :=
    { toFun := fun v i => Polynomial.toLaurent (v i)
      map_add' := fun v w => funext fun i => map_add _ _ _
      map_smul' := fun r v => funext fun i => by
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact map_smul (Polynomial.toLaurentAlg (R := R)) r (v i) }
  r1 :=
    { toFun := fun v i => T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (v i))
      map_add' := fun v w => funext fun i => by
        simp only [Pi.add_apply, map_add, mul_add]
      map_smul' := fun r v => funext fun i => by
        simp only [Pi.smul_apply, RingHom.id_apply]
        have h1 : Polynomial.toLaurent (r • v i) = r • Polynomial.toLaurent (v i) :=
          map_smul (Polynomial.toLaurentAlg (R := R)) r (v i)
        rw [h1, map_smul, mul_smul_comm] }
  r0_smul p v := funext fun i => by
    show Polynomial.toLaurent ((p • v) i) = Polynomial.toLaurent p * Polynomial.toLaurent (v i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  r1_smul p v := funext fun i => by
    show T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent ((p • v) i))
      = LaurentPolynomial.invert (Polynomial.toLaurent p)
          * (T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (v i)))
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring

end TwoChartCech.SerreH0

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Sections.finite_H1_of_chartFinite kerMap_injective_of_H0_eq_zero"
namespace SerreH0
p2m_open "TwoChartCech"
open Polynomial LaurentPolynomial

variable {R : Type u} [CommRing R]

theorem twistSections_r0_apply (m a : ℕ) (v : Fin m → R[X]) (i : Fin m) :
    ((twistSections R m a).r0 v : Fin m → R[T;T⁻¹]) i = Polynomial.toLaurent (v i) := rfl

theorem twistSections_r1_apply (m a : ℕ) (v : Fin m → R[X]) (i : Fin m) :
    ((twistSections R m a).r1 v : Fin m → R[T;T⁻¹]) i
      = T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (v i)) := rfl

theorem twistSections_cechDiff_apply (m a : ℕ) (p : (Fin m → R[X]) × (Fin m → R[X])) (i : Fin m) :
    ((twistSections R m a).cechDiff p : Fin m → R[T;T⁻¹]) i
      = T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (p.2 i))
        - Polynomial.toLaurent (p.1 i) := by
  rw [TwoChartCech.Sections.cechDiff_apply]; rfl

theorem toLaurent_apply_natCast (p : R[X]) (k : ℕ) :
    (Polynomial.toLaurent p : R[T;T⁻¹]).coeff (k : ℤ) = p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent, ← Polynomial.toFinsupp_apply]
  exact Finsupp.mapDomain_apply Nat.cast_injective _ _

theorem toLaurent_apply_of_neg (p : R[X]) {n : ℤ} (hn : n < 0) :
    (Polynomial.toLaurent p : R[T;T⁻¹]).coeff n = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨k, rfl⟩
  exact (not_le.mpr hn) (Int.natCast_nonneg k)

theorem T_mul_apply (n : ℤ) (f : R[T;T⁻¹]) (k : ℤ) :
    (T n * f : R[T;T⁻¹]).coeff k = f.coeff (k - n) := by
  have : (T n * f : R[T;T⁻¹]) = AddMonoidAlgebra.single n (1 : R) * f := rfl
  rw [this, AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (k - n)]
  · rw [one_mul]
  · intro a _
    omega

theorem eq_zero_of_toLaurent_eq_T_neg_mul_invert {a : ℕ} (ha : 1 ≤ a) {p q : R[X]}
    (h : (Polynomial.toLaurent p : R[T;T⁻¹])
      = T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent q)) : p = 0 ∧ q = 0 := by
  have hcoef : ∀ n : ℤ, (Polynomial.toLaurent p : R[T;T⁻¹]).coeff n
      = (Polynomial.toLaurent q : R[T;T⁻¹]).coeff (-(n + a)) := by
    intro n
    rw [h, T_mul_apply, LaurentPolynomial.invert_apply]
    congr 1
    omega
  constructor
  · apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero, ← toLaurent_apply_natCast, hcoef]
    exact toLaurent_apply_of_neg q (by omega)
  · apply Polynomial.ext
    intro k
    have := hcoef (-((k : ℤ) + a))
    rw [show (-(-((k : ℤ) + a) + a)) = (k : ℤ) by omega, toLaurent_apply_natCast] at this
    rw [Polynomial.coeff_zero, ← this]
    exact toLaurent_apply_of_neg p (by omega)

theorem ker_cechDiff_twistSections_eq_bot (m a : ℕ) (ha : 1 ≤ a) :
    LinearMap.ker (twistSections R m a).cechDiff = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨v, w⟩ hvw
  have h : ∀ i, (Polynomial.toLaurent (v i) : R[T;T⁻¹])
      = T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (w i)) := by
    intro i
    have := congrFun hvw i
    rw [twistSections_cechDiff_apply] at this
    change T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (w i)) - Polynomial.toLaurent (v i)
      = (0 : R[T;T⁻¹]) at this
    rw [sub_eq_zero] at this
    exact this.symm
  apply Prod.ext
  · funext i; exact (eq_zero_of_toLaurent_eq_T_neg_mul_invert ha (h i)).1
  · funext i; exact (eq_zero_of_toLaurent_eq_T_neg_mul_invert ha (h i)).2

end TwoChartCech.SerreH0

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Sections.finite_H1_of_chartFinite kerMap_injective_of_H0_eq_zero"
namespace SerreH0
p2m_open "TwoChartCech"
open Polynomial LaurentPolynomial

variable {R : Type u} [CommRing R]

section evalUnit
variable {A : Type u} [CommRing A] [Algebra R A] (u : A) (hu : IsUnit u)

noncomputable def evalUnit : R[T;T⁻¹] →+* A :=
  IsLocalization.Away.lift (X : R[X]) (g := (Polynomial.aeval u : R[X] →ₐ[R] A).toRingHom)
    (by simpa using hu)

theorem evalUnit_toLaurent (p : R[X]) : evalUnit u hu (Polynomial.toLaurent p) = Polynomial.aeval u p := by
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.Away.lift_eq (X : R[X]) _ p

theorem evalUnit_C (r : R) : evalUnit u hu (LaurentPolynomial.C r) = algebraMap R A r := by
  rw [← Polynomial.toLaurent_C, evalUnit_toLaurent, Polynomial.aeval_C]

theorem evalUnit_algebraMap (r : R) : evalUnit u hu (algebraMap R R[T;T⁻¹] r) = algebraMap R A r := by
  have : algebraMap R R[T;T⁻¹] r = LaurentPolynomial.C r := by
    rfl
  rw [this, evalUnit_C]

noncomputable def evalUnitAlg : R[T;T⁻¹] →ₐ[R] A :=
  { evalUnit u hu with commutes' := evalUnit_algebraMap u hu }

theorem evalUnitAlg_apply (ℓ : R[T;T⁻¹]) : evalUnitAlg u hu ℓ = evalUnit u hu ℓ := rfl

theorem evalUnit_T_one : evalUnit u hu (T 1 : R[T;T⁻¹]) = u := by
  rw [← Polynomial.toLaurent_X, evalUnit_toLaurent, Polynomial.aeval_X]

theorem evalUnit_T_natCast (n : ℕ) : evalUnit u hu (T (n : ℤ) : R[T;T⁻¹]) = u ^ n := by
  rw [← Polynomial.toLaurent_X_pow, evalUnit_toLaurent, map_pow, Polynomial.aeval_X]

theorem evalUnit_T_neg_one_mul : evalUnit u hu (T (-1) : R[T;T⁻¹]) * u = 1 := by
  have : evalUnit u hu (T (-1) : R[T;T⁻¹]) * evalUnit u hu (T 1 : R[T;T⁻¹]) = 1 := by
    rw [← map_mul, ← T_add]
    show evalUnit u hu (T 0 : R[T;T⁻¹]) = 1
    rw [LaurentPolynomial.T_zero, map_one]
  rwa [evalUnit_T_one] at this

theorem evalUnit_smul (r : R) (ℓ : R[T;T⁻¹]) : evalUnit u hu (r • ℓ) = r • evalUnit u hu ℓ :=
  map_smul (evalUnitAlg u hu) r ℓ

theorem evalUnit_invert_toLaurent {w : A} (hw : u * w = 1) (p : R[X]) :
    evalUnit u hu (LaurentPolynomial.invert (Polynomial.toLaurent p)) = Polynomial.aeval w p := by

  have key : ((evalUnitAlg u hu).comp ((LaurentPolynomial.invert (R := R)).toAlgHom.comp
      Polynomial.toLaurentAlg)) = Polynomial.aeval w := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom,
      Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X, LaurentPolynomial.invert_T,
      Polynomial.aeval_X, evalUnitAlg_apply]

    have h1 := evalUnit_T_neg_one_mul (R := R) u hu
    calc evalUnit u hu (T (-1) : R[T;T⁻¹]) = evalUnit u hu (T (-1) : R[T;T⁻¹]) * (u * w) := by rw [hw, mul_one]
      _ = (evalUnit u hu (T (-1) : R[T;T⁻¹]) * u) * w := by ring
      _ = w := by rw [h1, one_mul]
  have := congrArg (fun F : R[X] →ₐ[R] A => F p) key
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_algHom,
    Polynomial.toLaurentAlg_apply, evalUnitAlg_apply] using this

end evalUnit

end TwoChartCech.SerreH0

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Sections.finite_H1_of_chartFinite kerMap_injective_of_H0_eq_zero"
namespace SerreH0
p2m_open "TwoChartCech"
open Polynomial LaurentPolynomial

variable {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, u} R}

structure SerreData (S : TwoChartCech.Sections.{u, u, u} 𝒰) (f : 𝒰.A0) (g : 𝒰.A1) where
  m : ℕ
  a : ℕ
  one_le_a : 1 ≤ a
  hu : IsUnit (𝒰.ρ0 f)
  π0 : (Fin m → R[X]) →ₗ[R] S.M0
  π1 : (Fin m → R[X]) →ₗ[R] S.M1
  π01 : (Fin m → R[T;T⁻¹]) →ₗ[R] S.M01
  π0_smul : ∀ (p : R[X]) (v : Fin m → R[X]), π0 (p • v) = Polynomial.aeval f p • π0 v
  π1_smul : ∀ (p : R[X]) (v : Fin m → R[X]), π1 (p • v) = Polynomial.aeval g p • π1 v
  π01_smul : ∀ (ℓ : R[T;T⁻¹]) (w : Fin m → R[T;T⁻¹]), π01 (ℓ • w) = evalUnit (𝒰.ρ0 f) hu ℓ • π01 w
  comm0 : S.r0 ∘ₗ π0 = π01 ∘ₗ (twistSections R m a).r0
  comm1 : S.r1 ∘ₗ π1 = π01 ∘ₗ (twistSections R m a).r1
  surj0 : Function.Surjective π0
  surj1 : Function.Surjective π1
  surj01 : Function.Surjective π01

namespace SerreData

variable {S : TwoChartCech.Sections.{u, u, u} 𝒰} {f : 𝒰.A0} {g : 𝒰.A1} (D : SerreData S f g)

noncomputable def K0 : Submodule R[X] (Fin D.m → R[X]) where
  carrier := {v | D.π0 v = 0}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    rw [map_add, hv, hw, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  smul_mem' p v hv := by
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [D.π0_smul, hv, smul_zero]

noncomputable def K1 : Submodule R[X] (Fin D.m → R[X]) where
  carrier := {v | D.π1 v = 0}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    rw [map_add, hv, hw, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  smul_mem' p v hv := by
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [D.π1_smul, hv, smul_zero]

noncomputable def K01 : Submodule R[T;T⁻¹] (Fin D.m → R[T;T⁻¹]) where
  carrier := {w | D.π01 w = 0}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    rw [map_add, hv, hw, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  smul_mem' p v hv := by
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [D.π01_smul, hv, smul_zero]

theorem mem_K0_iff (v) : v ∈ D.K0 ↔ D.π0 v = 0 := Iff.rfl
theorem mem_K1_iff (v) : v ∈ D.K1 ↔ D.π1 v = 0 := Iff.rfl
theorem mem_K01_iff (w) : w ∈ D.K01 ↔ D.π01 w = 0 := Iff.rfl

theorem r0_mem_K01 {v} (hv : v ∈ D.K0) : (twistSections R D.m D.a).r0 v ∈ D.K01 := by
  rw [mem_K01_iff]
  have := congrArg (fun F => F v) D.comm0
  simp only [LinearMap.comp_apply] at this
  rw [← this, (D.mem_K0_iff v).mp hv, map_zero]

theorem r1_mem_K01 {v} (hv : v ∈ D.K1) : (twistSections R D.m D.a).r1 v ∈ D.K01 := by
  rw [mem_K01_iff]
  have := congrArg (fun F => F v) D.comm1
  simp only [LinearMap.comp_apply] at this
  rw [← this, (D.mem_K1_iff v).mp hv, map_zero]

@[reducible] noncomputable def kerSections : TwoChartCech.Sections.{u, u, u} (P1Cover R) where
  M0 := ↥D.K0
  M1 := ↥D.K1
  M01 := ↥D.K01
  r0 :=
    { toFun := fun v => ⟨(twistSections R D.m D.a).r0 (v : Fin D.m → R[X]), D.r0_mem_K01 v.2⟩
      map_add' := fun v w => Subtype.ext (map_add _ _ _)
      map_smul' := fun r v => Subtype.ext (by
        simp only [Submodule.coe_smul_of_tower, RingHom.id_apply]
        exact map_smul _ r (v : Fin D.m → R[X])) }
  r1 :=
    { toFun := fun v => ⟨(twistSections R D.m D.a).r1 (v : Fin D.m → R[X]), D.r1_mem_K01 v.2⟩
      map_add' := fun v w => Subtype.ext (map_add _ _ _)
      map_smul' := fun r v => Subtype.ext (by
        simp only [Submodule.coe_smul_of_tower, RingHom.id_apply]
        exact map_smul _ r (v : Fin D.m → R[X])) }
  r0_smul p v := Subtype.ext ((twistSections R D.m D.a).r0_smul p (v : Fin D.m → R[X]))
  r1_smul p v := Subtype.ext ((twistSections R D.m D.a).r1_smul p (v : Fin D.m → R[X]))

end SerreData

end TwoChartCech.SerreH0

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Sections.finite_H1_of_chartFinite kerMap_injective_of_H0_eq_zero"
namespace SerreH0
p2m_open "TwoChartCech"
open Polynomial LaurentPolynomial

variable {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, u} R}

section construction

variable (S : TwoChartCech.Sections.{u, u, u} 𝒰) (f : 𝒰.A0) (g : 𝒰.A1)

theorem eq_of_mul_eq_one_of_mul_eq_one {A : Type*} [CommMonoid A] {x y z : A}
    (hx : x * z = 1) (hy : y * z = 1) : x = y := by
  calc x = x * (y * z) := by rw [hy, mul_one]
    _ = y * (x * z) := by rw [mul_left_comm]
    _ = y := by rw [hx, mul_one]

theorem exists_generators_aeval {A : Type u} [CommRing A] [Algebra R A] (a : A)
    (M : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (hfin : Module.Finite (Algebra.adjoin R ({a} : Set A)) M) :
    ∃ (p : ℕ) (e : Fin p → M), ∀ x : M, ∃ c : Fin p → R[X], x = ∑ i, Polynomial.aeval a (c i) • e i := by
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨s.card, fun i => (s.equivFin.symm i : M), fun x => ?_⟩
  have hx : x ∈ Submodule.span (Algebra.adjoin R ({a} : Set A)) (Set.range fun i => ((s.equivFin.symm i : ↥s) : M)) := by
    have hrange : (Set.range fun i => ((s.equivFin.symm i : ↥s) : M)) = (s : Set M) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
      · intro hy; exact ⟨s.equivFin ⟨y, hy⟩, by simp⟩
    rw [hrange, hs]
    exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  have hc' : ∀ i, ∃ q : R[X], ((c i : Algebra.adjoin R ({a} : Set A)) : A) = Polynomial.aeval a q := by
    intro i
    have : ((c i : Algebra.adjoin R ({a} : Set A)) : A) ∈ (Polynomial.aeval a : R[X] →ₐ[R] A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (c i).2
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq.symm⟩
  choose q hq using hc'
  refine ⟨q, ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hq i]
  rfl

variable {S f g}

theorem exists_serreData (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hfin1 : Module.Finite (Algebra.adjoin R ({g} : Set 𝒰.A1)) S.M1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1) :
    Nonempty (SerreData S f g) := by
  classical
  set u : 𝒰.A01 := 𝒰.ρ0 f with hudef
  set w : 𝒰.A01 := 𝒰.ρ1 g with hwdef
  have huw : u * w = 1 := hfg
  have hwu : w * u = 1 := by rw [mul_comm]; exact hfg
  have hu : IsUnit u := ⟨⟨u, w, huw, hwu⟩, rfl⟩

  obtain ⟨p, e, he⟩ := exists_generators_aeval f S.M0 hfin0
  obtain ⟨q, t, ht⟩ := exists_generators_aeval g S.M1 hfin1

  choose n hn using fun j => hloc0 (S.r1 (t j))
  choose n' hn' using fun i => hloc1 (S.r0 (e i))
  choose x hx using fun j => LinearMap.mem_range.mp (hn j)
  choose x' hx' using fun i => LinearMap.mem_range.mp (hn' i)
  let a : ℕ := 1 + (∑ j, n j) + (∑ i, n' i)
  have ha : 1 ≤ a := by omega
  have hna : ∀ j, n j ≤ a := fun j => by
    have := Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hn'a : ∀ i, n' i ≤ a := fun i => by
    have := Finset.single_le_sum (f := n') (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

  let y : Fin q → S.M0 := fun j => f ^ (a - n j) • x j
  let z : Fin p → S.M1 := fun i => g ^ (a - n' i) • x' i
  have hy : ∀ j, S.r0 (y j) = u ^ a • S.r1 (t j) := by
    intro j
    show S.r0 (f ^ (a - n j) • x j) = _
    rw [S.r0_smul, map_pow, hx j, ← hudef, smul_smul, ← pow_add, Nat.sub_add_cancel (hna j)]
  have hz : ∀ i, S.r1 (z i) = w ^ a • S.r0 (e i) := by
    intro i
    show S.r1 (g ^ (a - n' i) • x' i) = _
    rw [S.r1_smul, map_pow, hx' i, ← hwdef, smul_smul, ← pow_add, Nat.sub_add_cancel (hn'a i)]

  let m := p + q
  let t0 : Fin m → S.M0 := Fin.append e y
  let t1 : Fin m → S.M1 := Fin.append z t
  let c : Fin m → S.M01 := Fin.append (fun i => S.r0 (e i)) (fun j => u ^ a • S.r1 (t j))
  have hwaua : w ^ a * u ^ a = 1 := by rw [← mul_pow, hwu, one_pow]
  have ht0 : ∀ k, S.r0 (t0 k) = c k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [t0, c, Fin.append_left]
    · simp only [t0, c, Fin.append_right, hy]
  have ht1 : ∀ k, S.r1 (t1 k) = w ^ a • c k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [t1, c, Fin.append_left, hz]
    · simp only [t1, c, Fin.append_right, smul_smul, hwaua, one_smul]

  have hevT : ∀ k : ℕ, evalUnit u hu (T (-(k : ℤ)) : R[T;T⁻¹]) = w ^ k := by
    intro k
    apply eq_of_mul_eq_one_of_mul_eq_one (z := u ^ k)
    · rw [← evalUnit_T_natCast (R := R) u hu k, ← map_mul, ← T_add]
      have h0 : (-(k : ℤ) + k) = 0 := by omega
      rw [h0, LaurentPolynomial.T_zero, map_one]
    · rw [← mul_pow, hwu, one_pow]

  let π0 : (Fin m → R[X]) →ₗ[R] S.M0 :=
    { toFun := fun v => ∑ k, Polynomial.aeval f (v k) • t0 k
      map_add' := fun v v' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.add_apply, map_add, add_smul]
      map_smul' := fun r v => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.smul_apply, map_smul, smul_assoc] }
  let π1 : (Fin m → R[X]) →ₗ[R] S.M1 :=
    { toFun := fun v => ∑ k, Polynomial.aeval g (v k) • t1 k
      map_add' := fun v v' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.add_apply, map_add, add_smul]
      map_smul' := fun r v => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.smul_apply, map_smul, smul_assoc] }
  let π01 : (Fin m → R[T;T⁻¹]) →ₗ[R] S.M01 :=
    { toFun := fun v => ∑ k, evalUnit u hu (v k) • c k
      map_add' := fun v v' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.add_apply, map_add, add_smul]
      map_smul' := fun r v => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.smul_apply, evalUnit_smul, smul_assoc] }
  have π0_apply : ∀ v, π0 v = ∑ k, Polynomial.aeval f (v k) • t0 k := fun _ => rfl
  have π1_apply : ∀ v, π1 v = ∑ k, Polynomial.aeval g (v k) • t1 k := fun _ => rfl
  have π01_apply : ∀ v, π01 v = ∑ k, evalUnit u hu (v k) • c k := fun _ => rfl
  have hπ0_smul : ∀ (P : R[X]) (v : Fin m → R[X]), π0 (P • v) = Polynomial.aeval f P • π0 v := by
    intro P v
    rw [π0_apply, π0_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  have hπ1_smul : ∀ (P : R[X]) (v : Fin m → R[X]), π1 (P • v) = Polynomial.aeval g P • π1 v := by
    intro P v
    rw [π1_apply, π1_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  have hπ01_smul : ∀ (ℓ : R[T;T⁻¹]) (v : Fin m → R[T;T⁻¹]),
      π01 (ℓ • v) = evalUnit u hu ℓ • π01 v := by
    intro ℓ v
    rw [π01_apply, π01_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  have hcomm0 : S.r0 ∘ₗ π0 = π01 ∘ₗ (twistSections R m a).r0 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, π0_apply, π01_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [S.r0_smul, ht0 k, ← Polynomial.aeval_algHom_apply, ← hudef]
    congr 1
    exact (evalUnit_toLaurent u hu (v k)).symm
  have hcomm1 : S.r1 ∘ₗ π1 = π01 ∘ₗ (twistSections R m a).r1 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, π1_apply, π01_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [S.r1_smul, ht1 k, ← Polynomial.aeval_algHom_apply, ← hwdef, smul_smul]
    rw [twistSections_r1_apply]
    congr 1
    rw [map_mul, hevT a, evalUnit_invert_toLaurent u hu huw, mul_comm]
  have hsurj0 : Function.Surjective π0 := by
    intro xm
    obtain ⟨cf, hcf⟩ := he xm
    refine ⟨Fin.append cf 0, ?_⟩
    rw [π0_apply, hcf, Fin.sum_univ_add]
    simp only [t0, Fin.append_left, Fin.append_right, Pi.zero_apply, map_zero, zero_smul,
      Finset.sum_const_zero, add_zero]
  have hsurj1 : Function.Surjective π1 := by
    intro xm
    obtain ⟨cg, hcg⟩ := ht xm
    refine ⟨Fin.append 0 cg, ?_⟩
    rw [π1_apply, hcg, Fin.sum_univ_add]
    simp only [t1, Fin.append_left, Fin.append_right, Pi.zero_apply, map_zero, zero_smul,
      Finset.sum_const_zero, zero_add]
  have hsurj01 : Function.Surjective π01 := by
    intro mv
    obtain ⟨N, hN⟩ := hloc0 mv
    obtain ⟨x0, hx0⟩ := LinearMap.mem_range.mp hN
    obtain ⟨v, rfl⟩ := hsurj0 x0
    have hc0v : S.r0 (π0 v) = π01 ((twistSections R m a).r0 v) := by
      have := congrArg (fun F => F v) hcomm0
      simpa only [LinearMap.comp_apply] using this
    refine ⟨(T (-(N : ℤ)) : R[T;T⁻¹]) • (twistSections R m a).r0 v, ?_⟩
    have hwNuN : w ^ N * u ^ N = 1 := by rw [← mul_pow, hwu, one_pow]
    rw [hπ01_smul, hevT N, ← hc0v, hx0, smul_smul, hwNuN, one_smul]
  exact ⟨⟨m, a, ha, hu, π0, π1, π01, hπ0_smul, hπ1_smul, hπ01_smul, hcomm0, hcomm1,
    hsurj0, hsurj1, hsurj01⟩⟩

end construction

end TwoChartCech.SerreH0

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Sections.finite_H1_of_chartFinite kerMap_injective_of_H0_eq_zero"
namespace SerreH0
p2m_open "TwoChartCech"
open Polynomial LaurentPolynomial

variable {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, u} R}

namespace SerreData
variable {S : TwoChartCech.Sections.{u, u, u} 𝒰} {f : 𝒰.A0} {g : 𝒰.A1} (D : SerreData S f g)

theorem kerSections_hfin0 [IsNoetherianRing R] :
    Module.Finite (Algebra.adjoin R ({X} : Set (P1Cover R).A0)) D.kerSections.M0 := by
  have hKfg : D.K0.FG := IsNoetherian.noetherian D.K0
  haveI : Module.Finite R[X] ↥D.K0 := Module.Finite.iff_fg.mpr hKfg
  haveI : Module.Finite (Algebra.adjoin R ({X} : Set R[X])) R[X] := by
    refine ⟨⟨{1}, ?_⟩⟩
    rw [Finset.coe_singleton, eq_top_iff]
    rintro p -
    have hp : p ∈ Algebra.adjoin R ({X} : Set R[X]) := by
      rw [Polynomial.adjoin_X]; exact Algebra.mem_top
    have : p = (⟨p, hp⟩ : Algebra.adjoin R ({X} : Set R[X])) • (1 : R[X]) := by
      rw [Subalgebra.smul_def, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self 1)
  exact Module.Finite.trans R[X] ↥D.K0

theorem exists_T_pow_smul_eq (m : ℕ) (kv : Fin m → R[T;T⁻¹]) :
    ∃ (N : ℕ) (ev : Fin m → R[X]), ∀ i, T (N : ℤ) * kv i = Polynomial.toLaurent (ev i) := by
  choose Nf ef hef using fun i => (kv i).exists_T_pow
  refine ⟨∑ i, Nf i, fun i => ef i * X ^ ((∑ i, Nf i) - Nf i), fun i => ?_⟩
  have hle : Nf i ≤ ∑ i, Nf i :=
    Finset.single_le_sum (f := Nf) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [map_mul, hef, map_pow, Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_assoc, ← T_add,
    mul_comm]
  congr 2
  push_cast [Nat.cast_sub hle]
  ring

theorem kerSections_hloc0 (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0) :
    ∀ k : D.kerSections.M01, ∃ n : ℕ, ((P1Cover R).ρ0 X) ^ n • k ∈ LinearMap.range D.kerSections.r0 := by
  rintro ⟨kv, hk⟩
  obtain ⟨N, ev, hev⟩ := exists_T_pow_smul_eq D.m kv
  have hr0ev : (twistSections R D.m D.a).r0 ev = (T (N : ℤ) : R[T;T⁻¹]) • kv := by
    funext i
    show Polynomial.toLaurent (ev i) = T (N : ℤ) * kv i
    exact (hev i).symm

  have hc0 : S.r0 (D.π0 ev) = 0 := by
    have := congrArg (fun F => F ev) D.comm0
    simp only [LinearMap.comp_apply] at this
    rw [this, hr0ev, D.π01_smul, (D.mem_K01_iff kv).mp hk, smul_zero]
  obtain ⟨M, hM⟩ := htors0 _ hc0
  have hmem : (X : R[X]) ^ M • ev ∈ D.K0 := by
    rw [mem_K0_iff, D.π0_smul, map_pow, Polynomial.aeval_X, hM]
  refine ⟨M + N, ⟨⟨(X : R[X]) ^ M • ev, hmem⟩, Subtype.ext ?_⟩⟩
  show (twistSections R D.m D.a).r0 ((X : R[X]) ^ M • ev) = ((P1Cover R).ρ0 X) ^ (M + N) • kv
  rw [(twistSections R D.m D.a).r0_smul, hr0ev, map_pow, smul_smul]
  congr 1
  show Polynomial.toLaurent (X : R[X]) ^ M * T (N : ℤ) = Polynomial.toLaurent (X : R[X]) ^ (M + N)
  rw [Polynomial.toLaurent_X, LaurentPolynomial.T_pow, LaurentPolynomial.T_pow, ← T_add]
  congr 1
  push_cast
  ring

theorem kerSections_hloc1 (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    ∀ k : D.kerSections.M01, ∃ n : ℕ, ((P1Cover R).ρ1 X) ^ n • k ∈ LinearMap.range D.kerSections.r1 := by
  rintro ⟨kv, hk⟩
  obtain ⟨N, ev, hev⟩ := exists_T_pow_smul_eq D.m (fun i => LaurentPolynomial.invert (kv i))

  have hev' : ∀ i, LaurentPolynomial.invert (Polynomial.toLaurent (ev i)) = T (-(N : ℤ)) * kv i := by
    intro i
    rw [← hev i, map_mul, LaurentPolynomial.invert_T]
    congr 1
    exact LaurentPolynomial.invert.apply_symm_apply (kv i)
  have hr1ev : (twistSections R D.m D.a).r1 ev = (T (-((N : ℤ) + D.a)) : R[T;T⁻¹]) • kv := by
    funext i
    show T (-(D.a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (ev i)) = T (-((N : ℤ) + D.a)) * kv i
    rw [hev', ← mul_assoc, ← T_add]
    congr 2
    ring
  have hc1 : S.r1 (D.π1 ev) = 0 := by
    have := congrArg (fun F => F ev) D.comm1
    simp only [LinearMap.comp_apply] at this
    rw [this, hr1ev, D.π01_smul, (D.mem_K01_iff kv).mp hk, smul_zero]
  obtain ⟨M, hM⟩ := htors1 _ hc1
  have hmem : (X : R[X]) ^ M • ev ∈ D.K1 := by
    rw [mem_K1_iff, D.π1_smul, map_pow, Polynomial.aeval_X, hM]
  refine ⟨M + N + D.a, ⟨⟨(X : R[X]) ^ M • ev, hmem⟩, Subtype.ext ?_⟩⟩
  show (twistSections R D.m D.a).r1 ((X : R[X]) ^ M • ev) = ((P1Cover R).ρ1 X) ^ (M + N + D.a) • kv
  rw [(twistSections R D.m D.a).r1_smul, hr1ev, map_pow, smul_smul]
  congr 1
  show (LaurentPolynomial.invert (Polynomial.toLaurent (X : R[X]))) ^ M * T (-((N : ℤ) + D.a))
    = (LaurentPolynomial.invert (Polynomial.toLaurent (X : R[X]))) ^ (M + N + D.a)
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T, LaurentPolynomial.T_pow, LaurentPolynomial.T_pow,
    ← T_add]
  congr 1
  push_cast
  ring

end SerreData

end TwoChartCech.SerreH0

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Sections.finite_H1_of_chartFinite kerMap_injective_of_H0_eq_zero"
namespace SerreH0
p2m_open "TwoChartCech"
open Polynomial LaurentPolynomial

variable {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, u} R}

theorem P1Cover_hfg : (P1Cover R).ρ0 X * (P1Cover R).ρ1 X = 1 := by
  show Polynomial.toLaurent (X : R[X]) * LaurentPolynomial.invert (Polynomial.toLaurent (X : R[X])) = 1
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T, ← T_add]
  simp

namespace SerreData
variable {S : TwoChartCech.Sections.{u, u, u} 𝒰} {f : 𝒰.A0} {g : 𝒰.A1} (D : SerreData S f g)

theorem finite_H0 [IsNoetherianRing R] (D : SerreData S f g) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0)
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    Module.Finite R S.H0 := by

  haveI hK1 : Module.Finite R D.kerSections.H1 :=
    TwoChartCech.Sections.finite_H1_of_chartFinite D.kerSections X X P1Cover_hfg
      D.kerSections_hfin0 (D.kerSections_hloc0 htors0) (D.kerSections_hloc1 hfg htors1)

  let E := twistSections R D.m D.a
  let i0 : D.kerSections.M0 × D.kerSections.M1 →ₗ[R] E.M0 × E.M1 :=
    LinearMap.prodMap (D.K0.subtype.restrictScalars R) (D.K1.subtype.restrictScalars R)
  let i1 : D.kerSections.M01 →ₗ[R] E.M01 := D.K01.subtype.restrictScalars R
  let p0 : E.M0 × E.M1 →ₗ[R] S.M0 × S.M1 := LinearMap.prodMap D.π0 D.π1
  let p1 : E.M01 →ₗ[R] S.M01 := D.π01
  have hi : E.cechDiff ∘ₗ i0 = i1 ∘ₗ D.kerSections.cechDiff := by
    apply LinearMap.ext; intro x; rfl
  have hp : S.cechDiff ∘ₗ p0 = p1 ∘ₗ E.cechDiff := by
    apply LinearMap.ext
    rintro ⟨v, w⟩
    simp only [LinearMap.comp_apply, TwoChartCech.Sections.cechDiff_apply, map_sub]
    have h0 := congrArg (fun F => F v) D.comm0
    have h1 := congrArg (fun F => F w) D.comm1
    simp only [LinearMap.comp_apply] at h0 h1
    show S.r1 (D.π1 w) - S.r0 (D.π0 v) = D.π01 (E.r1 w) - D.π01 (E.r0 v)
    rw [h0, h1]
    try rfl
  have hi0 : Function.Injective i0 := fun x y hxy => by
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hxy)
    · exact Subtype.ext (congrArg Prod.snd hxy)
  have hi1 : Function.Injective i1 := fun x y hxy => Subtype.ext hxy
  have hp0 : Function.Surjective p0 := fun ⟨x, y⟩ => by
    obtain ⟨v, rfl⟩ := D.surj0 x
    obtain ⟨w, rfl⟩ := D.surj1 y
    exact ⟨(v, w), rfl⟩
  have hp1 : Function.Surjective p1 := D.surj01
  have hex0 : LinearMap.range i0 = LinearMap.ker p0 := by
    apply le_antisymm
    · rintro _ ⟨⟨v, w⟩, rfl⟩
      rw [LinearMap.mem_ker]
      exact Prod.ext v.2 w.2
    · rintro ⟨v, w⟩ hvw
      rw [LinearMap.mem_ker] at hvw
      exact ⟨(⟨v, congrArg Prod.fst hvw⟩, ⟨w, congrArg Prod.snd hvw⟩), rfl⟩
  have hex1 : LinearMap.range i1 = LinearMap.ker p1 := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact w.2
    · intro w hw
      exact ⟨⟨w, hw⟩, rfl⟩
  have hE : LinearMap.ker E.cechDiff = ⊥ := ker_cechDiff_twistSections_eq_bot D.m D.a D.one_le_a
  exact TwoChartCech.kerMap_injective_of_H0_eq_zero D.kerSections.cechDiff E.cechDiff S.cechDiff
    i0 i1 p0 p1 hi hp hi0 hi1 hp0 hp1 hex0 hex1 hE

end SerreData

end TwoChartCech.SerreH0

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {𝒰 : TwoChartCech.Cover.{u, u} R}
    (S : TwoChartCech.Sections.{u, u, u} 𝒰)
    (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hfin1 : Module.Finite (Algebra.adjoin R ({g} : Set 𝒰.A1)) S.M1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1)
    (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0)
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    Module.Finite R S.H0 := by
  obtain ⟨D⟩ := TwoChartCech.SerreH0.exists_serreData hfg hfin0 hfin1 hloc0 hloc1
  exact D.finite_H0 hfg htors0 htors1

end S_TwoChartCech_Sections_finite_H0_of_chartFinite
end P2MW
export P2MW.S_TwoChartCech_Sections_finite_H0_of_chartFinite (solution)
