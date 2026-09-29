-- Prove2me | solution 1 for ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7c8bb410-6dc5-5800-a28d-8df2c4afcf15

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries

set_option autoImplicit false

namespace RedHomAux

variable {A : Type} [CommRing A] {R : Type} [CommRing R]

theorem emb_mul (φ : A →+* R) (x y : PowerSeries A) :
    HahnSeries.ofPowerSeries ℤ R ((x * y).map φ) =
      HahnSeries.ofPowerSeries ℤ R (x.map φ) * HahnSeries.ofPowerSeries ℤ R (y.map φ) := by
  rw [map_mul, map_mul]

theorem emb_add (φ : A →+* R) (x y : PowerSeries A) :
    HahnSeries.ofPowerSeries ℤ R ((x + y).map φ) =
      HahnSeries.ofPowerSeries ℤ R (x.map φ) + HahnSeries.ofPowerSeries ℤ R (y.map φ) := by
  rw [map_add, map_add]

theorem emb_injective {φ : A →+* R} (hφ : Function.Injective φ) {x y : PowerSeries A}
    (h : HahnSeries.ofPowerSeries ℤ R (x.map φ) = HahnSeries.ofPowerSeries ℤ R (y.map φ)) : x = y :=
  PowerSeries.map_injective φ hφ (HahnSeries.ofPowerSeries_injective h)

theorem emb_ne_zero [IsDomain R] (φ : A →+* R) {x : PowerSeries A} (hx : x.map φ ≠ 0) :
    HahnSeries.ofPowerSeries ℤ R (x.map φ) ≠ 0 :=
  fun h => hx (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))

end RedHomAux

open RedHomAux in
theorem solution
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) :
    ∃ red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A),
      (∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        red f = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      RingHom.ker red = IsLocalRing.maximalIdeal ↥W₀ := by
  classical
  have hinjL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  have hwd : ∀ (f : ↥K) (x y x' y' : PowerSeries A),
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y'.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) →
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) *
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y'.map (IsLocalRing.residue A)) =
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x'.map (IsLocalRing.residue A)) *
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) := by
    intro f x y x' y' h h'
    have h1 : HahnSeries.ofPowerSeries ℤ L ((x * y').map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((x' * y).map (algebraMap A L)) := by
      rw [emb_mul, emb_mul, ← h, ← h']
      ring
    have h2 : x * y' = x' * y := emb_injective hinjL h1
    rw [← emb_mul, ← emb_mul, h2]

  have hpres : ∀ f : ↥W₀, ∃ xy : PowerSeries A × PowerSeries A,
      xy.2.map (IsLocalRing.residue A) ≠ 0 ∧
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (xy.2.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (xy.1.map (algebraMap A L)) := by
    intro f
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ (f : ↥K)).mp f.2
    exact ⟨(x, y), hy, hxy⟩
  choose pr hpr_ne hpr_eq using hpres

  let rd : PowerSeries A → LaurentSeries (IsLocalRing.ResidueField A) := fun x =>
    HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A))
  have hrd_ne : ∀ y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 → rd y ≠ 0 :=
    fun y hy => emb_ne_zero _ hy
  have hrd_mul : ∀ x y : PowerSeries A, rd (x * y) = rd x * rd y := fun x y => emb_mul _ x y
  have hrd_add : ∀ x y : PowerSeries A, rd (x + y) = rd x + rd y := fun x y => emb_add _ x y
  let red₀ : ↥W₀ → LaurentSeries (IsLocalRing.ResidueField A) := fun f => rd (pr f).1 / rd (pr f).2

  have hred₀ : ∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) → red₀ f = rd x / rd y := by
    intro f x y hy hxy
    show rd (pr f).1 / rd (pr f).2 = rd x / rd y
    rw [div_eq_div_iff (hrd_ne _ (hpr_ne f)) (hrd_ne _ hy)]
    exact hwd (f : ↥K) _ _ _ _ (hpr_eq f) hxy

  have hone : (((1 : ↥W₀) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L)) := by
    rw [map_one, map_one, mul_one]; rfl
  have hzero : (((0 : ↥W₀) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L ((0 : PowerSeries A).map (algebraMap A L)) := by
    rw [map_zero, map_zero]
    push_cast
    ring
  have h1ne : (1 : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by rw [map_one]; exact one_ne_zero
  have hmul : ∀ f g : ↥W₀,
      (((f * g : ↥W₀) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (((pr f).2 * (pr g).2).map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (((pr f).1 * (pr g).1).map (algebraMap A L)) := by
    intro f g
    have hf := hpr_eq f
    have hg := hpr_eq g
    rw [emb_mul, emb_mul, ← hf, ← hg]
    push_cast
    ring
  have hadd : ∀ f g : ↥W₀,
      (((f + g : ↥W₀) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (((pr f).2 * (pr g).2).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (((pr f).1 * (pr g).2 + (pr g).1 * (pr f).2).map (algebraMap A L)) := by
    intro f g
    have hf := hpr_eq f
    have hg := hpr_eq g
    rw [emb_add, emb_mul, emb_mul, emb_mul, ← hf, ← hg]
    push_cast
    ring
  have hne2 : ∀ f g : ↥W₀, ((pr f).2 * (pr g).2).map (IsLocalRing.residue A) ≠ 0 := by
    intro f g
    rw [map_mul]
    exact mul_ne_zero (hpr_ne f) (hpr_ne g)

  let red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A) :=
    { toFun := red₀
      map_one' := by
        rw [hred₀ 1 1 1 h1ne hone, div_self (hrd_ne _ h1ne)]
      map_mul' := by
        intro f g
        rw [hred₀ (f * g) _ _ (hne2 f g) (hmul f g), hrd_mul, hrd_mul, div_mul_div_comm]
      map_zero' := by
        rw [hred₀ 0 0 1 h1ne hzero]
        show rd 0 / rd 1 = 0
        rw [show rd 0 = 0 from by simp [rd], zero_div]
      map_add' := by
        intro f g
        rw [hred₀ (f + g) _ _ (hne2 f g) (hadd f g), hrd_add, hrd_mul, hrd_mul, hrd_mul,
          div_add_div _ _ (hrd_ne _ (hpr_ne f)) (hrd_ne _ (hpr_ne g))]
        ring }
  refine ⟨red, ?_, ?_⟩
  · intro f x y hy hxy
    exact hred₀ f x y hy hxy
  · ext f
    rw [RingHom.mem_ker, ← ValuationSubring.coe_mem_nonunits_iff,
      hnu (f : ↥K) (pr f).1 (pr f).2 (hpr_ne f) (hpr_eq f)]
    show rd (pr f).1 / rd (pr f).2 = 0 ↔ _
    rw [div_eq_zero_iff, or_iff_left (hrd_ne _ (hpr_ne f))]
    constructor
    · intro h
      by_contra hx
      exact hrd_ne _ hx h
    · intro h
      show HahnSeries.ofPowerSeries ℤ _ _ = 0
      rw [h, map_zero]

end S_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
end P2MW
export P2MW.S_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries (solution)
