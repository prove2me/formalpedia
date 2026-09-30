-- Prove2me | solution 1 for WeierstrassEllipticZeta.closed_parallelepiped_wp_root_count
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T01:09:21.636586+00:00
-- url     : https://prove2.me/submissions/9a9139e6-171a-4ec0-8c30-05c98140a9e8

import Theorems.Thm_WeierstrassEllipticZeta_period_image_multiplicity_le_of_wp_polynomial
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_addition_data
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Tactic

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

private lemma closed_parallelepiped_class_count (L : PeriodPair) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z ∈ L.basis.parallelepiped) :
    Z.card ≤ 4 * (L.lattice.mkQ '' (Z : Set ℂ)).ncard := by
  let f : Z → (Z.image L.lattice.mkQ) × (Fin 2 → Bool) := fun z =>
    (⟨L.lattice.mkQ z, Finset.mem_image.mpr ⟨z, z.property, rfl⟩⟩,
      fun i => decide (L.basis.repr (z : ℂ) i = 1))
  have hf : Function.Injective f := by
    intro x y hxy
    have hq : L.lattice.mkQ (x : ℂ) = L.lattice.mkQ (y : ℂ) :=
      congrArg (fun p => p.1.val) hxy
    have hbits : (fun i => decide (L.basis.repr (x : ℂ) i = 1)) =
        (fun i => decide (L.basis.repr (y : ℂ) i = 1)) := congrArg Prod.snd hxy
    have hsub : (x : ℂ) - y ∈ L.lattice := (Submodule.Quotient.eq L.lattice).mp hq
    have hfract : ZSpan.fract L.basis (y : ℂ) = ZSpan.fract L.basis (x : ℂ) := by
      apply (ZSpan.fract_eq_fract L.basis _ _).mpr
      rw [← L.lattice_eq_span_range_basis]
      simpa only [sub_eq_add_neg, add_comm] using hsub
    apply Subtype.ext
    apply L.basis.ext_elem
    intro i
    have hx := hZ x x.property
    have hy := hZ y y.property
    change (x : ℂ) ∈ _root_.parallelepiped L.basis at hx
    change (y : ℂ) ∈ _root_.parallelepiped L.basis at hy
    rw [parallelepiped_basis_eq] at hx hy
    have hxi : 0 ≤ L.basis.repr (x : ℂ) i ∧ L.basis.repr (x : ℂ) i ≤ 1 := hx i
    have hyi : 0 ≤ L.basis.repr (y : ℂ) i ∧ L.basis.repr (y : ℂ) i ≤ 1 := hy i
    have hi := congrFun hbits i
    have hfloor : ⌊L.basis.repr (x : ℂ) i⌋ = ⌊L.basis.repr (y : ℂ) i⌋ := by
      by_cases hx1 : L.basis.repr (x : ℂ) i = 1
      · have hy1 : L.basis.repr (y : ℂ) i = 1 := by simpa [hx1] using hi.symm
        rw [hx1, hy1]
      · have hy1 : L.basis.repr (y : ℂ) i ≠ 1 := by simpa [hx1] using hi.symm
        have hx0 : ⌊L.basis.repr (x : ℂ) i⌋ = 0 := by
          apply Int.floor_eq_iff.mpr
          simpa using And.intro hxi.1 (lt_of_le_of_ne hxi.2 hx1)
        have hy0 : ⌊L.basis.repr (y : ℂ) i⌋ = 0 := by
          apply Int.floor_eq_iff.mpr
          simpa using And.intro hyi.1 (lt_of_le_of_ne hyi.2 hy1)
        rw [hx0, hy0]
    have hi' := congrArg (fun z => L.basis.repr z i) hfract
    simp only [ZSpan.repr_fract_apply, Int.fract] at hi'
    rw [hfloor] at hi'
    linarith
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Finset.coe_image, Set.ncard_coe_finset]
  simpa [Fintype.card_prod, Fintype.card_fun, mul_comm] using hcard


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z ∈ L.basis.parallelepiped)
    (H : Polynomial ℂ) (hH : H ≠ 0)
    (hroot : ∀ z ∈ Z, z ∉ L.lattice → L.weierstrassP z ∈ H.roots.toFinset) :
    (L.lattice.mkQ '' (Z : Set ℂ)).ncard ≤ 2 * H.natDegree + 1 ∧
      Z.card ≤ 8 * H.natDegree + 4 := by
  obtain ⟨D⟩ := exists_elliptic_sigma_addition_data L
    (hasDerivAt_weierstrassZeta L) (zeta_addition_formula L)
  have hp := period_image_multiplicity_le_of_wp_polynomial L D Z 1 H hH (by
    intro z hz hn
    rw [pow_one, Polynomial.dvd_iff_isRoot]
    exact (Polynomial.mem_roots hH).mp (Multiset.mem_toFinset.mp (hroot z hz hn)))
  simp only [one_mul] at hp
  refine ⟨hp, ?_⟩
  have hc := closed_parallelepiped_class_count L Z hZ
  omega
