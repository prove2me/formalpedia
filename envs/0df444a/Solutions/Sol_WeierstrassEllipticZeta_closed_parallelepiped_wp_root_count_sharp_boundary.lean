-- Prove2me | solution 1 for WeierstrassEllipticZeta.closed_parallelepiped_wp_root_count_sharp_boundary
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T01:26:32.348731+00:00
-- url     : https://prove2.me/submissions/f5db7446-b2b5-46ca-803a-5c55c2c5630a

import Theorems.Thm_WeierstrassEllipticZeta_closed_parallelepiped_wp_root_count
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Tactic

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

private lemma class_flags_injective (L : PeriodPair) (x y : ℂ)
    (hx : x ∈ L.basis.parallelepiped) (hy : y ∈ L.basis.parallelepiped)
    (hq : L.lattice.mkQ x = L.lattice.mkQ y)
    (hbits : (fun i => decide (L.basis.repr x i = 1)) =
      (fun i => decide (L.basis.repr y i = 1))) : x = y := by
  have hsub : (x : ℂ) - y ∈ L.lattice := (Submodule.Quotient.eq L.lattice).mp hq
  have hfract : ZSpan.fract L.basis (y : ℂ) = ZSpan.fract L.basis (x : ℂ) := by
    apply (ZSpan.fract_eq_fract L.basis _ _).mpr
    rw [← L.lattice_eq_span_range_basis]
    simpa only [sub_eq_add_neg, add_comm] using hsub
  apply L.basis.ext_elem
  intro i
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

private lemma same_class_fract (L : PeriodPair) (x y : ℂ)
    (hq : L.lattice.mkQ x = L.lattice.mkQ y) :
    ZSpan.fract L.basis x = ZSpan.fract L.basis y := by
  apply (ZSpan.fract_eq_fract L.basis _ _).mpr
  rw [← L.lattice_eq_span_range_basis]
  have hm := (Submodule.Quotient.eq L.lattice).mp hq.symm
  simpa only [sub_eq_add_neg, add_comm] using hm

private lemma class_fibre_bound (L : PeriodPair) (F : Finset ℂ)
    (hF : ∀ z ∈ F, z ∈ L.basis.parallelepiped) (q : ℂ ⧸ L.lattice)
    (hclass : ∀ z ∈ F, L.lattice.mkQ z = q) :
    F.card ≤ if q = 0 then 4 else 2 := by
  by_cases hq : q = 0
  · simp only [hq, ↓reduceIte]
    let f : F → (Fin 2 → Bool) := fun z i => decide (L.basis.repr (z : ℂ) i = 1)
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact class_flags_injective L x y (hF x x.property) (hF y y.property)
        ((hclass x x.property).trans (hclass y y.property).symm) hxy
    simpa using Fintype.card_le_of_injective f hf
  · simp only [hq, ↓reduceIte]
    by_cases hne : F.Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hfract : ZSpan.fract L.basis x ≠ 0 := by
        intro he
        have hm : -x + 0 ∈ Submodule.span ℤ (Set.range L.basis) :=
          (ZSpan.fract_eq_fract L.basis x 0).mp
            (he.trans (by simp [ZSpan.fract, ZSpan.floor]))
        rw [← L.lattice_eq_span_range_basis] at hm
        have hxL : x ∈ L.lattice := by simpa using L.lattice.neg_mem hm
        have hx0 : L.lattice.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hxL
        exact hq ((hclass x hx).symm.trans hx0)
      have hex : ∃ i : Fin 2, L.basis.repr (ZSpan.fract L.basis x) i ≠ 0 := by
        by_contra! hh
        apply hfract
        apply L.basis.ext_elem
        intro i
        simpa using hh i
      obtain ⟨i, hi⟩ := hex
      have hflag (z : ℂ) (hz : z ∈ F) : decide (L.basis.repr z i = 1) = false := by
        apply decide_eq_false_iff_not.mpr
        intro hzi
        have he := congrArg (fun t => L.basis.repr t i)
          (same_class_fract L z x ((hclass z hz).trans (hclass x hx).symm))
        rw [ZSpan.repr_fract_apply, hzi] at he
        exact hi (by simpa using he.symm)
      let f : F → {t : Fin 2 → Bool // t i = false} := fun z =>
        ⟨fun j => decide (L.basis.repr (z : ℂ) j = 1), hflag z z.property⟩
      have hf : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        exact class_flags_injective L x y (hF x x.property) (hF y y.property)
          ((hclass x x.property).trans (hclass y y.property).symm)
          (congrArg Subtype.val hxy)
      have hcard : Fintype.card {t : Fin 2 → Bool // t i = false} = 2 := by
        fin_cases i <;> decide
      simpa only [Fintype.card_coe, hcard] using Fintype.card_le_of_injective f hf
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

private lemma closed_class_count (L : PeriodPair) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z ∈ L.basis.parallelepiped) :
    Z.card ≤ 2 * (L.lattice.mkQ '' (Z : Set ℂ)).ncard + 2 := by
  let V := Z.image L.lattice.mkQ
  have hf (q : ℂ ⧸ L.lattice) :
      (Z.filter (fun z => L.lattice.mkQ z = q)).card ≤ if q = 0 then 4 else 2 :=
    class_fibre_bound L _ (fun z hz => hZ z (Finset.mem_filter.mp hz).1) q
      (fun z hz => (Finset.mem_filter.mp hz).2)
  have hsum : Z.card ≤ ∑ q ∈ V, (if q = 0 then 4 else 2 : ℕ) := by
    rw [Finset.card_eq_sum_card_image L.lattice.mkQ Z]
    exact Finset.sum_le_sum (fun q _ => hf q)
  have heq : (∑ q ∈ V, (if q = 0 then 4 else 2 : ℕ)) =
      2 * V.card + if (0 : ℂ ⧸ L.lattice) ∈ V then 2 else 0 := by
    calc
      _ = ∑ q ∈ V, (2 + if q = 0 then 2 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro q hq
        split_ifs <;> rfl
      _ = _ := by simp [Finset.sum_add_distrib, mul_comm]
  rw [heq] at hsum
  rw [← Finset.coe_image, Set.ncard_coe_finset]
  change Z.card ≤ 2 * V.card + 2
  split_ifs at hsum <;> omega


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z ∈ L.basis.parallelepiped)
    (H : Polynomial ℂ) (hH : H ≠ 0)
    (hroot : ∀ z ∈ Z, z ∉ L.lattice → L.weierstrassP z ∈ H.roots.toFinset) :
    Z.card ≤ 4 * H.natDegree + 4 := by
  have hp := (closed_parallelepiped_wp_root_count L Z hZ H hH hroot).1
  have hc := closed_class_count L Z hZ
  omega
