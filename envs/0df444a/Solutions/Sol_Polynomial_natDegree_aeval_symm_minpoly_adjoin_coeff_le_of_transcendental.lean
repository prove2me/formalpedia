-- Prove2me | solution 1 for Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/171cbb1c-dbd6-58e5-b7b3-3c2b61cb9ed6

import Mathlib
import Theorems.Thm_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental
import Theorems.Thm_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem solution
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V)
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m := by
  classical

  set q : Polynomial (Algebra.adjoin L ({x} : Set F)) :=
    minpoly (Algebra.adjoin L ({x} : Set F)) f with hq
  set d : ℕ := q.natDegree with hd
  set n : ℕ := (d - j) * m with hn
  set y : F := x⁻¹ with hy
  have hy0 : y ≠ 0 := inv_ne_zero hx0
  have hyL : Transcendental L y := by
    intro ⟨p, hp0, hpy⟩
    refine hxL ⟨p.reflect p.natDegree, fun h => hp0 (Polynomial.reflect_eq_zero_iff.mp h), ?_⟩
    haveI : Invertible y := invertibleOfNonzero hy0
    rw [Polynomial.aeval_def, show x = ⅟y by rw [invOf_eq_inv, hy, inv_inv],
      Polynomial.eval₂_reflect_eq_zero_iff (algebraMap L F) y p.natDegree p (le_refl _),
      ← Polynomial.aeval_def]
    exact hpy
  set g : F := f * (x ^ m)⁻¹ with hg

  haveI hICx : IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) :=
    Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental x hxL
  haveI hICy : IsIntegrallyClosed (Algebra.adjoin L ({y} : Set F)) :=
    Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental y hyL

  have hfallV : ∀ V : ValuationSubring F,
      (Algebra.adjoin L ({x} : Set F) : Set F) ⊆ (V : Set F) → f ∈ V := by
    intro V hLxV
    have hiInf := iInf_valuationSubring_superset (K := F)
      (s := ((Algebra.adjoin L ({x} : Set F)).toSubring : Set F))
    rw [Subring.closure_eq] at hiInf
    have hfmem : f ∈ (integralClosure
        (Algebra.adjoin L ({x} : Set F)).toSubring F).toSubring := hint
    rw [← hiInf] at hfmem
    exact (Subring.mem_iInf.mp hfmem) ⟨V, hLxV⟩

  have hgint : IsIntegral (Algebra.adjoin L ({y} : Set F)) g := by
    set s : Set F := Set.range (algebraMap L F) ∪ {y} with hsdef
    have hmem : g ∈ (integralClosure (Subring.closure s) F).toSubring := by
      rw [← iInf_valuationSubring_superset]
      simp only [Subring.mem_iInf]
      rintro ⟨V, hsV⟩
      have hLV : ∀ a : L, algebraMap L F a ∈ V := fun a => hsV (Or.inl ⟨a, rfl⟩)
      have hyV : y ∈ V := hsV (Or.inr rfl)
      by_cases hxV : x ∈ V
      · have hLxV : (Algebra.adjoin L ({x} : Set F) : Set F) ⊆ (V : Set F) := by
          show ((Algebra.adjoin L ({x} : Set F)).toSubring : Set F) ⊆ (V : Set F)
          rw [← (Algebra.adjoin_eq_ring_closure ({x} : Set F)).symm]
          exact Subring.closure_le.mpr (Set.union_subset
            (Set.range_subset_iff.mpr hLV) (Set.singleton_subset_iff.mpr hxV))
        have hfV : f ∈ V := hfallV V hLxV
        have hxmV : (x ^ m)⁻¹ ∈ V := by
          rw [← inv_pow, ← hy]; exact pow_mem hyV m
        exact mul_mem hfV hxmV
      · exact h₂ V hLV hxV
    have hcls : Subring.closure s = (Algebra.adjoin L ({y} : Set F)).toSubring :=
      (Algebra.adjoin_eq_ring_closure _).symm
    refine (hmem : IsIntegral (Subring.closure s) g).map_of_comp_eq
      (Subring.inclusion hcls.le) (RingHom.id F) ?_
    ext a; exact (Subring.coe_inclusion hcls.le a).symm

  have hxK : x ∈ IntermediateField.adjoin L ({y} : Set F) := by
    rw [show x = y⁻¹ from (inv_inv x).symm ▸ congrArg Inv.inv hy.symm]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self L y)
  have hyKx : y ∈ IntermediateField.adjoin L ({x} : Set F) := by
    rw [hy]; exact inv_mem (IntermediateField.mem_adjoin_simple_self L x)
  have hKeq : IntermediateField.adjoin L ({x} : Set F) = IntermediateField.adjoin L ({y} : Set F) :=
    le_antisymm
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxK))
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hyKx))

  have hmpgLy : ∀ i, ((minpoly (IntermediateField.adjoin L ({y} : Set F)) g).coeff i : F) ∈
      Algebra.adjoin L ({y} : Set F) := by
    intro i
    have heq := minpoly.isIntegrallyClosed_eq_field_fractions'
      (R := Algebra.adjoin L ({y} : Set F)) (IntermediateField.adjoin L ({y} : Set F)) hgint
    rw [heq, Polynomial.coeff_map]
    exact ((minpoly (Algebra.adjoin L ({y} : Set F)) g).coeff i).2

  have hmpfq : minpoly (IntermediateField.adjoin L ({x} : Set F)) f =
      q.map (algebraMap (Algebra.adjoin L ({x} : Set F))
        (IntermediateField.adjoin L ({x} : Set F))) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hint
  have hmpfd : (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).natDegree = d := by
    rw [hmpfq, (minpoly.monic hint).natDegree_map, hd]

  have hxKmem : x ∈ IntermediateField.adjoin L ({x} : Set F) :=
    IntermediateField.mem_adjoin_simple_self L x
  set xK : IntermediateField.adjoin L ({x} : Set F) := ⟨x, hxKmem⟩ with hxK
  have hxK0 : xK ≠ 0 := fun h => hx0 (congrArg Subtype.val h)

  have hgsmul : g = (xK ^ m)⁻¹ • f := by
    rw [hg, Algebra.smul_def, map_inv₀, map_pow, mul_comm]
    rfl

  have hfintK : IsIntegral (IntermediateField.adjoin L ({x} : Set F)) f := hint.tower_top

  set_option synthInstance.maxHeartbeats 800000 in
  have hmpg_scale : minpoly (IntermediateField.adjoin L ({x} : Set F)) g =
      (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).scaleRoots ((xK ^ m)⁻¹) := by
    rw [hgsmul]
    exact IsIntegrallyClosed.minpoly_smul (inv_ne_zero (pow_ne_zero m hxK0)) hfintK

  have hcoefj : (minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j =
      (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j * ((xK ^ m)⁻¹) ^ (d - j) := by
    rw [hmpg_scale, Polynomial.coeff_scaleRoots, hmpfd]

  have hcoefF : ((minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j : F) =
      ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ := by
    have hcast1 : ((minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j : F) =
        ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) := by
      rw [hmpfq, Polynomial.coeff_map]; rfl
    have hcast2 : (((xK ^ m)⁻¹ ^ (d - j) :
        IntermediateField.adjoin L ({x} : Set F)) : F) = (x ^ n)⁻¹ := by
      push_cast
      rw [show ((xK : IntermediateField.adjoin L ({x} : Set F)) : F) = x from rfl,
        ← inv_pow, ← pow_mul, hn, mul_comm m (d - j), inv_pow]
    calc ((minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j : F)
        = ((minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j : F) *
            (((xK ^ m)⁻¹ ^ (d - j) : IntermediateField.adjoin L ({x} : Set F)) : F) := by
          rw [hcoefj]; push_cast; ring
      _ = ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ := by
          rw [hcast1, hcast2]

  have hkey : ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ ∈
      Algebra.adjoin L ({y} : Set F) := by
    rw [← hcoefF, hKeq]
    exact hmpgLy j

  rw [← hc] at hkey
  have hy2 : ({x⁻¹} : Set F) = {y} := by rw [hy]
  rw [← hy2] at hkey
  exact Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv x hxL hx0 c n hkey

end S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
end P2MW
export P2MW.S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental (solution)
