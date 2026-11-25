-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.relation_map_comm_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:09:00.956709+00:00
-- url     : https://prove2.me/submissions/c1104cde-c0e2-46fa-ad4c-5af5f3e51244

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trv_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (c : ι) (i k : Fin (d.D + 1)) (hik : i ≠ k) :
    (Polynomial.mapRingHom (d.relationEliminateColumn c).toRingHom).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom =
      (trv (R := Ω c) i k Polynomial.X).toRingHom.comp (d.relationEliminateColumn c).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [trv, Data.relationEliminateColumn]
  · rintro ⟨a, b⟩
    have hC : ∀ x : Ω c, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (C x) = Polynomial.C (C x) := by
      intro x
      simp [trv, Polynomial.algebraMap_apply]
    have hX : ∀ r l, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (X (r, l)) =
        Polynomial.C (X (r, l)) + (if r = i then Polynomial.X * Polynomial.C (X (k, l)) else 0) := by
      intro r l
      rw [trv_X]
      split_ifs <;> simp_all
    have hXK : ∀ r l, trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X (X (r, l)) =
        Polynomial.C (X (r, l)) + (if r = i then Polynomial.X * Polynomial.C (X (k, l)) else 0) := by
      intro r l
      rw [trv_X]
      split_ifs <;> simp_all

    set φ : Fin (d.D + 1) → MvPolynomial (TVar d.D d.N) (Ω c) := fun r => d.relationEliminateColumn c (X (r, b)) with hφ
    have hφtrv : ∀ r, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (φ r) =
        Polynomial.C (φ r) + (if r = i then Polynomial.X * Polynomial.C (φ k) else 0) := by
      intro r
      by_cases h2 : b = d.jc c
      · have e1 : ∀ r', φ r' = -∑ l ∈ Finset.univ.erase (d.jc c),
            X (r', l) * C (ratio (Ω := Ω c) (d.w l c) (d.w (d.jc c) c)) := by
          intro r'
          simp only [hφ, Data.relationEliminateColumn, MvPolynomial.aeval_X, h2, eq_self_iff_true, if_true]
        rw [e1 r, e1 k, map_neg, map_sum]
        by_cases h1 : r = i
        · simp only [h1, eq_self_iff_true, if_true, map_mul, hX, hC, map_neg, map_sum, add_mul,
            Finset.sum_add_distrib, mul_neg, Finset.mul_sum, mul_assoc, neg_add]
        · simp only [h1, if_false, add_zero, map_mul, hX, hC, map_neg, map_sum]
      · have e1 : ∀ r', φ r' = X (r', b) := by
          intro r'
          simp only [hφ, Data.relationEliminateColumn, MvPolynomial.aeval_X, h2, if_false]
        rw [e1 r, e1 k, hX]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_mapRingHom]
    rw [hXK a b]
    change _ = trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (φ a)
    rw [hφtrv a]
    by_cases h1 : a = i
    · simp only [h1, eq_self_iff_true, if_true, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X]
      rfl
    · simp only [h1, if_false, add_zero, Polynomial.map_C]
      rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
