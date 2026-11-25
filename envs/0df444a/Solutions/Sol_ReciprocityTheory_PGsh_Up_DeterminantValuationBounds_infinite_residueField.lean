-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.infinite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:19.465668+00:00
-- url     : https://prove2.me/submissions/d725f628-3db6-41e7-b4f8-11e89342f9a6

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
theorem _root_.solution [IsAlgClosed C] :
    Infinite (IsLocalRing.ResidueField v.valuationSubring) := by
  classical
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  letI := Fintype.ofFinite (IsLocalRing.ResidueField v.valuationSubring)
  obtain ⟨q, hq⟩ : ∃ q, q = Fintype.card (IsLocalRing.ResidueField v.valuationSubring) := ⟨_, rfl⟩
  have hq2 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := IsLocalRing.ResidueField v.valuationSubring)
    omega
  have hdeg : (Polynomial.X ^ q - (Polynomial.X + Polynomial.C 1) : Polynomial C).degree ≠ 0 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]
    · exact_mod_cast (by omega : q ≠ 0)
    · rw [Polynomial.degree_X_add_C]
      exact_mod_cast (by omega : 1 < q)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_C] at hα
  have hαq : α ^ q = α + 1 := sub_eq_zero.mp hα
  have hle : v α ≤ 1 := by
    by_contra h
    push_neg at h
    have h1 : v (α + 1) ≤ v α := by
      calc v (α + 1) ≤ max (v α) (v 1) := v.map_add _ _
        _ = v α := by rw [map_one]; exact max_eq_left h.le
    have h2 : v α < v α ^ q := by
      calc v α = v α ^ 1 := (pow_one _).symm
        _ < v α ^ q := pow_lt_pow_right₀ h (by omega)
    rw [← map_pow, hαq] at h2
    exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)
  have hmem : α ∈ v.valuationSubring := (v.mem_valuationSubring_iff α).mpr hle
  have hx : (⟨α, hmem⟩ : v.valuationSubring) ^ q = ⟨α, hmem⟩ + 1 := by
    apply Subtype.ext
    push_cast
    exact hαq
  have hr := congrArg (IsLocalRing.residue v.valuationSubring) hx
  have hpc := FiniteField.pow_card (IsLocalRing.residue v.valuationSubring ⟨α, hmem⟩)
  rw [← hq] at hpc
  rw [map_pow, map_add, map_one, hpc] at hr
  have h10 : (1 : IsLocalRing.ResidueField v.valuationSubring) = 0 := by
    have := congrArg (· - IsLocalRing.residue v.valuationSubring ⟨α, hmem⟩) hr
    simpa using this.symm
  exact one_ne_zero h10
end ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
