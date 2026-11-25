-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.exists_val_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:33.886269+00:00
-- url     : https://prove2.me/submissions/1f6fa224-d462-4f96-9e13-186a23accdfa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_nonneg_of_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_val_eval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
theorem _root_.solution {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (P : MvPolynomial σ Ω) (hP : P ≠ 0) :
    ∃ c : Ω, c ≠ 0 ∧ w (MvPolynomial.aeval t P) = w (algebraMap Ω U c) := by
  classical
  have hsupp : P.support.Nonempty := by
    first
      | exact Finsupp.support_nonempty_iff.2 hP
      | (rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hP)

  obtain ⟨β₀, hβ₀, hmin⟩ := Finset.exists_min_image P.support
    (fun β => w (algebraMap Ω U (P.coeff β))) hsupp
  have hc0 : P.coeff β₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hβ₀
  refine ⟨P.coeff β₀, hc0, ?_⟩
  have hfc : w (algebraMap Ω U (P.coeff β₀)) ≠ ⊤ := by
    intro h
    rw [AddValuation.top_iff] at h
    exact hc0 ((algebraMap Ω U).injective (h.trans (map_zero _).symm))

  have hQ : ∀ β, 0 ≤ w (algebraMap Ω U ((MvPolynomial.C (P.coeff β₀)⁻¹ * P).coeff β)) := by
    intro β
    rw [MvPolynomial.coeff_C_mul]
    by_cases hβ : β ∈ P.support
    · have e : algebraMap Ω U ((P.coeff β₀)⁻¹ * P.coeff β) * algebraMap Ω U (P.coeff β₀) =
          algebraMap Ω U (P.coeff β) := by
        rw [← map_mul]
        congr 1
        field_simp
      exact wt_nonneg_of_add hfc (by rw [← AddValuation.map_mul, e]) (hmin β hβ)
    · rw [MvPolynomial.notMem_support_iff.1 hβ, mul_zero, map_zero, AddValuation.map_zero]
      exact le_top
  have hQ1 : (MvPolynomial.C (P.coeff β₀)⁻¹ * P).coeff β₀ = 1 := by
    rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc0]
  have h1 := val_eval_eq_zero w t ht hind _ hQ β₀ hQ1
  rw [map_mul, MvPolynomial.aeval_C, AddValuation.map_mul] at h1
  have h2 : w (algebraMap Ω U (P.coeff β₀)⁻¹) + w (algebraMap Ω U (P.coeff β₀)) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, inv_mul_cancel₀ hc0, map_one, AddValuation.map_one]
  have ha : w (algebraMap Ω U (P.coeff β₀)⁻¹) ≠ ⊤ := by
    intro h
    rw [AddValuation.top_iff] at h
    exact (inv_ne_zero hc0) ((algebraMap Ω U).injective (h.trans (map_zero _).symm))
  generalize w (algebraMap Ω U (P.coeff β₀)⁻¹) = a at ha h1 h2
  generalize w (MvPolynomial.aeval t P) = X at h1 ⊢
  generalize w (algebraMap Ω U (P.coeff β₀)) = Y at h2 ⊢
  induction a using WithTop.recTopCoe with
  | top => exact absurd rfl ha
  | coe a =>
    induction X using WithTop.recTopCoe with
    | top => simp at h1
    | coe X =>
      induction Y using WithTop.recTopCoe with
      | top => simp at h2
      | coe Y =>
        have e1 : a + X = 0 := by exact_mod_cast h1
        have e2 : a + Y = 0 := by exact_mod_cast h2
        have e3 : X = Y := by omega
        rw [e3]
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
