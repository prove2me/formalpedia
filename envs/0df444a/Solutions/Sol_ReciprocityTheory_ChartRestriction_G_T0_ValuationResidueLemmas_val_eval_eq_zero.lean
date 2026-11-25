-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.val_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:04:15.934513+00:00
-- url     : https://prove2.me/submissions/f2908ff8-5a9b-4da4-a0a2-2e1ea77ce9c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_residue_ne_zero_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
namespace ValuationResidueLemmas
section
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
private lemma mem_iff_lemma (y : F) : y ∈ vRing v ↔ 0 ≤ v y := by
  first
    | exact Iff.rfl
    | exact Valuation.mem_valuationSubring_iff _ _
end
end ValuationResidueLemmas
namespace ValuationResidueLemmas
end ValuationResidueLemmas
namespace ValuationResidueLemmas
end ValuationResidueLemmas
end ReciprocityTheory.ChartRestriction.G.T0
end

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
    (P : MvPolynomial σ Ω) (hP : ∀ β, 0 ≤ w (algebraMap Ω U (P.coeff β))) (α : σ →₀ ℕ)
    (h1 : P.coeff α = 1) :
    w (MvPolynomial.aeval t P) = 0 := by
  letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)

  have hc : ∀ β, P.coeff β ∈ (vRing w).comap (algebraMap Ω U) := fun β =>
    ValuationSubring.mem_comap.2 ((mem_iff_lemma w _).2 (hP β))
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : MvPolynomial σ ((vRing w).comap (algebraMap Ω U)),
      MvPolynomial.map ((vRing w).comap (algebraMap Ω U)).subtype P₀ = P := by
    first
      | (refine ⟨∑ β ∈ P.support, MvPolynomial.monomial β
            (⟨P.coeff β, hc β⟩ : (vRing w).comap (algebraMap Ω U)), ?_⟩
         rw [map_sum]
         simp only [MvPolynomial.map_monomial]
         conv_rhs => rw [P.as_sum]
         rfl)
      | exact MvPolynomial.mem_range_map_iff_coeffs_subset.2 (fun c hc' => by
          obtain ⟨β, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc'
          exact ⟨⟨_, hc β⟩, rfl⟩)

  have hQ1 : ((MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U))
      (fun s => (⟨t s, ht s⟩ : vRing w)) P₀ : vRing w) : U) = MvPolynomial.aeval t P := by
    rw [← hP₀, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have h2 := MvPolynomial.eval₂_comp_left (vRing w).subtype
      (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U)) (fun s => (⟨t s, ht s⟩ : vRing w)) P₀
    first
      | exact h2
      | (rw [← h2]; rfl)
  have hhom : (residue (vRing w)).comp (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U)) =
      (algebraMap (ResidueField ((vRing w).comap (algebraMap Ω U))) (ResidueField (vRing w))).comp
        (residue ((vRing w).comap (algebraMap Ω U))) := by
    ext x
    first
      | rfl
      | exact (IsLocalRing.ResidueField.map_residue _ _).symm
  have hkey : MvPolynomial.aeval (fun s => residue (vRing w) ⟨t s, ht s⟩)
      (MvPolynomial.map (residue ((vRing w).comap (algebraMap Ω U))) P₀) =
      residue (vRing w) (MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U))
        (fun s => (⟨t s, ht s⟩ : vRing w)) P₀) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left, hhom]
    rfl
  have hα : P₀.coeff α = 1 := by
    apply Subtype.ext
    have h3 := congrArg (MvPolynomial.coeff α) hP₀
    rw [MvPolynomial.coeff_map, h1] at h3
    exact h3
  have hne0 : MvPolynomial.map (residue ((vRing w).comap (algebraMap Ω U))) P₀ ≠ 0 := by
    intro h0
    have h4 := congrArg (MvPolynomial.coeff α) h0
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, hα, map_one] at h4
    exact one_ne_zero h4
  have hne : residue (vRing w) (MvPolynomial.eval₂
      (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U))
      (fun s => (⟨t s, ht s⟩ : vRing w)) P₀) ≠ 0 := by
    rw [← hkey]
    intro h0
    apply hne0
    first
      | exact algebraicIndependent_iff.1 hind _ h0
      | exact hind (by rw [h0, map_zero])
  have h5 := (residue_ne_zero_iff w _).1 hne
  rw [hQ1] at h5
  exact h5
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
