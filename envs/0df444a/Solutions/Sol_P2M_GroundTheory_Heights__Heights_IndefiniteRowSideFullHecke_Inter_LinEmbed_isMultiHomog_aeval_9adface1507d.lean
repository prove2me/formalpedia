-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_aeval_9adface1507d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:04:00.64174+00:00
-- url     : https://prove2.me/submissions/ccfb1405-e1a2-481b-92a8-1379738eece6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')]
open Classical
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
theorem _root_.solution (τ : K ≃ K') (g : (Σ k, ι k) → MRingOver F ι')
    (hg : ∀ p, IsMultiHomog (g p) (Pi.single (τ p.1) 1)) {s : MRingOver F ι} {a : K → ℕ}
    (hs : IsMultiHomog s a) : IsMultiHomog (aeval g s) (a ∘ τ.symm) := by
  classical
  conv_lhs => rw [s.as_sum]
  rw [map_sum]
  refine isMultiHomog_sum _ _ fun m hm => ?_
  have hm' := hs m hm
  have hdeg : (0 + ∑ p ∈ m.support, m p • (Pi.single (τ p.1) 1 : K' → ℕ)) = a ∘ τ.symm := by
    funext k'
    rw [zero_add, Finset.sum_apply, Function.comp_apply, ← hm' (τ.symm k')]
    rw [Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, zero_smul, Pi.zero_apply])]
    rw [Fintype.sum_sigma, Finset.sum_eq_single (τ.symm k')]
    · simp
    · intro k _ hk
      have hk' : k' ≠ τ k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
      simp [Pi.single_eq_of_ne hk']
    · simp
  have h := isMultiHomog_mul (isMultiHomog_C (ι := ι') (coeff m s))
    (isMultiHomog_prod m.support _ _ fun p _ => isMultiHomog_pow (hg p) (m p))
  rw [hdeg] at h
  rwa [aeval_monomial, MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
