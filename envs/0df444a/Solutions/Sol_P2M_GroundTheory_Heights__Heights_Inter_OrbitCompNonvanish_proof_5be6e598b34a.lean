-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_proof_5be6e598b34a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:48.093841+00:00
-- url     : https://prove2.me/submissions/cd93f3c8-6499-4f7c-9260-1237769bb7f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_POrbitCompNonvanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_isHomogeneous_blkWt_dd2d96ba1873
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_isMultiHomog_component_c257cf16c06e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_homog


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
namespace OrbitCompNonvanish
theorem _root_.solution : OrbitCompNonvanish.Statement := by
  intro K _ ι _ P E hP hE
  classical
  have hPh := OrbitCompNonvanish.isHomogeneous_blkWt hP
  obtain ⟨δ, hδ⟩ : ∃ δ, weightedHomogeneousComponent (blkWt (ι := ι)) δ E ∉ P := by
    by_contra h
    push Not at h
    exact hE ((mem_iff_weightedHomogeneousComponent_mem ℤ _ hPh E).mpr h)
  refine ⟨_, δ, OrbitCompNonvanish.isMultiHomog_component E δ, hδ, fun z hz => ?_⟩

  let comp : (K →₀ ℕ) → MRing ι := fun b => weightedHomogeneousComponent (blkWt (ι := ι)) b E
  let lam : (K →₀ ℕ) → ℂ := fun b => eval z (map (Int.castRingHom ℂ) (comp b))
  have hfin := weightedHomogeneousComponent_finsupp (w := blkWt (ι := ι)) E
  let T : Finset (K →₀ ℕ) := insert δ hfin.toFinset
  have hsum : ∑ b ∈ T, comp b = E := by
    rw [← Finset.sum_subset (Finset.subset_insert δ hfin.toFinset), ← finsum_eq_sum _ hfin]
    · exact sum_weightedHomogeneousComponent _ E
    · intro b _ hb
      by_contra hne
      exact hb (hfin.mem_toFinset.mpr hne)
  let Q : MvPolynomial K ℂ := ∑ b ∈ T, monomial b (lam b)
  have hQ : ∀ c : K → ℂ, eval c Q = eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) E) := by
    intro c
    conv_rhs => rw [← hsum]
    simp only [Q, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [eval_smul_homog (comp b) b (OrbitCompNonvanish.isMultiHomog_component E b) c z, eval_monomial,
      Finsupp.prod_fintype _ _ (by simp)]
    ring
  have hQ0 : Q ≠ 0 := by
    intro h0
    have hc := congrArg (coeff δ) h0
    simp only [Q, coeff_sum, coeff_monomial, coeff_zero] at hc
    rw [Finset.sum_ite_eq' T δ, if_pos (Finset.mem_insert_self _ _)] at hc
    exact hz hc
  by_contra hno
  push Not at hno
  apply hQ0
  refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton 0).infinite_compl)
    fun x hx => ?_
  rw [hQ, map_zero]
  exact hno x fun k => hx k (Set.mem_univ k)
end OrbitCompNonvanish
end GroundTheory.Heights₂.Heights.Inter
