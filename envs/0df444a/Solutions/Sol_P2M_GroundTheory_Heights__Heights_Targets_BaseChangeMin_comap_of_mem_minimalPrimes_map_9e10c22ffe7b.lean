-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_comap_of_mem_minimalPrimes_map_9e10c22ffe7b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:55.947372+00:00
-- url     : https://prove2.me/submissions/22e42c73-ae79-4fd1-8751-9d2fed732618

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_flat_mvPolynomial_map_770f1c9d3b57

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
attribute [local instance] MvPolynomial.algebraMvPolynomial
omit [Fintype σ]
namespace GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
theorem _root_.solution (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ F'))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap F F')) = 𝔭 := by
  have := flat_mvPolynomial_map (σ := σ) (F := F) (F' := F')
  have hQp : Q.IsPrime := hQ.1.1
  have hle : Ideal.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F')) 𝔭 ≤ Q := hQ.1.2
  set q := Q.comap (algebraMap (MvPolynomial σ F) (MvPolynomial σ F')) with hq
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  have hpq : 𝔭 ≤ q := Ideal.map_le_iff_le_comap.mp hle
  obtain ⟨P, hPQ, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hpq
  have hPext : Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭 ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hQP : Q ≤ P := hQ.2 ⟨hP, hPext⟩ hPQ
  have hPQe : P = Q := le_antisymm hPQ hQP
  subst hPQe
  exact hPl.over.symm
end GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
