-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:38.119279+00:00
-- url     : https://prove2.me/submissions/27850902-c729-4deb-aa0e-24c7d162f686

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramDet_comap_641348eb9df1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
namespace HermitianBundle
theorem _root_.solution (E : HermitianBundle K)
    (F : Submodule (𝓞 K) E.carrier) {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → F}
    (hs : LinearIndependent (𝓞 K) s) (hcard : Fintype.card ι = E.rank F) :
    E.degree F = Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s))) -
      (1 / 2) * ∑ σ : K →+* ℂ,
        Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ (fun i ↦ (s i : E.carrier))) := by
  rw [HermitianBundle.degree_eq_arithDegree, arithDegree_eq _ hs hcard, GroundTheory.Heights₂.Heights.degreeWith]
  simp only [gramDet_comap, Submodule.subtype_apply]
end HermitianBundle
end GroundTheory.Heights₂.Heights
