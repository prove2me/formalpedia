-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isRegularSection_form_6765ee38e78f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:19.646892+00:00
-- url     : https://prove2.me/submissions/97017e50-f1e8-4e75-8b0e-cef4c4ba7211

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    {P : Ideal (MRing ι F)} (hP : P.IsPrime) {a : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsRegularSection P (fun k => (a k : ℤ)) s 1 where
  degrees := ⟨a, 0, hs, MvPolynomial.isWeightedHomogeneous_one _ _, by funext k; simp⟩
  num_not_mem := hsP
  den_not_mem := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  regular := fun W hW _ => ⟨1, s, fun h => hW.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
end GroundTheory.Heights₂.Heights.Model
