-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_eval__monomial_cone_2bc04389d40a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:36.526337+00:00
-- url     : https://prove2.me/submissions/d724509b-9a8b-40b2-b064-61abaaa7f6ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
namespace GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
theorem _root_.solution {F Φ : Type*} [CommRing F] [CommRing Φ] (α : F →+* Φ) {K : Type*}
    {ι : K → Type*} (z : (Σ k, ι k) → Φ) (m : (Σ k, ι k) →₀ ℕ) (c : F) :
    eval₂ (C.comp α) (fun p => C (z p) * X p.1) (monomial m c) =
      C (eval₂ α z (monomial m c)) * monomial (Finsupp.mapDomain Sigma.fst m) (1 : Φ) := by
  rw [eval₂_monomial, eval₂_monomial, monomial_eq, C_1, one_mul,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [mul_pow, Finsupp.prod_mul, map_mul, RingHom.coe_comp, Function.comp_apply,
    map_finsuppProd, map_pow, mul_assoc]
end GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
