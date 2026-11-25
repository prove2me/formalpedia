-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_psumExpansion_cac4269a2de6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:26:47.24031+00:00
-- url     : https://prove2.me/submissions/3410d688-eb0d-4947-a3c0-791b171c3406

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_rename_1c775c5899c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_geoSum_rename_6748cb29faab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_eq_polyVal_bf23e9c95722
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psumExpansion_217a129f2629


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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (u v : Fin N → K → ℤ) (k : ℕ) (i : Fin N) {Q : List (K → ℤ)}
    {d : ℕ} (hQ : Q.length + k = d + 1) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim u v) (psumExpansion N k i) Q W = geoVal (listNum W Q d) k (u i) (v i) := by
  cases k with
  | zero => simp [classNum, psumExpansion, geoVal, geoSum, polyVal]
  | succ m =>
    have e : psumExpansion N (m + 1) i =
        rename ![Sum.inl i, Sum.inr i] (geoSum (m + 1) (X 0) (X 1)) := by
      rw [geoSum_rename]; rfl
    have hc : (Sum.elim u v ∘ ![Sum.inl i, Sum.inr i]) = ![u i, v i] := by
      funext j
      fin_cases j <;> rfl
    rw [classNum_eq_polyVal (Q := Q) (d := d) _ (isHomogeneous_psumExpansion N (m + 1) i)
      (by omega), e, polyVal_rename, hc, geoVal]
end GroundTheory.Heights₂.Heights.NumbersDVR
