-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_trdeg_adjoin_1be3e3994da1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:19:04.581492+00:00
-- url     : https://prove2.me/submissions/0cf24c06-7bc2-4493-92f8-e9fbd77c5dc3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AevalMemAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_ker_aeval_F_7dc16d4c0989

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.FibreTranscendence
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.Inter.FibreTranscendence
theorem _root_.solution [Fintype K] [∀ k, Fintype (ι k)] (hE : EvalKerKrullDim.Statement) {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L]
    (y : (Σ k, ι k) → L) {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J)
    (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) {n : ℕ} (hV : IsProjVarF (J.map (PointVertical.red (ι := ι) p)) n) :
    Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y)) = ((n + Fintype.card K : ℕ) : Cardinal) := by
  have h := hE K ι (ZMod p) L y
  rw [ker_aeval_F p y hp hJ, hV.2] at h
  have h' : (Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y))).toENat =
      ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h.symm
  exact Cardinal.toENat_eq_natCast.mp h'
end GroundTheory.Heights₂.Heights.Inter.FibreTranscendence
