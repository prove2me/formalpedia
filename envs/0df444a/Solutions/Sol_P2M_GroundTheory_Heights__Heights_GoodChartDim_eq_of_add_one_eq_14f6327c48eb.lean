-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartDim_eq_of_add_one_eq_14f6327c48eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:55.155715+00:00
-- url     : https://prove2.me/submissions/8e1c7ce2-9ba6-41e0-a35e-0ceaf6e80983

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartDim

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.GoodChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.GoodChartDim
theorem _root_.solution {x : WithBot ℕ∞} {e : ℕ} (h : x + 1 = (e : WithBot ℕ∞) + 1) : x = e := by
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← Nat.cast_succ] at h
    exact absurd h (WithBot.bot_ne_natCast _)
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = ((e + 1 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_inj, top_add] at h'
      exact absurd h' (by exact_mod_cast (ENat.top_ne_natCast (e + 1)))
    | coe x =>
      have h' : ((x + 1 : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h'' : x + 1 = e + 1 := by exact_mod_cast h'
      exact_mod_cast (show x = e by omega)
end GroundTheory.Heights₂.Heights.GoodChartDim
