-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__mass_le_of_card_class_reps_le_c99329ec7ab7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:26.741507+00:00
-- url     : https://prove2.me/submissions/407b699b-9690-42b5-8884-5b2af0ad5e74

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_GenusOrthonormalIntegralUnimodular
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s → (s.card : ℝ) ≤ B) : mass h L ≤ B := by
  classical
  unfold mass
  split_ifs with hs
  · refine le_trans ?_ (hc _ hs.choose_spec)
    calc ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ hs.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (Formalism.ThetaLiftIndependence.autL h M)) with h0 | h0
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast h0)
      _ = (hs.choose.card : ℝ) := by simp
  · exact hB
end Formalism.MainNotions.BridgeLemma₂
