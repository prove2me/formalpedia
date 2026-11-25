-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveProperClosedFinite_proof_19a9f160baa2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:20.535202+00:00
-- url     : https://prove2.me/submissions/6c92fd92-e21a-4f4c-a132-8726b40fe576

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveProperClosedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveProperClosedFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveProperClosedFinite_no_chain_two_1b7260404b30

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
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace CurveProperClosedFinite
theorem _root_.solution : CurveProperClosedFinite.Statement := by
  intro n W K hW hdim hK
  let m : (Fin n → ℂ) → Ideal (MvPolynomial (Fin n) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have hx : X i - C (x i) ∈ m x := by simp [m, RingHom.mem_ker]
    have hy : X i - C (x i) ∈ m y := hxy ▸ hx
    have hy' : y i - x i = 0 := by simpa [m, RingHom.mem_ker] using hy
    exact (sub_eq_zero.1 hy').symm
  have hsub : m '' (zeroSet W ∩ zeroSet K) ⊆ (W ⊔ K).minimalPrimes := by
    rintro _ ⟨x, ⟨hxW, hxK⟩, rfl⟩
    have hmax : (m x).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective (eval x) (fun c => ⟨C c, by simp⟩)
    have hle : W ⊔ K ≤ m x := sup_le (fun q hq => hxW q hq) (fun q hq => hxK q hq)
    refine ⟨⟨hmax.isPrime, hle⟩, fun Q ⟨hQ, hJQ⟩ hQm => ?_⟩
    by_contra hmQ
    have hWQ : W < Q := by
      refine lt_of_le_of_ne (le_sup_left.trans hJQ) ?_
      rintro rfl
      exact hK (le_sup_right.trans hJQ)
    exact CurveProperClosedFinite.no_chain_two hW hQ hmax.isPrime hdim hWQ (lt_of_le_of_ne hQm
      (fun h => hmQ (h ▸ le_rfl)))
  exact Set.Finite.of_finite_image
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset hsub) hinj.injOn
end CurveProperClosedFinite
end GroundTheory.Heights₂.Heights
