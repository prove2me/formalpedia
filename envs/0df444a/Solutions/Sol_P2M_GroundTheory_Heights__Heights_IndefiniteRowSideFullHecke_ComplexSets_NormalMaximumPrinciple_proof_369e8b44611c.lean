-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalMaximumPrinciple_proof_369e8b44611c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:59:26.849733+00:00
-- url     : https://prove2.me/submissions/51e65876-f0bc-4abc-af7b-9ea317840a9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalMaximumPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalMaximumPrinciple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_of_sum_eq_nsmul_of_norm_le_831fa282c107

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter RealInnerProductSpace
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalMaximumPrinciple
theorem _root_.solution (htr : LocalTrace.Statement) : NormalMaximumPrinciple.Statement := by
  intro σ _ I w U g hI _ hw hU hg hle
  obtain ⟨k, A, B, D, m, T, hB, hwB, hBU, hD, hwD, hfib, hT, hrep⟩ := htr σ I w U g hI hw hU hg
  have hle' : ∀ z ∈ zeroSetIn I ∩ B, ‖g z‖ ≤ ‖g w‖ := fun z hz => hle z ⟨hz.1, hBU hz.2⟩

  have hTw : T (A w) = m • g w := by
    obtain ⟨x, hx, -, hTx⟩ := hrep (A w) hwD
    rw [hTx, Finset.sum_congr rfl fun j _ => congrArg g (hfib (x j) (hx j).1 (hx j).2),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]

  have hmax : IsLocalMax (norm ∘ T) (A w) := by
    filter_upwards [hD.mem_nhds hwD] with y hy
    obtain ⟨x, hx, -, hTx⟩ := hrep y hy
    simp only [Function.comp_apply, hTx, hTw]
    calc ‖∑ j, g (x j)‖ ≤ ∑ j, ‖g (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, ‖g w‖ := Finset.sum_le_sum fun j _ => hle' _ (hx j).1
      _ = ‖m • g w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp [nsmul_eq_mul]
  have hconst := Complex.eventually_eq_of_isLocalMax_norm
    (Filter.eventually_of_mem (hD.mem_nhds hwD) fun y hy =>
      (hT y hy).differentiableAt (hD.mem_nhds hy)) hmax
  have hcont : Tendsto A (𝓝 w) (𝓝 (A w)) := A.continuous.tendsto w
  filter_upwards [hB.mem_nhds hwB, hcont.eventually hconst, hcont.eventually (hD.mem_nhds hwD)]
    with z hzB hzT hzD hzZ
  obtain ⟨x, hx, hcov, hTx⟩ := hrep (A z) hzD
  obtain ⟨j, rfl⟩ := hcov z ⟨hzZ, hzB⟩ rfl
  exact eq_of_sum_eq_nsmul_of_norm_le (fun i => g (x i)) (g w) (fun i => hle' _ (hx i).1)
    (by rw [← hTx, hzT, hTw]) j
end NormalMaximumPrinciple
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
