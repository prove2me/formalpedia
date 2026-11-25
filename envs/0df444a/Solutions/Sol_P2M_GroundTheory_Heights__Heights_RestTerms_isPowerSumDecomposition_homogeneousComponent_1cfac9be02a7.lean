-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_isPowerSumDecomposition_homogeneousComponent_1cfac9be02a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:18.713897+00:00
-- url     : https://prove2.me/submissions/ff6fa201-0011-4118-84f7-c15b4f516c60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_blockPowerSum_isHomogeneous_c5d784bee3b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HomogeneousComponentMul_proof_071fefd82e0b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.RestTerms.rootRingToReal_X
attribute [local simp] GroundTheory.Heights₂.Heights.RestTerms.rootRingToReal_C

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f N : ℕ) (F : RootRing f N)
    (Q : ℕ → Fin f → RootRing f N) (hF : F.IsHomogeneous (topDegree f N + 1))
    (hQ : IsPowerSumDecomposition f N F Q) :
    IsPowerSumDecomposition f N F
        (fun m τ => homogeneousComponent (topDegree f N + 1 - m) (Q m τ)) ∧
      ∀ m τ, (homogeneousComponent (topDegree f N + 1 - m) (Q m τ)).IsHomogeneous
        (topDegree f N + 1 - m) := by
  refine ⟨?_, fun m τ => homogeneousComponent_isHomogeneous _ _⟩
  have hle : ∀ m, m ≤ N → ∀ τ : Fin f, m ≤ topDegree f N + 1 := by
    intro m hm τ
    have hf : 0 < f := τ.pos
    have h1 : N - 1 ≤ N * (N - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      rcases N with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]
        rcases n with _ | n
        · simp
        · nlinarith
    have h2 : N * (N - 1) / 2 ≤ topDegree f N := Nat.le_mul_of_pos_left _ hf
    omega
  unfold IsPowerSumDecomposition at hQ ⊢
  have hcomp : homogeneousComponent (topDegree f N + 1) F = F := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hF), if_pos rfl]
  conv_lhs => rw [← hcomp, hQ]
  simp only [map_sum]
  refine sum_congr rfl fun m hm => sum_congr rfl fun τ _ => ?_
  rw [HomogeneousComponentMul.proof _ _ _ _ _ _ (blockPowerSum_isHomogeneous f N m τ),
    if_pos (hle m (Finset.mem_Icc.1 hm).2 τ)]
end GroundTheory.Heights₂.Heights.RestTerms
