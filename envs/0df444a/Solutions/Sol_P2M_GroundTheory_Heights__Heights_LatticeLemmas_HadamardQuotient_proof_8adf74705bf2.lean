-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_proof_8adf74705bf2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:04:07.644568+00:00
-- url     : https://prove2.me/submissions/0b8812e1-9865-42cf-9ace-46ace4b473da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_exists_subfamily_card_eq_finrank_7faf8527523a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_normAt_mkQ_le_f55819c0c9d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights
universe u v w
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace HadamardQuotient
theorem _root_.solution (h1 : Hadamard.Statement.{u, v, w}) :
    HadamardQuotient.Statement.{u, v, w} := by
  intro K _ _ M F hF ι x La hx hLa
  obtain ⟨s, hs, hfin, hcard⟩ := exists_subfamily_card_eq_finrank F x hx
  have := Fintype.ofFinite s
  exact h1 K (M.quot F hF) (ι := s) (fun i ↦ F.mkQ (x i)) La hs
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    (fun i σ ↦ (normAt_mkQ_le M F hF σ (x i)).trans (hLa i σ))
end HadamardQuotient
end GroundTheory.Heights₂.Heights.LatticeLemmas
