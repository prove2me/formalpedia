-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_preimage_phi_e3189524c6f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:40.560455+00:00
-- url     : https://prove2.me/submissions/e6f86761-88e2-4295-836f-37051e3bef56

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_coe_phi_846279105f53
import Theorems.Thm_Formalism_REAL_injective_coeMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
variable {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (A : Set (UJ ε)) : (phi ε e h1 h2) ⁻¹' A =
    {g | ∃ a ∈ A, ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindex e e (UpqT.mat g)} := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro hg
    exact ⟨_, hg, coe_phi ε e h1 h2 g⟩
  · rintro ⟨a, ha, hag⟩
    have : a = phi ε e h1 h2 g := injective_coeMatrix ε (by rw [coe_phi]; exact hag)
    rw [← this]
    exact ha
end Formalism.BasicNotions.Examples₂.CD
