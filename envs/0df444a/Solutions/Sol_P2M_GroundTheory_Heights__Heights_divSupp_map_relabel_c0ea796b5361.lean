-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_divSupp_map_relabel_c0ea796b5361
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:27.88681+00:00
-- url     : https://prove2.me/submissions/e5e200f0-526a-4b64-b8b3-26f1a384813a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_minimalPrimes_map_ringEquiv_b33fb8696bed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRelevant_map_relabel_iff_831acc433198

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (V : Ideal (MRing ι)) (s : MRing ι) :
    divSupp (V.map (relabelRingEquiv ε h)) (relabelRingEquiv ε h s) =
      Ideal.map (relabelRingEquiv ε h) '' divSupp V s := by
  have hsup : V.map (relabelRingEquiv ε h) ⊔ Ideal.span {relabelRingEquiv ε h s} =
      (V ⊔ Ideal.span {s}).map (relabelRingEquiv ε h) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  ext W'
  simp only [divSupp, Set.mem_ofPred_eq, Set.mem_image, hsup, minimalPrimes_map_ringEquiv]
  constructor
  · rintro ⟨⟨W, hW, rfl⟩, hrel⟩
    exact ⟨W, ⟨hW, (isRelevant_map_relabel_iff ε h W).1 hrel⟩, rfl⟩
  · rintro ⟨W, ⟨hW, hrel⟩, rfl⟩
    exact ⟨⟨W, hW, rfl⟩, (isRelevant_map_relabel_iff ε h W).2 hrel⟩
end GroundTheory.Heights₂.Heights
