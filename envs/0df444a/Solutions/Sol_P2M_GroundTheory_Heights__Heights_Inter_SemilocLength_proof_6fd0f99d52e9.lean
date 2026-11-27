-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocLength_proof_6fd0f99d52e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:49.761593+00:00
-- url     : https://prove2.me/submissions/abde6be1-76b7-478b-801f-53e570a222ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocLength

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemilocLength
theorem _root_.solution (h₁ : SemilocLengthSum.Statement) (h₂ : FibreDivSupp.Statement)
    (h₃ : regularityDehomogenization_holds.Statement) : SemilocLength.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE
  have := hP'.2.1.1
  have hfib := h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  obtain ⟨-, N, hN, hsum⟩ := h₁ K ι K' ι' κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy
    (fun W' hW' hsW' => hE W' ((hfib W').1 ⟨hW', hsW'⟩).1 ((hfib W').1 ⟨hW', hsW'⟩).2)
  refine ⟨N, hN, hsum.trans (finsum_mem_congr (Set.ext fun W' => hfib W') fun W' hW' => ?_)⟩
  obtain ⟨hW'd, hW'i⟩ := hW'
  have hs' : rename v s ∉ P' := hsP
  have ht' : rename v t ∉ W' := fun h => htW (hW'i ▸ h)
  have hy' : fracMapZ v P' y * algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))
      (Ideal.Quotient.mk P' (rename v t)) =
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (rename v s)) := by
    rw [← fracMapZ_algebraMap, ← fracMapZ_algebraMap, ← map_mul, hy]
  rw [(h₃ K' ι' P' (rename v s) (rename v t) (Function.extend κ α 0) W' (fracMapZ v P' y) hP'.2.1
    (rename_isMultiHomog hv hs) hs' hW'd (rename_isMultiHomog hv ht) ht' hy').2]
end SemilocLength
end GroundTheory.Heights₂.Heights.Inter
