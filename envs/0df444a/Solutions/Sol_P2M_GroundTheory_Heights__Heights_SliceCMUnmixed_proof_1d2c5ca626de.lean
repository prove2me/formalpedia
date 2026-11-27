-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCMUnmixed_proof_1d2c5ca626de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:24.851022+00:00
-- url     : https://prove2.me/submissions/29fccfd9-86c7-4856-80fa-c2d565d7ce82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCMUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMQuotientUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceCMUnmixed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sliceCMUnmixed_local_c3dc3ab32cc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385


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
open MvPolynomial Matrix ComplexSets IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace SliceCMUnmixed
theorem _root_.solution (h : CMQuotientUnmixed.Statement) : SliceCMUnmixed.Statement := by
  intro n d J L q hCM hdimB hdimS P hP hPm
  have : IsCohenMacaulayLocalRing (localRingAt J q) := hCM
  have hℓ : ∀ i, linPoly L i - C ((L *ᵥ q) i) ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := by
    intro i
    rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self]
  have hsl : sliceIdeal J L q = J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i)) := rfl
  rw [hsl] at hP hdimS ⊢
  have h1 := sliceCMUnmixed_local h (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) J
    (fun i => linPoly L i - C ((L *ᵥ q) i)) hℓ (localRingAt J q)
  have h2 := h1 (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.mk_ker
  have h3 := h2 hdimB hdimS
  exact h3 P hP hPm
end SliceCMUnmixed
end GroundTheory.Heights₂.Heights
