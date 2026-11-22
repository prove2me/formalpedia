-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_substS_monomial__39ec68064bef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:27.965327+00:00
-- url     : https://prove2.me/submissions/17781dfe-67fd-415c-8387-d5a1181d2019

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α : L × Fin r →₀ ℕ) (c : K) :
    substS ι sg S A B (monomial α c) = C (ι c) * substS ι sg S A B (monomial α 1) := by
  rw [substS_monomial, substS_monomial ι sg S A B α 1, map_one, map_one, one_mul]
end Formalism.MainNotions.PlaneGram
