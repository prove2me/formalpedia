-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_iwasawa__f83cbdce79a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:49:21.772989+00:00
-- url     : https://prove2.me/submissions/23fe88c5-8f39-4878-9072-efd389dfe36f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Theorems.Thm_Formalism_L2_Pj_iwasawa
import Theorems.Thm_Formalism_L2_Pj_upper_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open Matrix IsDedekindDomain
variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
namespace Formalism.L2.Pj
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (N : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ N.BlockTriangular id ∧
      (∀ i, N i i ≠ 0) ∧ A * N = k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, hA⟩ := iwasawa (V := V) A hA
  obtain ⟨hinv, hdinv, hUU⟩ := upper_inv U hU hd
  refine ⟨k, U⁻¹, hk, hinv, hdinv, ?_⟩
  rw [hA, Matrix.mul_assoc, hUU, Matrix.mul_one]
end Formalism.L2.Pj
