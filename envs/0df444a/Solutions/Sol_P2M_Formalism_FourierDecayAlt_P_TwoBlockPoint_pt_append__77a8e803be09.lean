-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_pt_append__77a8e803be09
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:25.485563+00:00
-- url     : https://prove2.me/submissions/cba413f5-7e5b-4d7b-95d6-ac80499097d6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_pt_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (L l l' : List ℕ) (hL : L = l ++ l') (T T₁ T₂ : ℕ → Kˣ)
    (h₁ : ∀ b, b < l.length → T b = T₁ b) (h₂ : ∀ b, b < l'.length → T (l.length + b) = T₂ b)
    (hN : L.sum = l.sum + l'.sum) : pt L T = blkM hN (pt l T₁) 0 0 (pt l' T₂) := by
  subst hL
  exact pt_append l l' T T₁ T₂ h₁ h₂ hN
end Formalism.FourierDecayAlt.P.TwoBlockPoint
