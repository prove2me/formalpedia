-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_pow_fbfa36c014cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:27.640675+00:00
-- url     : https://prove2.me/submissions/a3939b34-7f58-44bf-ad19-06052c74620c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_mul_dc8f078d9407
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_one_f1d8f695b8c6

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Inter.Choice
theorem _root_.solution {f : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (homog_one (R := R) (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hf
end GroundTheory.Heights₂.Heights.Inter.Choice
