-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_up_95943556fabe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:50:47.967426+00:00
-- url     : https://prove2.me/submissions/b24800ec-f798-4c4d-8f96-9284f8516d2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_segreLine_a_a7bacdd13797
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_secOf_spec_345d47ba9dcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_upDeg_cast_eb6ec3376b64

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (A : HermLine ι) :
    IsSectionOn P (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) :=
  ⟨upDeg A, fun _ => by simp [HermLine.tensor, segreLine_a, upDeg_cast], (secOf_spec hP _).1,
    (secOf_spec hP _).2⟩
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
