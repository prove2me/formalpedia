-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:54.254814+00:00
-- url     : https://prove2.me/submissions/add44b06-3e9a-445d-bed0-33ec352bb013

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_cycEval_ratDiv_d916b441ca86

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace CutRational
theorem _root_.solution (h1 : CutRegular.Statement.{u}) (h2 : IntNumAdd.Statement.{u}) :
    CutRational.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hn bf bg f g hf hg hfP hgP bs
  have hadd := h2 F K ι P hP.multiHomog hP.relevant (n + 1) hn
    (Fin.snoc (α := fun _ => K → ℤ) bs 0) (Fin.last n)
    (fun k => (bf k : ℤ) - bg k) (fun k => (bg k : ℤ))
  simp only [Fin.update_snoc_last] at hadd
  have hsum : ((fun k => (bf k : ℤ) - bg k) + fun k => (bg k : ℤ)) = fun k => (bf k : ℤ) := by
    funext k; simp
  rw [hsum, h1 F K ι P hP n hn bf f hf hfP bs, h1 F K ι P hP n hn bg g hg hgP bs] at hadd
  rw [cycEval_ratDiv]
  linarith
end CutRational
end GroundTheory.Heights₂.Heights.FieldNumbers
