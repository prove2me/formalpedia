-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_proof_bc085c65b8cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:49.73735+00:00
-- url     : https://prove2.me/submissions/603b99de-cb10-458d-afb1-068903c8343a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_add_card_le_ringKrullDim_97857621ed3a

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace HilbDegreeBound
theorem _root_.solution (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u}) : HilbDegreeBound.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  refine ⟨fun _ p hp hp0 => ?_, fun hrel => hZ F K ι I hrel⟩
  have key := fun n => totalDegree_add_card_le_ringKrullDim h1 h2 h3 h4 hU hS hZ hD F K ι n I hI
  unfold relDim
  generalize hx : ringKrullDim (MRing ι F ⧸ I) = x at key
  induction x using WithBot.recBotCoe with
  | bot =>
    have := key 0 (WithBot.bot_lt_coe _) p hp hp0
    exact absurd this (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe N =>
      have := key (N + 1) (by exact_mod_cast Nat.lt_succ_self N) p hp hp0
      have hle : p.totalDegree + Fintype.card K ≤ N := by exact_mod_cast this
      show ((p.totalDegree : ℕ) : WithBot (WithTop ℤ)) ≤
        (((N : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
      have : (p.totalDegree : ℤ) ≤ (N : ℤ) - Fintype.card K := by omega
      exact_mod_cast this
end HilbDegreeBound
end GroundTheory.Heights₂.Heights.FieldNumbers
