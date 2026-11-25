-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_cons_add_83d8ed79e032
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:32.326863+00:00
-- url     : https://prove2.me/submissions/cb36998b-35fc-49e6-b208-62e82b5e496d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
theorem _root_.solution (hadd : FieldNumbers.IntNumAdd.Statement.{0}) (F : Type) [Field F]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F P ((c + c') :: l) = intNumL F P (c :: l) + intNumL F P (c' :: l) := by
  have key : ∀ d, Function.update (c :: l).get (0 : Fin (l.length + 1)) d = (d :: l).get := by
    intro d
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := hadd F K ι P hP.multiHomog hP.relevant (l.length + 1) hd ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
