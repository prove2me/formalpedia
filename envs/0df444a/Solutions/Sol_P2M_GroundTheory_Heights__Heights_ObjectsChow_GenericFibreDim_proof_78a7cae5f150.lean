-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_proof_78a7cae5f150
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:06:32.358625+00:00
-- url     : https://prove2.me/submissions/5363b56f-4f51-4366-a67b-1dfa1ba81ae8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_finIdeal_eq_comap_eead2ee5270f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_ringKrullDim_quot_finIdeal_f12def14930b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_eq_natCast_of_add_one_eq_8a51e7536497
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
open GenericFibreDim
namespace GroundTheory.Heights₂.Heights.ObjectsChow
namespace GenericFibreDim
theorem _root_.solution : GenericFibreDim.Statement := by
  intro n d P hP
  obtain ⟨-, ⟨hPp, -, -⟩, hhor, hdim⟩ := hP
  set P' := IndefiniteRowSideFullHecke.ArithBezout.finIdeal P with hP'
  have hP'p : P'.IsPrime := by
    rw [hP', finIdeal_eq_comap]
    exact Ideal.comap_isPrime _ _
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Fin n) ℤ) ∈ P' → m = 0 := by
    intro m hm
    rw [hP', finIdeal_eq_comap, Ideal.mem_comap] at hm
    have hm' : (blkRingEquiv n) (C m) = C m := by
      simp [blkRingEquiv]
    rw [hm'] at hm
    have : m ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := hm
    rw [show P.comap (C : ℤ →+* MRing (PBlk n)) = ⊥ from hhor, Ideal.mem_bot] at this
    exact this
  obtain ⟨-, -, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P' hchar
  have hgen : genericIdeal P = ReciprocityTheory.AnForm.R.extQ P' := rfl
  rw [hP', ringKrullDim_quot_finIdeal, hdim] at hform
  rw [hgen]
  simp only [Fintype.card_unit] at hform
  exact eq_natCast_of_add_one_eq d _ hform
end GenericFibreDim
end GroundTheory.Heights₂.Heights.ObjectsChow
