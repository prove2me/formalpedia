-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_HilbertIncrement_closed_4d09085c2c1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:29.155966+00:00
-- url     : https://prove2.me/submissions/f94e7c63-c5ac-4bfd-bc7d-501583b58385

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_ringKrullDim_quot_add_one_le_978fb20ae9e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_le_of_add_one_le_natCast_add_one_6b5626c06405
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_colon_span_singleton_eq_of_not_mem_585d56ee6b6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_closed_52aa7c2563e1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
namespace HilbertIncrement
theorem _root_.solution : HilbertIncrement.Statement.{u} := by
  intro F _ K _ _ ι _ d q b i hq hdim hd hX
  have : q.IsPrime := hq.isPrime
  refine ⟨fun a => ?_, fun W _ hle => ?_⟩
  · have hhom : IsMultiHomog (X ⟨b, i⟩ : MRing ι F) (Pi.single b 1) :=
      isWeightedHomogeneous_X F (blockWeight ι) ⟨b, i⟩
    have h := HilbExactDivide.closed F K ι q hq.multiHomog (Pi.single b 1) (X ⟨b, i⟩) hhom a
    have hcast : (a - fun k => (((Pi.single b 1 : K → ℕ) k : ℕ) : ℤ)) = a - Pi.single b 1 := by
      funext k
      by_cases hk : k = b
      · subst hk
        simp
      · simp [Pi.single_apply, hk]
    rwa [colon_span_singleton_eq_of_not_mem hX, hcast] at h
  · have hXW : (X ⟨b, i⟩ : MRing ι F) ∈ W :=
      hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hstep := ringKrullDim_quot_add_one_le (le_sup_left.trans hle) hX hXW
    rw [hdim] at hstep
    have hn : d + Fintype.card K = (d - 1 + Fintype.card K) + 1 := by omega
    rw [hn] at hstep
    exact le_of_add_one_le_natCast_add_one hstep
end HilbertIncrement
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
