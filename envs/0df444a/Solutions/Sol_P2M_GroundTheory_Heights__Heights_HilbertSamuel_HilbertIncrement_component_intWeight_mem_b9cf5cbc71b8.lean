-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_component_intWeight_mem_b9cf5cbc71b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:03.626337+00:00
-- url     : https://prove2.me/submissions/7aadeca6-db90-47ac-a5bd-0d6e1e826200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_weight_intWeight_8853f7eb7b24

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
theorem _root_.solution {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    {f : MRing ι F} (hf : f ∈ J) (m : K → ℤ) :
    weightedHomogeneousComponent (intWeight (ι := ι)) m f ∈ J := by
  classical
  by_cases hm : ∀ k, 0 ≤ m k
  · have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f =
        weightedHomogeneousComponent (blockWeight ι) (fun k => (m k).toNat) f := by
      ext e
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_intWeight]
      have hiff : ((fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ)) = m) ↔
          Finsupp.weight (blockWeight ι) e = fun k => (m k).toNat := by
        constructor
        · intro h
          funext k
          have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
          have := hm k
          show _ = (m k).toNat
          omega
        · intro h
          funext k
          have e1 : Finsupp.weight (blockWeight ι) e k = (m k).toNat := congrFun h k
          have := hm k
          show ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k
          omega
      simp only [hiff]
    rw [e]
    exact hJ f hf _
  · push Not at hm
    obtain ⟨k, hk⟩ := hm
    have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f = 0 := by
      ext e
      rw [coeff_weightedHomogeneousComponent, weight_intWeight, coeff_zero, if_neg]
      intro h
      have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
      omega
    rw [e]
    exact J.zero_mem
end GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
