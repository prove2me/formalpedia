-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.Jm_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:56.082806+00:00
-- url     : https://prove2.me/submissions/18b5c345-99e4-41aa-84f2-45c8fe963827

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_finite_hermIdx
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_int_of_mem_coset
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_eq_sum
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_continuous
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SatakeBound_card_hermIdx
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_irreducible
import Theorems.Thm_GlobalTheory_SplitFlip_exists_isUnif
import Theorems.Thm_GlobalTheory_SplitFlip_haarVol_self
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (n : ℕ) (t : ℕ) :
    Jm n (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) t =
      ∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i : Fin n, ((resCard k : ℂ) ^ (n - 1 - (i : ℕ))) ^ a i := by
  classical
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hfin : ∀ a : Fin n → ℕ, Finite (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) :=
    finite_hermIdx hϖ.irreducible
  let _ : ∀ a : Fin n → ℕ, Fintype (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) := fun a => Fintype.ofFinite _
  have hC : IsClopen {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} :=
    ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hc : Continuous (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin n) (Fin n) k → ℂ)) :=
    (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hC).isLocallyConstant.continuous
  rw [Jm_eq_sum hϖ hc fun x hx => Set.mem_of_indicator_ne_zero hx]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : ∀ c, cosetInt (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1)
      (GlobalTheory.SatakeBound.hermGL hϖ.irreducible a c).val = 1 := fun c => by
    rw [cosetInt, setIntegral_congr_fun isOpen_KO.measurableSet (g := fun _ => (1 : ℂ))]
    · simp [Measure.real, haarVol_self isOpen_KO le_rfl]
    · intro w hw
      have h2 : (GlobalTheory.SatakeBound.hermGL hϖ.irreducible a c).val * w.val ∈
          {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} :=
        int_of_mem_coset hϖ.irreducible (c := c) (g := GlobalTheory.SatakeBound.hermGL hϖ.irreducible a c * w)
          (by simpa using hw)
      exact Set.indicator_of_mem h2 _
  simp only [h1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one,
    GlobalTheory.SatakeBound.card_hermIdx hϖ.irreducible]
  push_cast
  rfl
end PositivityTheory.ThK.SplitLoc.Unr
