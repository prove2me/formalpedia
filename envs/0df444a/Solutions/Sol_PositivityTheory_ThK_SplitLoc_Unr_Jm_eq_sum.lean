-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.Jm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:59.363007+00:00
-- url     : https://prove2.me/submissions/1d6ba319-0e8f-4403-bb73-59938117eddc

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_exists_hermGL
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_ord_gdet_of_mem_coset
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_int_of_mem_coset
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_eq_inter
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_setIntegral_coset
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SatakeBound_hermGL_injective
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_irreducible
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
open GlobalTheory.SatakeBound
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : Continuous φ)
    (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) [∀ a : Fin n → ℕ, Fintype (HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a)] (t : ℕ) :
    Jm n φ t = ∑ a ∈ Finset.piAntidiag Finset.univ t, ∑ c, cosetInt φ (hermGL hϖ.irreducible a c).val := by
  classical
  have hU : dShell n t ∩ {g : GL (Fin n) k | ∀ i j, g.val i j ∈ 𝒪[k]} =
      ⋃ x ∈ (Finset.piAntidiag Finset.univ t).sigma fun a => (Finset.univ : Finset (HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a)),
        {g | (hermGL hϖ.irreducible x.1 x.2)⁻¹ * g ∈ KO k (Fin n)} := by
    ext g
    simp only [Set.mem_iUnion, Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
      Set.mem_ofPred_eq, Set.mem_inter_iff, dShell, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a, c, h⟩ := exists_hermGL hϖ.irreducible h2
      exact ⟨⟨a, c⟩, by exact_mod_cast (ord_gdet_of_mem_coset hϖ h).symm.trans h1, h⟩
    · rintro ⟨⟨a, c⟩, h1, h⟩
      exact ⟨(ord_gdet_of_mem_coset hϖ h).trans (congrArg Nat.cast h1), int_of_mem_coset _ h⟩
  rw [Jm_eq_inter hs, hU, integral_biUnion_finset, Finset.sum_sigma]
  · simp only [setIntegral_coset]
  · exact fun x _ => (isOpen_KO.preimage (continuous_const_mul _)).measurableSet
  · intro x _ y _ hxy
    refine Set.disjoint_left.2 fun g h1 h2 => hxy (hermGL_injective hϖ.irreducible ?_)
    exact (QuotientGroup.eq.2 h1).trans (QuotientGroup.eq.2 h2).symm
  · intro x _
    have hc : IsCompact {g | (hermGL hϖ.irreducible x.1 x.2)⁻¹ * g ∈ KO k (Fin n)} :=
      (Homeomorph.mulLeft (hermGL hϖ.irreducible x.1 x.2)⁻¹).isCompact_preimage.2 isCompact_KO
    exact (hφ.comp Units.continuous_val).continuousOn.integrableOn_compact hc
end PositivityTheory.ThK.SplitLoc.Unr
