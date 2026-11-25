-- Prove2me | solution 1 for P2M_GlobalTheory_PDivGroup_conv_eq_one_of_forall_pairing__b1a5d38aac2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:14.586643+00:00
-- url     : https://prove2.me/submissions/468c5d71-0f2f-4c5d-9b98-2533f1054bfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_TateFree_eq_of_forall_pts
import Theorems.Thm_GlobalTheory_PDivGroup_tateLevel_apply
import Theorems.Thm_GlobalTheory_PDivGroup_pt_surjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT


attribute [local simp] GlobalTheory.PDivGroup.tateLevel_apply

set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (t : G.Tate) (n : ℕ)
    (h : ∀ χ : G.dual.Tate, muRoot (pairing G O t χ) n = 1) : t.conv n = 1 := by
  have h1 : (toConv (t.pt n).toLinearMap : CartierDual O (G.A n)) =
      toConv ((0 : G.Tate).pt n).toLinearMap := eq_of_forall_pts O C (G.dual.A n) fun x => by
    obtain ⟨χ, rfl⟩ := G.dual.pt_surjective C n x
    refine (apply_charElem χ n _).symm.trans (Eq.trans ?_ (apply_charElem χ n _))
    change t.pt n (charElem χ n) = (0 : G.Tate).pt n (charElem χ n)
    rw [← muRoot_pairing, ← muRoot_pairing, h, map_zero, LinearMap.zero_apply, muRoot_zero]
  exact ofConv_injective <| AlgHom.ext fun a => LinearMap.congr_fun (congrArg ofConv h1) a
end GlobalTheory.PDivGroup
