-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.formFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:10.023831+00:00
-- url     : https://prove2.me/submissions/44ec8b54-10bf-4053-8ebf-d5de3586a6f4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_fform_eq_gf
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_step
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_KopL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_box_stable
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_symW_step
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_symK_hlin
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_symK_tr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_der_adj
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_adj
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_herm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_sub_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_sub_right
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_sum_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open CoreC CoreC.G
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution : FormFacts := by
  intro m n ε c hc
  have hw : ∀ (s : Fin m × Fin n × Bool →₀ ℕ) k, (fun s => (wt c s : ℂ)) (Finsupp.single k 1 + s) =
      ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (fun s => (wt c s : ℂ)) s := fun s k => wt_step c s k
  have hst : ∀ s : Fin m × Fin n × Bool →₀ ℕ, star ((fun s => (wt c s : ℂ)) s) = (fun s => (wt c s : ℂ)) s :=
    fun s => Complex.conj_ofReal _
  have hpos : ∀ s : Fin m × Fin n × Bool →₀ ℕ, 0 < ((fun s => (wt c s : ℂ)) s).re := fun s => by
    simpa using wt_pos hc s
  refine ⟨fun p q => gf_herm _ hst p q, fun p hp => gf_pos _ hst hpos p hp, fun i j p q => ?_,
    fun i j R f hf => box_stable ε i j R f hf, fun i j s t => ⟨by simp [fform], ?_⟩⟩
  · rw [fform_eq_gf, fform_eq_gf, KopL_apply, KopL_apply, gf_sub_left, gf_sub_right, gf_sum_left, gf_sum_left,
      gf_sum_right, gf_sum_right]
    congr 1 <;> exact Finset.sum_congr rfl fun a _ => gf_adj _ hw _ _ _ _
  · exact der_adj (w := symW) 1 symW_step (symK ε i j) (symK ε j i) (symK_hlin ε i j) (symK_hlin ε j i)
      (symK_tr ε i j) s t
end PositivityTheory.Rg.Sw.LC
