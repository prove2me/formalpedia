-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_maDens_cons_of_hessC_eq_smul_1613fdd029d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:31.343785+00:00
-- url     : https://prove2.me/submissions/435c8b29-d840-4e54-9d68-27f333e75ea1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCutHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {D : ℕ} (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) (c : ℝ)
    (h : hessC f y = (c : ℂ) • hessC g y) :
    maDens (Fin.cons f ψ) y = c * maDens (Fin.cons g ψ) y := by
  have e : ∀ u : (Fin (D + 1) → ℂ) → ℝ,
      (fun k => hessC ((Fin.cons u ψ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ) k) y) =
        Fin.cons (hessC u y) (fun k => hessC (ψ k) y) := fun u => by
    funext k; exact Fin.cases rfl (fun i => rfl) k
  have hm := mdisc_update_smul
    (Fin.cons (hessC g y) (fun k => hessC (ψ k) y) : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    0 (c : ℂ) (hessC g y)
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at hm
  unfold maDens
  rw [e, e, h, hm, Complex.re_ofReal_mul]
  ring
end GroundTheory.Heights₂.Heights
