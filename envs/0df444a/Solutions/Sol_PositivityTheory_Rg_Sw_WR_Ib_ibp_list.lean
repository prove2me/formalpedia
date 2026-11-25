-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.ibp_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:55.735804+00:00
-- url     : https://prove2.me/submissions/800d2c43-ed64-45fd-8e48-916e88d687f3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_integrable_of_bound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_ibp_dkl
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_contDiff_foldr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (β : E n)
    (hb : ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧
      ∀ y, ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y‖ ≤ h y) (L : List (Fin n × Fin n)) :
    ∫ y, L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y * chr t β y =
      (L.map fun kl => Complex.I * t * herm β kl.1 kl.2).prod * ∫ y, f y * chr t β y := by
  have hI : ∀ L : List (Fin n × Fin n), Integrable (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
    intro L
    obtain ⟨h, hh, hbd⟩ := hb L
    exact integrable_of_bound (contDiff_foldr hf L).continuous hh hbd
  induction L with
  | nil => simp
  | cons kl L ih =>
    have h1 := hI (kl :: L)
    have h2 := hI ((kl.2, kl.1) :: L)
    simp only [List.foldr_cons] at h1 h2 ⊢
    rw [ibp_dkl (contDiff_foldr hf L) (hI L) kl.1 kl.2 h1 h2 t β, ih, List.map_cons, List.prod_cons]
    ring
end PositivityTheory.Rg.Sw.WR.Ib
