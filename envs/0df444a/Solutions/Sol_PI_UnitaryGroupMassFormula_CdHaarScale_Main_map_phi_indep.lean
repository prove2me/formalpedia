-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.map_phi_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:06.477078+00:00
-- url     : https://prove2.me/submissions/cb689c0d-7f2a-4160-9058-6348985f6d5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_umat_phi
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_umat_rho
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_umat_injective
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_rho_finite_order
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_map_eq_self_of_iterate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution {P Q n : ℕ} {ε : Fin n → Bool} (e e' : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (h1' : ∀ i, ε (e' (Sum.inl i)) = true) (h2' : ∀ j, ε (e' (Sum.inr j)) = false)
    (μ : Measure (Formalism.BasicNotions.UpqT P Q)) [μ.IsHaarMeasure] :
    μ.map (phi e' h1' h2') = μ.map (phi e h1 h2) := by
  set π : Fin n ≃ Fin n := e.symm.trans e' with hπdef
  have hπ : ∀ i, ε (π i) = ε i := by
    intro i
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | a <;> simp [hπdef, h1, h2, h1', h2']
  have hcomp : ⇑(phi e' h1' h2') = ⇑(rho π hπ) ∘ ⇑(phi e h1 h2) := by
    funext g
    apply umat_injective
    rw [Function.comp_apply, umat_rho, umat_phi, umat_phi]
    ext i j
    simp [hπdef, Matrix.reindex_apply]
  obtain ⟨N, hN, hN'⟩ := rho_finite_order π hπ
  have hmr : Measurable ⇑(rho π hπ) := (rho π hπ).continuous.measurable
  have hmp : Measurable ⇑(phi e h1 h2) := (phi e h1 h2).continuous.measurable
  rw [hcomp, ← Measure.map_map hmr hmp]
  exact map_eq_self_of_iterate _ (rho π hπ) N hN hN'
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
