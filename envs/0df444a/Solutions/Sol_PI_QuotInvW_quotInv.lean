-- Prove2me | solution 1 for PI.QuotInvW.quotInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:05.12249+00:00
-- url     : https://prove2.me/submissions/9a0a51e0-5154-40d6-90fe-2271634a8371

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
import Theorems.Thm_PI_QuotInvW_ineq
import Theorems.Thm_PI_QuotInvW_measurable_mm_left
import Theorems.Thm_PI_QuotInvW_mm_assoc
import Theorems.Thm_PI_QuotInvW_mm_mem
import Theorems.Thm_PI_QuotInvW_mm_oneM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
namespace PI.QuotInvW
theorem _root_.solution : PI.QuotInv := by
  intro m G S μG μS ν h F hF hFi g0 hg0
  obtain ⟨g, rfl⟩ : ∃ g : MtM m, Matrix.of g = g0 := ⟨Matrix.of.symm g0, rfl⟩
  have hg : Matrix.of g ∈ G := hg0
  have hFi' : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x :=
    fun s hs x hx => hFi s hs x hx
  have h1 : ∫⁻ x, F (mm x g) ∂ν ≤ ∫⁻ x, F x ∂ν := ineq h hF hFi' (g := g) hg
  obtain ⟨hginvG, hgg⟩ := h.1.2.2.2 _ hg
  have hdet : IsUnit (Matrix.of g).det :=
    isUnit_iff_exists_inv.2 ⟨(Matrix.of g)⁻¹.det, by rw [← Matrix.det_mul, hgg, Matrix.det_one]⟩
  have hgig : mm (minv g) g = oneM := by
    have := Matrix.nonsing_inv_mul (Matrix.of g) hdet
    funext i j; exact congrFun (congrFun this i) j
  have h2 : ∫⁻ x, F (mm (mm x (minv g)) g) ∂ν ≤ ∫⁻ x, F (mm x g) ∂ν :=
    ineq h (F := fun x => F (mm x g)) (hF.comp (measurable_mm_left g))
      (by
        intro s hs x hx
        rw [mm_assoc]
        exact hFi' s hs _ (mm_mem h.1 hx hg))
      (g := minv g) hginvG
  simp only [mm_assoc, hgig, mm_oneM] at h2
  exact le_antisymm h1 h2
end PI.QuotInvW
