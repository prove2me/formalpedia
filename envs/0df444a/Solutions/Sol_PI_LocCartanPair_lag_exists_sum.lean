-- Prove2me | solution 1 for PI.LocCartanPair.lag_exists_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:04.988992+00:00
-- url     : https://prove2.me/submissions/0c5db144-b343-4514-ad5d-1767bb2ca7ec

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
import Theorems.Thm_PI_LocCartanPair_lag_congr
import Theorems.Thm_PI_LocCartanPair_hypJ_herm
import Theorems.Thm_PI_LocCartanPair_hypJ_det
import Theorems.Thm_PI_LocCartanPair_hypE_idem
import Theorems.Thm_PI_LocCartanPair_hypE_lag
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
  [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
namespace PI.LocCartanPair
theorem _root_.solution (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (hA : Aᴴ = A)
    (hdet : IsUnit A.det) :
    ∃ e : Matrix (κ ⊕ κ) (κ ⊕ κ) R, e * e = e ∧ eᴴ * A = A * (1 - e) := by
  obtain ⟨g, hg, hgA⟩ := Formalism.HermitianLatticesTheory.unimodUnramUnique_main hR₀ hθ _ (κ ⊕ κ) rfl A hA hdet
  obtain ⟨c, hc, hcJ⟩ := Formalism.HermitianLatticesTheory.unimodUnramUnique_main hR₀ hθ _ (κ ⊕ κ) rfl
    (hypJ κ) (hypJ_herm κ) (hypJ_det κ)
  have hc1 : c * c⁻¹ = 1 := mul_nonsing_inv c hc
  have hc2 : (c⁻¹)ᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, hc1, conjTranspose_one]
  have hcX : ∀ X : Matrix (κ ⊕ κ) (κ ⊕ κ) R, (c⁻¹)ᴴ * (cᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hc2, Matrix.one_mul]
  have hP : IsUnit (g * c⁻¹).det := by
    rw [det_mul]; exact hg.mul (isUnit_nonsing_inv_det c hc)
  have hPA : (g * c⁻¹)ᴴ * A * (g * c⁻¹) = hypJ κ := by
    calc (g * c⁻¹)ᴴ * A * (g * c⁻¹) = (c⁻¹)ᴴ * (gᴴ * A * g) * c⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (c⁻¹)ᴴ * (cᴴ * hypJ κ * c) * c⁻¹ := by rw [hgA, hcJ]
      _ = hypJ κ := by simp only [Matrix.mul_assoc, hc1, Matrix.mul_one, hcX]
  exact ⟨_, lag_congr A (hypJ κ) (g * c⁻¹) (hypE κ) hP hPA (hypE_idem κ) (hypE_lag κ)⟩
end PI.LocCartanPair
