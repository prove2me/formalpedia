-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.Q_perp_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:46:03.689826+00:00
-- url     : https://prove2.me/submissions/99f9c7e4-05e1-45e5-8297-18b813f70a7d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_add_right
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_smul_right
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_sub_right
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_sum_right
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_smul_left
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
variable {r : ℕ}
private theorem Q_eq_hform_expansion (e f : Fin r → n → A) (z y w : n → A) :
    Formalism.UG.hform σ J w (Q σ J e f z y) =
      -Formalism.UG.hform σ J z z * (Formalism.UG.hform σ J w y - ∑ a, (Formalism.UG.hform σ J (f a) y * Formalism.UG.hform σ J w (e a) +
        Formalism.UG.hform σ J (e a) y * Formalism.UG.hform σ J w (f a))) + Formalism.UG.hform σ J z y * Formalism.UG.hform σ J w z := by
  simp only [Q, h_add_right, h_smul_right, h_sub_right, h_sum_right]
end PI.UnitaryDimensionFormula.FrameAlg
end

set_option autoImplicit false
open Matrix
open PI PI.UnitaryDimensionFormula PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
variable {r : ℕ}
namespace PI.UnitaryDimensionFormula.FrameAlg
theorem _root_.solution (hJ : Formalism.UG.cT σ J = J) (hσ : ∀ a, σ (σ a) = a) {e f : Fin r → n → A} {z : n → A} (E₁ : A)
    (hE : E₁ * E₁ = E₁) (hEs : σ E₁ = E₁) (he : ∀ a, e a = E₁ • e a) (hf : ∀ a, f a = E₁ • f a)
    (hee : ∀ a b, Formalism.UG.hform σ J (e a) (e b) = 0) (hff : ∀ a b, Formalism.UG.hform σ J (f a) (f b) = 0)
    (hef : ∀ a b, Formalism.UG.hform σ J (e a) (f b) = if a = b then E₁ else 0)
    (hez : ∀ a, Formalism.UG.hform σ J (e a) z = 0) (hfz : ∀ a, Formalism.UG.hform σ J (f a) z = 0) (y : n → A) :
    (∀ b, Formalism.UG.hform σ J (e b) (Q σ J e f z y) = 0) ∧ (∀ b, Formalism.UG.hform σ J (f b) (Q σ J e f z y) = 0) ∧
      Formalism.UG.hform σ J z (Q σ J e f z y) = 0 := by
  have hfe : ∀ a b, Formalism.UG.hform σ J (f b) (e a) = if a = b then E₁ else 0 := fun a b => by
    rw [h_symm σ J hJ hσ (e a) (f b), hef]; split_ifs <;> simp [hEs]
  have hze : ∀ a, Formalism.UG.hform σ J z (e a) = 0 := fun a => by rw [h_symm σ J hJ hσ (e a) z, hez, map_zero]
  have hzf : ∀ a, Formalism.UG.hform σ J z (f a) = 0 := fun a => by rw [h_symm σ J hJ hσ (f a) z, hfz, map_zero]
  have hEe : ∀ b, Formalism.UG.hform σ J (e b) y = Formalism.UG.hform σ J (e b) y * E₁ := fun b => by
    conv_lhs => rw [he b, h_smul_left, hEs]
    ring
  have hEf : ∀ b, Formalism.UG.hform σ J (f b) y = Formalism.UG.hform σ J (f b) y * E₁ := fun b => by
    conv_lhs => rw [hf b, h_smul_left, hEs]
    ring
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩ <;> rw [Q_eq_hform_expansion]
  · simp [hee, hef, hez]
    rw [← hEe b]; ring
  · simp [hfe, hff, hfz]
    rw [← hEf b]; ring
  · simp [hze, hzf]; ring
end PI.UnitaryDimensionFormula.FrameAlg
