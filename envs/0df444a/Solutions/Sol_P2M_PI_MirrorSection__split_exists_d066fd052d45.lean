-- Prove2me | solution 1 for P2M_PI_MirrorSection__split_exists_d066fd052d45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:26.372451+00:00
-- url     : https://prove2.me/submissions/98b9b46f-49f5-4e6d-9179-ddc290aadf8c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Theorems.Thm_P2M_PI_MirrorSection__ut_conjTranspose_65da1bf78ca4
import Theorems.Thm_P2M_PI_MirrorSection__lt_conjTranspose_880787298ed1
import Theorems.Thm_P2M_PI_MirrorSection__isMonomial_conjTranspose_2451b3732e32

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution (hLS : LowSplit) {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsMonomial P) (hPd : IsUnit P.det)
    {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) :
    ∃ a v : Matrix (Fin m) (Fin m) ℂ, a ∈ UTset m ∧ v ∈ UTset m ∧ P * a * P⁻¹ ∈ LTset m ∧
      P * v * P⁻¹ ∈ UTset m ∧ u = a * v := by
  obtain ⟨⟨l₁, l₂⟩, ⟨h1, h2, he⟩, -⟩ := hLS m Pᴴ (isMonomial_conjTranspose hP) uᴴ (ut_conjTranspose hu)
  have key : ∀ l : Matrix (Fin m) (Fin m) ℂ, ((Pᴴ)⁻¹ * l * Pᴴ)ᴴ = P * lᴴ * P⁻¹ := by
    intro l
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
  refine ⟨l₂ᴴ, l₁ᴴ, lt_conjTranspose h2.1, lt_conjTranspose h1.1, ?_, ?_, ?_⟩
  · rw [← key]; exact ut_conjTranspose h2.2
  · rw [← key]; exact lt_conjTranspose h1.2
  · have := congrArg conjTranspose he
    simp only [conjTranspose_conjTranspose, conjTranspose_mul] at this
    exact this
end PI.MirrorSection₂
