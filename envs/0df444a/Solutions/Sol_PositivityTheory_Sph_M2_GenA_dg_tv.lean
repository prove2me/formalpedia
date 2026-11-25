-- Prove2me | solution 1 for PositivityTheory.Sph.M2.GenA.dg_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:57.944201+00:00
-- url     : https://prove2.me/submissions/ad04dcad-18aa-47b0-98f7-fd96473228b7

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_dg_val
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_tv_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph PositivityTheory.Sph.M2 PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace PositivityTheory.Sph.M2.GenA
theorem _root_.solution {i j : n} (h : i ≠ j) (d : Kˣ) (s : K) :
    dg (Function.update 1 i d) * tv h s = tv h (d * s) * dg (Function.update 1 i d) := by
  ext a b
  rw [Units.val_mul, Units.val_mul, dg_val, tv_val, tv_val, diagonal_mul, mul_diagonal]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, of_apply]
  by_cases h1 : a = b
  · subst h1
    have : ¬ (i = a ∧ j = a) := fun e => h (e.1.trans e.2.symm)
    simp [this]
  · by_cases h2 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h1, Function.update_of_ne (Ne.symm h)]
    · simp [h1, h2]
end PositivityTheory.Sph.M2.GenA
