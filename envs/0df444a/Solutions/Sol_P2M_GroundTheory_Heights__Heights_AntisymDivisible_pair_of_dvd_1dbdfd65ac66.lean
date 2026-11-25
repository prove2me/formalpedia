-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_pair_of_dvd_1dbdfd65ac66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:09.172841+00:00
-- url     : https://prove2.me/submissions/4e8b6fed-f784-4e31-a63b-8881546e8d45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution {u v u' v' : σ} (h' : u' ≠ v')
    (hd : (X u - X v : MvPolynomial σ ℝ) ∣ X u' - X v') :
    (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
  obtain ⟨Q, hQ⟩ := hd
  have h1 := congrArg (rename (R := ℝ) (collapse u v)) hQ
  simp only [map_sub, map_mul, rename_X, collapse, ↓reduceIte, ite_self, sub_self, zero_mul,
    sub_eq_zero] at h1
  have h2 := X_injective h1
  split_ifs at h2 with ha hb hb
  · exact absurd (ha.trans hb.symm) h'
  · exact Or.inl ⟨ha, h2.symm⟩
  · exact Or.inr ⟨h2, hb⟩
  · exact absurd h2 h'
end GroundTheory.Heights₂.Heights.AntisymDivisible
