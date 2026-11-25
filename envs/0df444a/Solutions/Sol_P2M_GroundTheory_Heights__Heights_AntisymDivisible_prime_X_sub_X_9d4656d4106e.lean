-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_prime_X_sub_X_9d4656d4106e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:18.101525+00:00
-- url     : https://prove2.me/submissions/ffa6c834-5a3b-4b20-ad0c-1052bfd7ed53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_sub_rename_collapse_mem_70f922bc8132

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
theorem _root_.solution {u v : σ} (huv : u ≠ v) : Prime (X u - X v : MvPolynomial σ ℝ) := by
  have hne : (X u - X v : MvPolynomial σ ℝ) ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => huv (X_injective h)
  rw [← Ideal.span_singleton_prime hne]
  have : Ideal.span {(X u - X v : MvPolynomial σ ℝ)} =
      RingHom.ker (rename (R := ℝ) (collapse u v)) := by
    ext P
    constructor
    · intro hP
      obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.1 hP
      rw [RingHom.mem_ker]
      simp [collapse]
    · intro hP
      rw [RingHom.mem_ker] at hP
      have := sub_rename_collapse_mem u v P
      rwa [hP, sub_zero] at this
  rw [this]
  exact RingHom.ker_isPrime _
end GroundTheory.Heights₂.Heights.AntisymDivisible
