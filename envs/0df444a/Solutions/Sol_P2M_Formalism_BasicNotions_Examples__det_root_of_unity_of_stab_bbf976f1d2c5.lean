-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__det_root_of_unity_of_stab_bbf976f1d2c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:34.166911+00:00
-- url     : https://prove2.me/submissions/c3e9e654-e6cb-4c7c-97a4-52254c1284c2

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__isIntegral_det_of_stab_256182f483d4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution [StarRing E]
    (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (γ : Matrix (Fin N) (Fin N) E) (hu : γ.det ∈ unitary E) (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : ∃ n : ℕ, 0 < n ∧ γ.det ^ n = 1 := by
  have hint_r := isIntegral_det_of_stab γ L hfg hsp hγ
  have hnorm : ∀ φ : E →+* ℂ, ‖φ γ.det‖ = 1 := by
    intro φ
    have h1 : star γ.det * γ.det = 1 := hu.1
    have h2 : starRingEnd ℂ (φ γ.det) * φ γ.det = 1 := by
      rw [← hstar, ← map_mul, h1, map_one]
    have h4 : Complex.normSq (φ γ.det) = 1 := by
      have h := Complex.normSq_eq_conj_mul_self (z := φ γ.det)
      rw [h2] at h
      exact_mod_cast h
    have h5 : ‖φ γ.det‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact h4
    nlinarith [norm_nonneg (φ γ.det)]
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := E) (A := ℂ) hint_r hnorm
  exact ⟨n, hn, h⟩
end Formalism.BasicNotions.Examples₂
