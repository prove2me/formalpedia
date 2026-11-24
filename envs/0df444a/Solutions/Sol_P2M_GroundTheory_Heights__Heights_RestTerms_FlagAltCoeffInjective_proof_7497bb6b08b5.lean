-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagAltCoeffInjective_proof_7497bb6b08b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:11.423502+00:00
-- url     : https://prove2.me/submissions/f5dc2ccf-a4b5-49a9-bdcb-4f14cecd97b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagAltCoeffInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagAltCoeffInjective
theorem _root_.solution (h1 : FlagCoeffBlockPermute.Statement) :
    FlagAltCoeffInjective.Statement := by
  classical
  intro f N P α hP hc τ i j hij
  simp only at hij
  by_contra hne
  let w : Fin f → Equiv.Perm (Fin N) := Function.update 1 τ (Equiv.swap i j)
  have hsign : blockSign f N w = -1 := by
    unfold blockSign
    rw [Finset.prod_eq_single τ]
    · simp [w, Equiv.Perm.sign_swap hne]
    · intro b _ hb
      simp [w, Function.update_of_ne hb]
    · simp
  have hα : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α := by
    ext ⟨σ, k⟩
    change α (σ, w σ k) = α (σ, k)
    by_cases hσ : σ = τ
    · subst hσ
      simp only [w, Function.update_self]
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left]; exact hij.symm
      · rcases eq_or_ne k j with rfl | hkj
        · rw [Equiv.swap_apply_right]; exact hij
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    · simp [w, Function.update_of_ne hσ]
  have key := h1 f N w P α
  rw [hα, hP w, hsign, coeff_smul] at key
  have : coeff α P = 0 := by
    have h2 : (2 : ℚ) * coeff α P = 0 := by
      rw [smul_eq_mul] at key
      linarith
    simpa using h2
  exact hc this
end FlagAltCoeffInjective
end GroundTheory.Heights₂.Heights.RestTerms
