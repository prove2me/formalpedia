-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.prj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:52.344627+00:00
-- url     : https://prove2.me/submissions/dbcd1928-120e-41ba-91d5-230e7619d3ef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_LaurentWeightBound_laurent_coeff_zero
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_LaurentWeightBound_gt_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
open PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
variable {k : Type} [Field k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
theorem _root_.solution [Infinite k] (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W) (m : ℤ) (y : Fin n → k) (hy : y ∈ W) :
    prj P w m y ∈ W := by
  classical
  by_cases hm : m ∈ Finset.univ.image w
  · rw [← Submodule.Quotient.mk_eq_zero]
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro ℓ
    have key := laurent_coeff_zero (Finset.univ.image w)
      (fun m => ℓ (Submodule.Quotient.mk (p := W) (prj P w m y))) (fun t => by
        have h1 := hinv t y hy
        rw [← Submodule.Quotient.mk_eq_zero, gt_mulVec] at h1
        have h2 : (ℓ ∘ₗ W.mkQ) (∑ m ∈ Finset.univ.image w, ((t ^ m : kˣ) : k) • prj P w m y) = 0 := by
          rw [LinearMap.comp_apply, Submodule.mkQ_apply, h1, map_zero]
        rw [map_sum] at h2
        simpa only [map_smul, LinearMap.comp_apply, Submodule.mkQ_apply, smul_eq_mul] using h2) m hm
    exact key
  · have : prj P w m y = 0 := by
      rw [prj]
      have hc : cut w m (P⁻¹.val *ᵥ y) = 0 := by
        ext i
        simp only [cut, Pi.zero_apply]
        split_ifs with h
        · exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩) hm
        · rfl
      rw [hc, mulVec_zero]
    rw [this]; exact W.zero_mem
end PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
