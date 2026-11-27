-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_NormalFormRelations_vander__fab4b06acbc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:52.539913+00:00
-- url     : https://prove2.me/submissions/88301fb2-e427-4fde-a34b-ad65589d54ea

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_JacobiDiagonalBounds_Vander

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NormalFormRelations
namespace Formalism.FourierDecayAlt.P.NormalFormRelations
theorem _root_.solution (Q : ℕ) : ∃ lam : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ (E : Type) [AddCommGroup E] [Module ℂ E]
    (a : Fin (Q + 1) → E) (q : Fin (Q + 1)),
    a q = ∑ s : Fin (Q + 1), lam q s • ∑ j : Fin (Q + 1), (((s : ℕ) : ℂ) ^ (j : ℕ)) • a j := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ,
      V = Matrix.vandermonde fun s => ((s : ℕ) : ℂ) := ⟨_, rfl⟩
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    simpa [Fin.ext_iff] using hij
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  refine ⟨fun q s => (V⁻¹ : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q s, fun E _ _ a q => ?_⟩
  beta_reduce
  have hrow : ∀ j : Fin (Q + 1),
      ∑ s : Fin (Q + 1), V⁻¹ q s * ((s : ℕ) : ℂ) ^ (j : ℕ) = (1 : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q j := by
    intro j
    rw [← hinv, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [hV, Matrix.vandermonde_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp
end Formalism.FourierDecayAlt.P.NormalFormRelations
