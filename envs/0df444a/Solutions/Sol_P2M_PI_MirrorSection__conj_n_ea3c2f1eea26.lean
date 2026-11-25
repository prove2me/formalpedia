-- Prove2me | solution 1 for P2M_PI_MirrorSection__conj_n_ea3c2f1eea26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:57.507585+00:00
-- url     : https://prove2.me/submissions/7c5462bc-942b-47a2-8118-cbb1cf9645d2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Theorems.Thm_P2M_PI_MirrorSection__uh_mul_4992d70a4799
import Theorems.Thm_P2M_PI_MirrorSection__uh_inv_11c75eae1df9
import Theorems.Thm_P2M_PI_MirrorSection__col_eq_524aef35e814
import Theorems.Thm_P2M_PI_MirrorSection__fix_low_6d40825a88fa
import Theorems.Thm_P2M_PI_MirrorSection__uw_inWb_121488a2cc3d
import Theorems.Thm_P2M_PI_MirrorSection__uw_inv_20d23c57ffe1
import Theorems.Thm_P2M_PI_MirrorSection__n_on_Wb_19802610ecc0

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
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {h n : B.Mat k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) :
    h⁻¹ * n * h ∈ Nset k r := by
  have hu := uh_inv hh.1
  have hhi := uw_inv hh
  have hfixi : ∀ b : Fin r, h⁻¹ *ᵥ bvec (eI k r b) = bvec (eI k r b) := fun b => (hhi.2.1 b).1
  refine ⟨uh_mul (uh_mul hu.2.2 hn.1) hh.1, ?_, ?_⟩
  · intro a i hai
    have hcol : (h⁻¹ * n * h) *ᵥ bvec (eI k r a) = n *ᵥ bvec (eI k r a) := by
      rw [← Matrix.mulVec_mulVec, (hh.2.1 a).1, ← Matrix.mulVec_mulVec]
      apply fix_low hfixi le_rfl
      intro l hl
      rw [col_eq]
      simp only
      rw [hn.2.1 a l (by have := a.isLt; omega), if_neg]
      intro h'
      have h2 : l.val = a.val := congrArg Fin.val h'
      have := a.isLt
      omega
    have e := congrFun hcol i
    rw [col_eq, col_eq] at e
    simp only at e
    rw [e]
    exact hn.2.1 a i hai
  · intro i j hj1 hj2 hi
    have hbj : inWb k r (bvec j) := by
      intro l hl
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro h'
      rw [h'] at hl
      omega
    set u := h *ᵥ bvec j with hu_def
    have huW : inWb k r u := uw_inWb hh hbj
    have hd := n_on_Wb hn huW
    have hcol : (h⁻¹ * n * h) *ᵥ bvec j = bvec j + (n *ᵥ u - u) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu_def]
      have : n *ᵥ u = u + (n *ᵥ u - u) := by abel
      rw [this, Matrix.mulVec_add, fix_low hfixi le_rfl _ hd, hu_def, Matrix.mulVec_mulVec, hu.2.1,
        Matrix.one_mulVec]
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hd i hi, add_zero]
    simp [bvec, Pi.single_apply]
end PI.MirrorSection₂
