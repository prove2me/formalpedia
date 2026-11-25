-- Prove2me | solution 1 for P2M_PI_MirrorSection__n_inv_2b0268f7044c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:21.605577+00:00
-- url     : https://prove2.me/submissions/aae93196-cfe8-4bd8-ae78-d30f8ae9171e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Theorems.Thm_P2M_PI_MirrorSection__uh_inv_11c75eae1df9
import Theorems.Thm_P2M_PI_MirrorSection__col_eq_524aef35e814
import Theorems.Thm_P2M_PI_MirrorSection__maps_low_ff5c1839ec93
import Theorems.Thm_P2M_PI_MirrorSection__onto_low_16ac7e56a491

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
theorem _root_.solution {n : B.Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Nset k r := by
  have hu := uh_inv hn.1
  have hC1 := hn.2.1
  refine ⟨hu.2.2, ?_, ?_⟩
  · intro a i hai
    have hmaps := maps_low hC1 (a := a.val) a.isLt.le
    have hy : bvec (eI k r a) - n *ᵥ bvec (eI k r a) ∈ lowS k r a.val := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hC1 a l hl]
      simp [bvec, Pi.single_apply]
    obtain ⟨x, hx, hgx⟩ := onto_low hu.2.1 hmaps _ hy
    have hx2 : n *ᵥ (x + bvec (eI k r a)) = bvec (eI k r a) := by
      rw [Matrix.mulVec_add, hgx]
      abel
    have hx3 : n⁻¹ *ᵥ bvec (eI k r a) = x + bvec (eI k r a) := by
      rw [← hx2, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec, hx2]
    have e := congrFun hx3 i
    rw [col_eq] at e
    simp only at e
    rw [e]
    simp only [Pi.add_apply]
    rw [hx i hai, zero_add]
    simp [bvec, Pi.single_apply]
  · intro i j hj1 hj2 hi
    have hmaps := maps_low hC1 (a := r) le_rfl
    have hy : bvec j - n *ᵥ bvec j ∈ lowS k r r := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hn.2.2 l j hj1 hj2 hl]
      simp [bvec, Pi.single_apply]
    obtain ⟨x, hx, hgx⟩ := onto_low hu.2.1 hmaps _ hy
    have hx2 : n *ᵥ (x + bvec j) = bvec j := by
      rw [Matrix.mulVec_add, hgx]
      abel
    have hx3 : n⁻¹ *ᵥ bvec j = x + bvec j := by
      rw [← hx2, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec, hx2]
    have e := congrFun hx3 i
    rw [col_eq] at e
    simp only at e
    rw [e]
    simp only [Pi.add_apply]
    rw [hx i hi, zero_add]
    simp [bvec, Pi.single_apply]
end PI.MirrorSection₂
