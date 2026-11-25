-- Prove2me | solution 1 for P2M_PI_MirrorSection__n_mul_f9b46a5d1768
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:45:07.74531+00:00
-- url     : https://prove2.me/submissions/e8316e5a-5b10-42d4-a326-dbb9251686e4

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Theorems.Thm_P2M_PI_MirrorSection__uh_mul_4992d70a4799
import Theorems.Thm_P2M_PI_MirrorSection__col_eq_524aef35e814
import Theorems.Thm_P2M_PI_MirrorSection__maps_low_ff5c1839ec93

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
theorem _root_.solution {n m : B.Mat k r} (hn : n ∈ Nset k r) (hm : m ∈ Nset k r) : n * m ∈ Nset k r := by
  refine ⟨uh_mul hn.1 hm.1, ?_, ?_⟩
  · intro a i hai
    have hy : m *ᵥ bvec (eI k r a) - bvec (eI k r a) ∈ lowS k r a.val := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hm.2.1 a l hl]
      simp [bvec, Pi.single_apply]
    have hmaps := maps_low hn.2.1 (a := a.val) a.isLt.le
    have hcol : (n * m) *ᵥ bvec (eI k r a) =
        n *ᵥ bvec (eI k r a) + n *ᵥ (m *ᵥ bvec (eI k r a) - bvec (eI k r a)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
      congr 1
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hmaps _ hy i hai, add_zero, col_eq]
    exact hn.2.1 a i hai
  · intro i j hj1 hj2 hi
    have hy : m *ᵥ bvec j - bvec j ∈ lowS k r r := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hm.2.2 l j hj1 hj2 hl]
      simp [bvec, Pi.single_apply]
    have hmaps := maps_low hn.2.1 (a := r) le_rfl
    have hcol : (n * m) *ᵥ bvec j = n *ᵥ bvec j + n *ᵥ (m *ᵥ bvec j - bvec j) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
      congr 1
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hmaps _ hy i hi, add_zero, col_eq]
    exact hn.2.2 i j hj1 hj2 hi
end PI.MirrorSection₂
