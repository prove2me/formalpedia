-- Prove2me | solution 1 for PI.StabSplit.nilpotent_orthogonal_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:01.246804+00:00
-- url     : https://prove2.me/submissions/ae4108ed-71ee-4b3a-b740-17b77c741c37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
import Theorems.Thm_PI_StabSplit_UnipW_herm_coord
import Theorems.Thm_PI_StabSplit_UnipW_m_perp
import Theorems.Thm_PI_StabSplit_UnipW_inX_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit
open UnipW
namespace PI.StabSplit
theorem _root_.solution : NPerp := by
  intro k r g hg v hv
  obtain ⟨_, h1, h2⟩ := hg
  have hcol : Formalism.QuantumDeterminants.WeylGroupFacts.col k r g := by
    intro i j hj hji
    by_cases hjr : j.val < r
    · have h3 := h1 ⟨j.val, hjr⟩ i (by show j.val ≤ i.val; omega)
      have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      rw [e] at h3
      exact h3
    · exact h2 i j (by omega) hj (by omega)
  have hperp : UnipW.perpX k r v := by
    intro i hi
    have hir : 2 * r + k - i.val < r := by omega
    have h4 := hv ⟨2 * r + k - i.val, hir⟩
    rw [herm_coord, Finset.sum_eq_single (eI k r ⟨2 * r + k - i.val, hir⟩)] at h4
    · have hs : sig k r (eI k r ⟨2 * r + k - i.val, hir⟩) = i := by
        have hc : (eI k r ⟨2 * r + k - i.val, hir⟩).val < r ∨
            r + k < (eI k r ⟨2 * r + k - i.val, hir⟩).val := Or.inl hir
        unfold sig
        rw [if_pos hc]
        apply Fin.ext
        show 2 * r + k - (2 * r + k - i.val) = i.val
        omega
      have hsg : sgn k r (eI k r ⟨2 * r + k - i.val, hir⟩) = 1 := by
        have hc : ¬ (eI k r ⟨2 * r + k - i.val, hir⟩).val = r + k := by
          show ¬ 2 * r + k - i.val = r + k
          omega
        unfold sgn
        rw [if_neg hc]
      rw [hs, hsg] at h4
      simpa [bvec] using h4
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h5 := m_perp hcol hperp
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact inX_mem h5
end PI.StabSplit
