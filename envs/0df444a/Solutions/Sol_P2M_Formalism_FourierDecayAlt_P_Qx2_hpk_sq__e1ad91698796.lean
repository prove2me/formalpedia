-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:39.176278+00:00
-- url     : https://prove2.me/submissions/30148eec-efec-42d7-af56-8569c0a694c6

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution : Hpk k r * Hpk k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hm : r ≤ a.val ∧ a.val ≤ r + k
  · rw [Finset.sum_eq_single a]
    · by_cases hab : a = b
      · subst hab
        rw [if_pos rfl]
        simp only [Hpk, eq_self_iff_true, and_true]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
      · rw [if_neg hab]
        have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
        simp only [Hpk]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
    · intro c _ hc
      have hc' : c.val ≠ a.val := fun e => hc (Fin.ext e)
      simp only [Hpk]
      split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin (2 * r + k + 1), c₀.val = 2 * r + k - a.val :=
      ⟨⟨2 * r + k - a.val, by omega⟩, rfl⟩
    rw [Finset.sum_eq_single c₀]
    · by_cases hab : a = b
      · subst hab
        rw [if_pos rfl]
        simp only [Hpk, eq_self_iff_true, and_true]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
      · rw [if_neg hab]
        have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
        simp only [Hpk]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
    · intro c _ hc
      have hc' : c.val ≠ c₀.val := fun e => hc (Fin.ext e)
      simp only [Hpk]
      split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
    · intro h
      exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.Qx2
