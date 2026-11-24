-- Prove2me | solution 1 for PI.StabSplit.UnipW.herm_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:11:44.873018+00:00
-- url     : https://prove2.me/submissions/c413ca48-7a75-4bee-8c18-3fe0a8496fbc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
namespace PI.StabSplit.UnipW
private lemma hpk_apply_of_outer_index (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  by_cases hi : i.val < r ∨ r + k < i.val
  · have hsig : sig k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold sig
      rw [if_pos hi]
    rw [hsig]
    have hj : (j = (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))) ↔ i.val + j.val = 2 * r + k := by
      rw [Fin.ext_iff]
      simp only
      omega
    simp only [Hpk, sgn, hj]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · have hsig : sig k r i = i := by
      unfold sig
      rw [if_neg hi]
    rw [hsig]
    push_neg at hi
    simp only [Hpk, sgn]
    by_cases hij : j = i
    · subst hij
      simp only [if_true, and_true, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hij' : ¬ i = j := fun h => hij h.symm
      simp only [hij, hij', if_false, and_false]
      split_ifs <;> first | rfl | (exfalso; omega)
end PI.StabSplit.UnipW
namespace PI.StabSplit
end PI.StabSplit
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW
namespace PI.StabSplit.UnipW
theorem _root_.solution {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ i, star (w i) * (sgn k r i * v (sig k r i)) := by
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, hpk_apply_of_outer_index, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
end PI.StabSplit.UnipW
