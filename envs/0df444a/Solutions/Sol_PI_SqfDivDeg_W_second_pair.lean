-- Prove2me | solution 1 for PI.SqfDivDeg.W.second_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:48.97656+00:00
-- url     : https://prove2.me/submissions/f3745efc-2bf4-417a-84b4-3463d184fd67

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_FibreNonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
namespace PI.SqfDivDeg.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] {q h : (ZMod g)[X]} (hq : q.Monic) (hh : h.Monic)
    (hs : Squarefree (q * h)) {x y : ZMod g} (hx : q.IsRoot x) (hy : h.IsRoot y) :
    ((X - C y) * (q /ₘ (X - C x))).Monic ∧ ((X - C x) * (h /ₘ (X - C y))).Monic ∧
    ((X - C y) * (q /ₘ (X - C x))).natDegree = q.natDegree ∧
    ((X - C x) * (h /ₘ (X - C y))).natDegree = h.natDegree ∧
    ((X - C y) * (q /ₘ (X - C x))) * ((X - C x) * (h /ₘ (X - C y))) = q * h ∧
    (X - C y) * (q /ₘ (X - C x)) ≠ q := by
  have hq' : (X - C x) * (q /ₘ (X - C x)) = q := mul_divByMonic_eq_iff_isRoot.mpr hx
  have hh' : (X - C y) * (h /ₘ (X - C y)) = h := mul_divByMonic_eq_iff_isRoot.mpr hy
  have mq : (q /ₘ (X - C x)).Monic :=
    (monic_X_sub_C x).of_mul_monic_left (by rw [hq']; exact hq)
  have mh : (h /ₘ (X - C y)).Monic :=
    (monic_X_sub_C y).of_mul_monic_left (by rw [hh']; exact hh)
  have dq : q.natDegree = 1 + (q /ₘ (X - C x)).natDegree := by
    conv_lhs => rw [← hq']
    rw [(monic_X_sub_C x).natDegree_mul mq, natDegree_X_sub_C]
  have dh : h.natDegree = 1 + (h /ₘ (X - C y)).natDegree := by
    conv_lhs => rw [← hh']
    rw [(monic_X_sub_C y).natDegree_mul mh, natDegree_X_sub_C]
  refine ⟨(monic_X_sub_C y).mul mq, (monic_X_sub_C x).mul mh, ?_, ?_, ?_, ?_⟩
  · rw [(monic_X_sub_C y).natDegree_mul mq, natDegree_X_sub_C, dq]
  · rw [(monic_X_sub_C x).natDegree_mul mh, natDegree_X_sub_C, dh]
  · calc (X - C y) * (q /ₘ (X - C x)) * ((X - C x) * (h /ₘ (X - C y)))
        = ((X - C x) * (q /ₘ (X - C x))) * ((X - C y) * (h /ₘ (X - C y))) := by ring
      _ = q * h := by rw [hq', hh']
  · intro heq
    have hqy : (X - C y) ∣ q := ⟨_, heq.symm⟩
    have hhy : (X - C y) ∣ h := dvd_iff_isRoot.mpr hy
    exact not_isUnit_X_sub_C y (hs _ (mul_dvd_mul hqy hhy))
end PI.SqfDivDeg.W
