-- Prove2me | solution 1 for WeierstrassCurve.natCard_stabilizer_variableChange_dvd_four_of_j_eq_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/574f55dd-c256-51e2-9d90-e00163ea1fd1

import Mathlib
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_dvd_four_of_j_eq_1728

set_option autoImplicit false

namespace WeierstrassCurve p2m_export "WeierstrassCurve" "VariableChange j natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728" end WeierstrassCurve
p2m_open_scoped "WeierstrassCurve" in

lemma WeierstrassCurve.natCard_rootsOfUnity_dvd' (F : Type*) [Field F] (k : ℕ) [NeZero k] :
    Nat.card (rootsOfUnity k F) ∣ k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity k F)
  have hgk : g ^ k = 1 := by
    have h := (mem_rootsOfUnity k (g : Fˣ)).mp g.2
    exact Subtype.ext (by push_cast; exact h)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_dvd_of_pow_eq_one hgk

theorem solution
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 1728) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ∣ 4 := by
  rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728
    h2 h3 E hj]
  exact WeierstrassCurve.natCard_rootsOfUnity_dvd' F 4

end S_WeierstrassCurve_natCard_stabilizer_variableChange_dvd_four_of_j_eq_1728
end P2MW
export P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_dvd_four_of_j_eq_1728 (solution)
