-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.khw_lowK_sub_root_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:26.867302+00:00
-- url     : https://prove2.me/submissions/9def1258-b9db-4df7-8739-a4e670ec2552

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_nsq_add__e834c2ab7af1
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_nsq_sub__a7aa378eee5a
import Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_DS_nsq_root_da10e168d3dff856
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_khw_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rho_eq_rhoC_add_rhoN


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) (lam : Fin n → ℝ) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) (hgap : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b)) {v : M}
    (hv : IsKHWVec ε E (lowK ε lam - root a b) v)
    (hc : casimir E v = (casVal lam : ℂ) • v) : v = 0 := by
  by_contra hv0
  have hle := casimir_khw_le ε hE hU hv hv0 hc
  have hμ : lowK ε lam - root a b + rhoC ε - rhoN ε = lam - root a b := by
    ext i; simp only [lowK, Pi.add_apply, Pi.sub_apply]; ring
  rw [hμ] at hle
  have e1 := nsq_sub' lam (root a b)
  have e2 : nsq (root a b) = 2 := nsq_root (ne_of_lt hab)
  have e3 : casVal lam = nsq lam - (nsq (rhoC ε) + 2 * dot (rhoC ε) (rhoN ε) + nsq (rhoN ε)) := by
    rw [casVal, rho_eq_rhoC_add_rhoN ε, nsq_add']
  have e4 := nsq_sub' (rhoC ε) (rhoN ε)
  linarith
end ReciprocityTheory.ChartRestriction.DS
