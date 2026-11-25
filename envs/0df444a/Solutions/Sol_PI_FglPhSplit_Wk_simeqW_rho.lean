-- Prove2me | solution 1 for PI.FglPhSplit.Wk.simeqW_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:10.02382+00:00
-- url     : https://prove2.me/submissions/46c0903a-e117-4462-9983-2970da7ba790

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_subst_X
import Theorems.Thm_PI_FglPhSplit_Wk_expMv_eq_subst
import Theorems.Thm_PI_FglPhSplit_Wk_rho_apply
import Theorems.Thm_PI_FglPhSplit_Wk_rho_psubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
variable {ι ι' : Type} [Fintype ι]
variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0
omit hex0 hl0
namespace PI.FglPhSplit.Wk
theorem _root_.solution [CharZero K] {W : Subring K} {f h : MvPowerSeries (ι ⊕ ι) K}
    (hfh : SimeqW W f h) : SimeqW W (rho (ι' := ι') f) (rho h) := by
  unfold SimeqW at hfh ⊢
  obtain ⟨h0, hW⟩ := hfh
  have hcc : ∀ d : MvPowerSeries (ι ⊕ ι) K, MvPowerSeries.constantCoeff d = 0 →
      MvPowerSeries.constantCoeff (rho (ι' := ι') d) = 0 := by
    intro d hd
    rw [rho_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_subst hasSubst_inl]
    refine finsum_induction (p := fun x => x = 0) rfl (fun x z hx hz => by rw [hx, hz, add_zero])
      fun e => ?_
    by_cases he : e = 0
    · subst he
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hd, zero_smul]
    · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact he (Finsupp.ext hc)
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
        Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs)
          (by rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hs]), smul_zero]
  have hsub : rho (ι' := ι') f - rho h = rho (f - h) := (map_sub _ _ _).symm
  rw [hsub]
  refine ⟨hcc _ h0, fun n => ?_⟩
  rw [expMv_eq_subst (hcc _ h0), ← rho_psubst _ h0, ← expMv_eq_subst h0, rho_apply]
  exact allIn_subst_X Sum.inl hasSubst_inl hW n
end PI.FglPhSplit.Wk
