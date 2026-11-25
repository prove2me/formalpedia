-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.subst_sub_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:41.799039+00:00
-- url     : https://prove2.me/submissions/394f1e85-6899-4afb-a5ea-1cef2e15ae26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_multiset_prod_sub_dvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_finsupp_prod_eq_multiset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_card_toMultiset_eq_degree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {d : ℕ} (f : MvPowerSeries (Fin d) C)
    (hf : ∀ e : Fin d →₀ ℕ, e.degree ≤ 1 → coeff e f = 0)
    (α β : Fin d → PowerSeries C) (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (k : ℕ)
    (hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ k ∣ α b - β b) :
    (PowerSeries.X : PowerSeries C) ^ (k + 1) ∣ subst α f - subst β f := by
  have hA : HasSubst α := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => hα b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => hα b)
  have hB : HasSubst β := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => hβ b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => hβ b)
  have hterm : ∀ e : Fin d →₀ ℕ, ∀ j < k + 1,
      coeff e f • PowerSeries.coeff j (e.prod (fun s n => α s ^ n)) -
        coeff e f • PowerSeries.coeff j (e.prod (fun s n => β s ^ n)) = 0 := by
    intro e j hj
    by_cases he : e.degree ≤ 1
    · rw [hf e he, zero_smul, zero_smul, sub_zero]
    · rw [← smul_sub, ← map_sub]
      have hne : e.toMultiset ≠ 0 := by
        intro h0
        have h0' : Multiset.card e.toMultiset = 0 := by rw [h0]; rfl
        rw [card_toMultiset_eq_degree] at h0'
        omega
      have hdvd := multiset_prod_sub_dvd (PowerSeries.X : PowerSeries C) k α β
        (fun b => PowerSeries.X_dvd_iff.mpr (hα b)) (fun b => PowerSeries.X_dvd_iff.mpr (hβ b)) hk
        e.toMultiset hne
      rw [card_toMultiset_eq_degree, ← finsupp_prod_eq_multiset,
        ← finsupp_prod_eq_multiset] at hdvd
      have h2 := (pow_dvd_pow (PowerSeries.X : PowerSeries C)
        (show k + 1 ≤ k + e.degree - 1 by omega)).trans hdvd
      rw [PowerSeries.X_pow_dvd_iff.mp h2 j hj, smul_zero]
  rw [PowerSeries.X_pow_dvd_iff]
  intro j hj
  rw [map_sub]
  change MvPowerSeries.coeff (Finsupp.single () j) (subst α f) -
    MvPowerSeries.coeff (Finsupp.single () j) (subst β f) = 0
  rw [MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hB,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hA f _)
      (MvPowerSeries.coeff_subst_finite hB f _)]
  exact finsum_eq_zero_of_forall_eq_zero fun e => hterm e j hj
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
