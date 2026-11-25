-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.ptx_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:54.289443+00:00
-- url     : https://prove2.me/submissions/cd084a7d-302c-485c-a9e5-1d1b07413eae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sub_dvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_sum_smul_tangent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_vecMul_inv_tmat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
private theorem lgCurve_zero' (G : LogFGL v d) (a : Fin d) :
    G.lgCurve (fun _ => (0 : PowerSeries C)) a = 0 := by
  have h0 : HasSubst (fun _ : Fin d => (0 : PowerSeries C)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun _ => by simp)
  ext j
  rw [map_zero]
  change MvPowerSeries.coeff (Finsupp.single () j) (subst _ (G.lg a)) = 0
  rw [MvPowerSeries.coeff_subst h0]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · subst he
    rw [coeff_zero_eq_constantCoeff_apply, G.lg_const a, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact he (Finsupp.ext hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [hs]),
      map_zero, smul_zero]
private theorem lc_at_zero_eq_tangent (G : LogFGL v d) (p : ℕ) (ga : Fin d → PowerSeries C)
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : G.lc p ga 0 = tangent ga := by
  funext a
  have hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - (fun _ => (0 : PowerSeries C)) b := by
    intro b
    show (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - 0
    rw [pow_one, sub_zero]
    exact PowerSeries.X_dvd_iff.mpr (h0 b)
  have h1 := lgCurve_sub_dvd (β := fun _ => (0 : PowerSeries C)) G h0 (fun _ => by simp) 1 hk a
  simp only [lgCurve_zero', sub_zero] at h1
  have h2 := PowerSeries.X_pow_dvd_iff.mp h1 1 (by norm_num)
  rw [map_sub, sub_eq_zero] at h2
  show PowerSeries.coeff (p ^ 0) (G.lgCurve ga a) = PowerSeries.coeff 1 (ga a)
  rw [pow_zero, h2]
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) (p : ℕ) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (tmat γ).det = 0) (ga : Fin d → PowerSeries C)
    (n : ℕ) :
    G.lc p ga n = ∑ s ∈ Finset.range (n + 1), ∑ b,
      (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s) := by
  have hlast : ∑ b, (ptx G p γ ga n b) ^ (p ^ (n - n)) • G.lc p (γ b) (n - n) =
      ptw G p γ ga n := by
    simp only [Nat.sub_self, pow_zero, pow_one]
    rw [Finset.sum_congr rfl (fun b _ => by rw [lc_at_zero_eq_tangent G p (γ b) (fun c => (hγ b c).1)]),
      sum_smul_tangent, ptx_eq, vecMul_inv_tmat hdet]
  rw [Finset.sum_range_succ, hlast, ptw]
  abel
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
