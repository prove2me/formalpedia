-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.ptx_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:29.52508+00:00
-- url     : https://prove2.me/submissions/222d0c39-4fcf-4e71-894b-e8627eb78e33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sub_dvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_vecMul_inv_tmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_vecMul_tmat_support

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
private theorem lgCurve_const_zero (G : LogFGL v d) (a : Fin d) :
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
private theorem lc_zero_eq_tangent_of_constantCoeff_eq_zero (G : LogFGL v d) (p : ℕ) (ga : Fin d → PowerSeries C)
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : G.lc p ga 0 = tangent ga := by
  funext a
  have hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - (fun _ => (0 : PowerSeries C)) b := by
    intro b
    show (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - 0
    rw [pow_one, sub_zero]
    exact PowerSeries.X_dvd_iff.mpr (h0 b)
  have h1 := lgCurve_sub_dvd (β := fun _ => (0 : PowerSeries C)) G h0 (fun _ => by simp) 1 hk a
  simp only [lgCurve_const_zero, sub_zero] at h1
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
theorem _root_.solution {h : ℕ} (ty : Fin d → ZMod h) (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (tmat γ).det = 0)
    (hγty : ∀ b, G.IsOfType p ty (ty b) (γ b)) (ga : Fin d → PowerSeries C) (i : ZMod h)
    (hga : G.IsOfType p ty i ga) :
    ∀ n b, ptx G p γ ga n b ≠ 0 → ty b = i + n := by
  have ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0 := by
    intro b c hc
    have h0 := (hγty b).2 0 c (by simpa using hc)
    rwa [lc_zero_eq_tangent_of_constantCoeff_eq_zero G p (γ b) (fun c' => (hγ b c').1)] at h0
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hw : ∀ c, ty c ≠ i + n → Matrix.vecMul (ptx G p γ ga n) (tmat γ) c = 0 := by
      intro c hc
      rw [ptx_eq, vecMul_inv_tmat hdet]
      simp only [ptw, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hga.2 n c hc, zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro s hs
      have hsn : s < n := Finset.mem_range.mp hs
      apply Finset.sum_eq_zero
      intro b _
      by_cases hx0 : ptx G p γ ga s b = 0
      · rw [hx0, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul]
      · have htb := ih s hsn b hx0
        have hlc : G.lc p (γ b) (n - s) c = 0 := by
          apply (hγty b).2 (n - s) c
          rw [htb, Nat.cast_sub hsn.le]
          intro h'
          apply hc
          rw [h']
          ring
        rw [hlc, mul_zero]
    intro b hb
    by_contra hne
    exact hb (vecMul_tmat_support ty hdet ht (ptx G p γ ga n) (i + n) hw b hne)
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
