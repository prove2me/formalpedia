-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.gaugeExp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:20.682589+00:00
-- url     : https://prove2.me/submissions/683e37f6-a073-4098-8d33-36e8a2671757

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
open G2
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (hA : ExpAddZeroConstant) (hE : ConstantCoeffSubstitution) (hG : CanonicalGaugeDiffBiadditive) (hQ : QuadraticFormDerivatives)
    (hW : WickExpSt) : GaugeExpSt := by
  intro R _ d O _ _ k _ _ _ B h h' hh hh' w0 m ι _ u Q f
  have ha0 : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff
      ((![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] : Fin 2 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · simp [pt]
    · show MvPowerSeries.constantCoeff (ev ![pt k d 0] (B.actK k w0 i)) = 0
      rw [hE k d 1 1 ![pt k d 0] (B.actK k w0 i) (by intro j i; fin_cases j; simp [pt])]
      show MvPowerSeries.constantCoeff (MvPowerSeries.map (algebraMap R k) (B.A.act w0 i)) = 0
      rw [MvPowerSeries.constantCoeff_map, B.A.const, map_zero]
  have hc0 : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff
      ((![0, pt k d 0] : Fin 2 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  have hsub : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d =>
      (![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] : Fin 2 → Pt k 1 d) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha0 p.1 p.2)
  have hlin : B.hL k h' w0 = B.hL k h w0 +
      ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] (h' - h) := by
    simp only [FB.hL, ev]
    rw [MvPowerSeries.subst_sub hsub]
    abel
  have hch : MvPowerSeries.constantCoeff h = 0 := by
    rw [← hE k d 2 1 ![0, pt k d 0] h hc0, hh.ax0, map_zero]
  have hcL : MvPowerSeries.constantCoeff (B.hL k h w0) = 0 := by
    simp only [FB.hL]
    rw [hE k d 2 1 _ h ha0, hch]
  have hq := hQ R d O k B (h' - h) (hG R d O k B h h' hh hh') w0
  have hcm1 : MvPowerSeries.constantCoeff ((m : k) • B.hL k h w0) = 0 := by
    first
    | simp [hcL]
    | (rw [MvPowerSeries.smul_eq_C_mul]; simp [hcL])
  have hcm2 : MvPowerSeries.constantCoeff ((m : k) •
      ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] (h' - h)) = 0 := by
    first
    | simp [hq.1]
    | (rw [MvPowerSeries.smul_eq_C_mul]; simp [hq.1])
  simp only [FB.nabVal]
  rw [hlin, smul_add, hA k 1 d _ _ hcm1 hcm2, ← mul_assoc]
  exact hW k d (B.FK k) ι u _ Q _ (fun l l' => add_comm _ _) hq.1 (fun l => hq.2.1 (u l))
    (fun l l' => hq.2.2 (u l) (u l')) (m : k) _
end ReciprocityTheory.ChartRestriction.G.TB.GE
