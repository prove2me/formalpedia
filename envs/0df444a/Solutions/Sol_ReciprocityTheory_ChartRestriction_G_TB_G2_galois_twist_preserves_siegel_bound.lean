-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.galois_twist_preserves_siegel_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:16.063884+00:00
-- url     : https://prove2.me/submissions/494abf67-e5cd-4bb3-9776-24f9255ae40c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_G2Assumption

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (hA : ExpAddZeroConstant) (hE : ConstantCoeffSubstitution) (hG : CanonicalGaugeDiffBiadditive) (hQ : QuadraticFormDerivatives)
    (hW : WickOperatorVanishing) : AdmissibilitySecond := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' w0 m ι _ u P hP f
  unfold FB.nabVal
  set a : Fin 2 → Pt k 1 d := ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] with hadef
  set q := ev (n := 1) a (h' - h) with hqdef
  have hbi := hG R d O k B h h' hh hh'
  obtain ⟨hq0, hq1, hq2⟩ := hQ R d O k B (h' - h) hbi w0
  have hac : ∀ j i, constantCoeff (a j i) = 0 := by
    intro j i
    fin_cases j
    · simp [hadef, pt]
    · show constantCoeff (ev (n := 1) ![pt k d 0] (B.actK k w0 i)) = 0
      rw [hE k d 1 1 ![pt k d 0] _ (fun j i => by fin_cases j; simp [pt])]
      simp only [FB.actK]
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, B.A.const, map_zero]
  have hs : HasSubst (fun p : Fin 2 × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => hac p.1 p.2
  have hL' : B.hL k h' w0 = B.hL k h w0 + q := by
    simp only [FB.hL, hqdef, ev]
    rw [subst_sub hs]
    ring
  have hh0 : constantCoeff h = 0 := by
    have h1 := hE k d 2 1 ![0, pt k d 0] h (fun j i => by fin_cases j <;> simp [pt])
    rw [hh.ax0] at h1
    simpa using h1.symm
  have hL0 : constantCoeff (B.hL k h w0) = 0 := by
    simp only [FB.hL]
    rw [hE k d 2 1 _ h hac, hh0]
  have hexp : FB.expS k ((m : k) • B.hL k h' w0) =
      FB.expS k ((m : k) • B.hL k h w0) * FB.expS k ((m : k) • q) := by
    rw [hL', smul_add]
    exact hA k 1 d _ _ (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hL0, mul_zero])
      (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq0, mul_zero])
  rw [hexp, ← mul_assoc]
  symm
  exact hW k d (B.FK k) ι u
    (fun l l' => dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))))
    P q (fun l l' => add_comm _ _) hq0 (fun l => hq1 (u l)) (fun l l' => hq2 (u l) (u l')) hP (m : k)
    (f * FB.expS k ((m : k) • B.hL k h w0))
end ReciprocityTheory.ChartRestriction.G.TB.G2
