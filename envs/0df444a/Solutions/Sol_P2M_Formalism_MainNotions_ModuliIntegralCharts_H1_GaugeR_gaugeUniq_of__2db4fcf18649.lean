-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_gaugeUniq_of__2db4fcf18649
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:34.377427+00:00
-- url     : https://prove2.me/submissions/f4791b73-1f78-4a1a-89c2-c7377b5a1875

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqD
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeExpPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_corr_scaled
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_corr_scaled_left
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_exists_ps_of_compat
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_gam_pullUnit
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_jetAug_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_jetSubstP_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_psJet_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_psJet_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_psJet_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_ratio_exp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_ratio_of_gen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_scaled_genPow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_scaled_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_scaled_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_scaled_pull
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_value_scaled
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_psJet_inj
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_pull_unique
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_gam_to__114d125ac7f0


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution (hB : BetaUniqSt) (hR : GaugeRatioSt) (hP : ExpPowSt) : GaugeUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x hx e e' he he'
  have hL := Xo.univ.t.PP.isLB
  choose u hu using fun m => ratio_of_gen Xo.univ.t.PP.L hL (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ))
    (e m) (e' m) (he.gen m) (he'.gen m)
  let g : ∀ m, Jet S (Fin 1 × Fin (dL Dw)) m := fun m => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (u m).val
  have hpull : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (f : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] B),
      gam B (pullUnit (homAt y.x f).left (u m)).val = f (g m) := fun m B _ _ f =>
    gam_pullUnit (f : Jet S (Fin 1 × Fin (dL Dw)) m →+* B) (u m)
  have htr : ∀ m, jetTrunc (g (m + 1)) = g m := by
    intro m
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] _)).left (hu (m + 1))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (hu m) (he.trunc m) (he'.trunc m)
    have h2 := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    exact (hpull (m + 1) _ jetTrunc).symm.trans h2
  obtain ⟨r, hr⟩ := exists_ps_of_compat g htr
  have hrig : MvPowerSeries.constantCoeff r = 1 := by
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left (hu 0)
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (scaled_one _) he.rig he'.rig
    have h2 := congrArg (fun v => gam S (Units.val v)) hU
    simp only [Units.val_one, map_one] at h2
    rw [← jetAug_psJet 0 r, hr 0]
    exact (hpull 0 S jetAug).symm.trans h2
  have hid : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r *
        MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r := by
    intro a
    obtain ⟨β, hβg, hβr, hβc⟩ := he.coc a
    obtain ⟨β', hβ'g, hβ'r, hβ'c⟩ := he'.coc a
    obtain rfl := hB E H Dw l Xo a β β' hβg hβ'g hβr hβ'r
    refine GermFun.psJet_inj fun m => ?_
    have s1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a)))).left (hu m)
    have sa := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left (hu m)
    have sb := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a)))).left (hu m)
    have srhs := scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_one (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left))
      (scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_genPow _ _ sa 2) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (hu m) sb))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ s1 srhs (hβc m) (hβ'c m)
    have hv := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, one_mul] at hv
    rw [hpull, hpull, hpull] at hv
    have hv' : jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (1 + a * H.bar a) i) * MvPolynomial.X i) (g m) =
        jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S a i) * MvPolynomial.X i) (g m) ^ 2 *
          (g m * jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (a * H.bar a) i) * MvPolynomial.X i) (g m)) :=
      hv
    rw [psJet_mul, psJet_mul, psJet_pow, ← jetSubstP_scale, ← jetSubstP_scale, ← jetSubstP_scale, hr m, hv']
    ring
  obtain ⟨q, hq0, hdeg, hpair, hexp⟩ := ratio_exp hR c S r hrig hid
  refine ⟨q, hq0, hdeg, hpair, fun k F f f' hf hf' => ?_⟩
  refine GermFun.psJet_inj fun m => ?_
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hf' m
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have sg := scaled_genPow (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (hu m) k
  have sτ := corr_scaled_left Xo.univ.t.PP.L hL (x m).left (k : ℤ) _ _ τ₁ τ₂ _ _ _ sg hC₁ hC₂
  have hval := value_scaled Xo.univ.t.G Xo.univ.t.PP.L hL (k : ℤ) _ (x m) τ₁ τ₂ _ _ _ hV₁ hV₂ sτ
  have hg := congrArg (gam (Jet S (Fin 1 × Fin (dL Dw)) m)) hval
  rw [gam_toΓ, map_mul, gam_toΓ, Units.val_pow_eq_pow_val, map_pow] at hg
  have hpow := congrArg (psJet m) (hP S _ q hq0 k)
  rw [psJet_mul, psJet_pow, ← hexp, hr m, psJet_one] at hpow
  rw [psJet_mul, hg]
  calc psJet m f' = psJet m f' * (g m ^ k * psJet m (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S))) := by
        rw [hpow, mul_one]
    _ = _ := by ring
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
