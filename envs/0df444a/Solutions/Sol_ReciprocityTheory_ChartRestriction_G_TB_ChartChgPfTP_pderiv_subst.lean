-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:56:06.227055+00:00
-- url     : https://prove2.me/submissions/da11af67-90e6-4196-b169-deb041f8b638

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_pderiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_pderiv_subst_coe

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {σ τ : Type} [Fintype σ] [DecidableEq σ] (a : σ → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (i : τ) (f : MvPowerSeries σ k) :
    pderiv k i (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k i (a s) := by
  classical
  have hs : HasSubst a := (by first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha)
  have hle : ∀ (m : σ →₀ ℕ) (s : σ), m s ≤ m.degree := by
    intro m s
    have h := congrArg Finsupp.degree (Finsupp.single_add_erase s m)
    first
    | (rw [map_add, Finsupp.degree_single] at h; omega)
    | (rw [map_add] at h
       have h3 : Finsupp.degree (Finsupp.single s (m s)) = m s := by simp
       omega)
    | exact Finsupp.le_degree s m
    | exact Finsupp.le_degree m s
  ext e
  obtain ⟨q, hq⟩ : ∃ q : MvPolynomial σ k, OrdGE (e.degree + 1 + 1) (f - (q : MvPowerSeries σ k)) := by
    refine ⟨∑ m ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ : σ => e.degree + 1 + 1)),
      MvPolynomial.monomial m (coeff m f), ?_⟩
    intro m hm
    have hmn : m ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ : σ => e.degree + 1 + 1)) := by
      rw [Finset.mem_Iic]
      show ∀ s, m s ≤ (Finsupp.equivFunOnFinite.symm (fun _ : σ => e.degree + 1 + 1)) s
      intro s
      have := hle m s
      first
      | (rw [Finsupp.equivFunOnFinite_symm_apply]; omega)
      | (simp only [Finsupp.equivFunOnFinite_symm_apply]; omega)
      | (show m s ≤ e.degree + 1 + 1; omega)
    rw [map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial, hmn]
  have k1 : coeff e (pderiv k i (subst a (f - (q : MvPowerSeries σ k)))) = 0 :=
    ordGE_pderiv i (r := e.degree + 1) (ordGE_subst a ha hq) e (by omega)
  have k2 : coeff e (∑ s, subst a (pderiv k s (f - (q : MvPowerSeries σ k))) * pderiv k i (a s)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    exact ordGE_mul (ordGE_subst a ha (ordGE_pderiv s (r := e.degree + 1) hq))
      (ordGE_zero_left (pderiv k i (a s))) e (by omega)
  have hpoly := ChartChgPfTP.pderiv_subst_coe hs i q
  rw [MvPowerSeries.coe_substAlgHom] at hpoly
  have hfq : f = (q : MvPowerSeries σ k) + (f - (q : MvPowerSeries σ k)) := (add_sub_cancel _ _).symm
  rw [hfq]
  simp only [MvPowerSeries.subst_add hs, map_add, add_mul, Finset.sum_add_distrib, hpoly, k1, k2]
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
