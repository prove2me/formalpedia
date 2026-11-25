-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.cc_ordEval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:20.052666+00:00
-- url     : https://prove2.me/submissions/3343d0ce-3882-4add-be8c-9f898dcb0b16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_good_ofFn

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (J : Submodule R k) (e : ℕ) (E0 : AA k d) (hE0 : constantCoeff E0 = 1) {r q : ℕ}
    (a : Fin r → Module.End k (AA k d)) (a' : Fin q → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (ha' : ∀ j X, GoodE R E0 X → GoodE R E0 (a' j X))
    (σ : AA k d) (hσ : GoodE R E0 σ) (Q : MvPolynomial (Fin r ⊕ Fin q) k) (hQ : ∀ mo, Q.coeff mo ∈ J ^ e) :
    constantCoeff (PI.WickFormula.ordEval a a' Q σ) ∈ J ^ e := by
  unfold PI.WickFormula.ordEval
  rw [LinearMap.sum_apply, map_sum]
  refine Submodule.sum_mem _ fun mo _ => ?_
  have hgood : GoodE R E0 (((List.ofFn fun i => a i ^ mo (Sum.inl i)).prod *
      (List.ofFn fun j => a' j ^ mo (Sum.inr j)).prod) σ) :=
    good_ofFn E0 a ha _ _ (good_ofFn E0 a' ha' _ σ hσ)
  obtain ⟨G, hGi, hGe⟩ := hgood
  rw [LinearMap.smul_apply, hGe, MvPowerSeries.smul_eq_C_mul, map_mul, map_mul,
    MvPowerSeries.constantCoeff_C, hE0, one_mul]
  obtain ⟨r, hr⟩ := hGi 0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← hr, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hQ mo)
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
