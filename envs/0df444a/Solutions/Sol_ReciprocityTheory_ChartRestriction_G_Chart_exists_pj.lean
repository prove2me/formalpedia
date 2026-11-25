-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:06:04.468922+00:00
-- url     : https://prove2.me/submissions/d0fd9f1b-adc9-4efe-ad5a-bbcfa00161f2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pj_eq_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (z : ∀ m, JetR R σ m) (hz : ∀ m, jetTruncR R σ m (z (m + 1)) = z m) :
    ∃ f : MvPowerSeries σ R, ∀ m, pj m f = z m := by
  choose q hq using fun m => Ideal.Quotient.mk_surjective (z m)
  have step : ∀ m (e : σ →₀ ℕ), e.degree < m + 1 → (q (m + 1)).coeff e = (q m).coeff e := fun m e he => by
    have : Ideal.Quotient.mk _ (q (m + 1)) = Ideal.Quotient.mk _ (q m) := ((congrArg (jetTruncR R σ m) (hq _)).trans (hz m)).trans
      (hq m).symm
    rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at this
    exact sub_eq_zero.1 ((MvPolynomial.coeff_sub _ _ _ _).symm.trans (this e he))
  refine ⟨fun e => (q e.degree).coeff e, fun m => (pj_eq_mk.2 fun e he => ?_).trans (hq m)⟩
  show (q e.degree).coeff e = _
  induction m, Nat.le_of_lt_succ he using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [step k e (Nat.lt_succ_of_le hk), ih (Nat.lt_succ_of_le hk)]
end ReciprocityTheory.ChartRestriction.G.Chart
