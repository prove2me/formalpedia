-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.proj_ne_zero_of_snc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:16:31.855166+00:00
-- url     : https://prove2.me/submissions/f1e593c0-c95b-4c53-8757-75277843ed2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_snc_eval_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_divSupp_of_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P J : Ideal (MRing ι)} {e n : ℕ} (R : AnLogRes P J e) {A : HermLine ι}
    {s : MRing ι} {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set R.X}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hsnc : IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W)
    (hΨ : ∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) {k : Fin r} (hm : m k ≠ 0)
    {x : R.X} (hx : x ∈ W k) : Ψ (segre (R.lift x x)) ≠ 0 := by
  have h0 := snc_eval_zero hsnc hx hm
  have hz : R.lift x x ∈ mcPts P := R.mem x x (R.mem_U x)
  obtain ⟨W', hW', hh, hzW⟩ := exists_divSupp_of_eval hz h0
  exact hΨ W' hW' hh _ hzW
end ReciprocityTheory.ChartRestriction.G.Geo
