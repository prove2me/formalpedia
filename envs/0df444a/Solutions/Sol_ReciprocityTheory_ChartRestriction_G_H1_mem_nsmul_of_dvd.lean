-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.mem_nsmul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:25:53.200656+00:00
-- url     : https://prove2.me/submissions/1b553033-ce56-407d-a445-4428a6713c44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (Dw : Datum H) (N : ℕ) (d : Dw.La)
    (h : ∀ b, (N : ℤ) ∣ Dw.EF b d) : ∃ f : Dw.La, d = N • f := by
  have skew : ∀ x y, Dw.EF x y = - Dw.EF y x := by
    intro x y
    have hxy := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at hxy
    linarith
  have hdiv : ∀ y, (N : ℤ) ∣ Dw.EF d y := fun y => by
    rw [skew]
    exact dvd_neg.mpr (h y)
  let φ : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => Dw.EF d y / N
      map_add' := fun y z => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_left (hdiv y)
      map_smul' := fun m y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc _ (hdiv y) }
  obtain ⟨f, hf⟩ := Dw.unimod.2 φ
  refine ⟨f, Dw.unimod.1 (LinearMap.ext fun y => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, hf]
  show Dw.EF d y = N • (Dw.EF d y / N)
  rw [nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv y)]
end ReciprocityTheory.ChartRestriction.G.H1
