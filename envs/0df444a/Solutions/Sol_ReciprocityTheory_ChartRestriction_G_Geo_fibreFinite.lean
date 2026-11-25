-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:35:29.117064+00:00
-- url     : https://prove2.me/submissions/f16eb034-35de-4a24-977e-6daf3b082430

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibSys_finite


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
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]
variable {e : ℕ}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution : FibreFiniteStatement := by
  intro K _ ι _ P e Ψ hP hΨ y
  classical
  choose r hr G hG hrel using fun i => segre_rel hP.2.1.2.1 Ψ hΨ i
  let H : ((k : K) → ι k) → MvPolynomial ((k : K) → ι k) ℂ := fun i =>
    ∑ j, C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j) * G i j
  refine (fibSys_finite r H (fun i => ?_)).subset ?_
  · refine lt_of_le_of_lt ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_))
      (Nat.sub_lt (hr i) one_pos)
    exact (totalDegree_mul _ _).trans (by simpa using hG i j)
  · rintro w ⟨z, hz, rfl, hΨz⟩ i
    rw [hrel i z hz, hΨz]
    simp [H]
end ReciprocityTheory.ChartRestriction.G.Geo
