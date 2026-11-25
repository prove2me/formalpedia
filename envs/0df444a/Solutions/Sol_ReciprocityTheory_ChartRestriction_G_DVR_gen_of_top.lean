-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gen_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:17:29.417101+00:00
-- url     : https://prove2.me/submissions/cfb06e5c-49d8-4338-b4ca-fdba0ab32226

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum


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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : L.IsLB) {S : Scheme.{0}} {W : Over S} (ψ : K → (W.left ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L (fun k => (W.hom ⁻¹ᵁ ⊤).ι ≫ ψ k) ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L ψ ε), t'.IsGen := by
  have e : ∀ k, W.left.topIso.inv ≫ (W.hom ⁻¹ᵁ ⊤).ι ≫ ψ k = ψ k := fun k =>
    W.left.toIso_inv_ι_assoc (ψ k)
  have hs : LB.SameSum (fun k => W.left.topIso.inv ≫ (W.hom ⁻¹ᵁ ⊤).ι ≫ ψ k) ε ψ ε := by
    rw [sameSum_iff_fsum]
    exact congrArg (fun f => fsum f ε) (funext e)
  obtain ⟨t', ht', -⟩ := gen_transport hL hs _ (pullGen_isGen_of_isGen _ ε t ht W.left.topIso.inv)
  exact ⟨t', ht'⟩
end ReciprocityTheory.ChartRestriction.G.DVR
