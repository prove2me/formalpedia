-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.dsK_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:16.092007+00:00
-- url     : https://prove2.me/submissions/d37c5008-bdf4-4cfd-b9b3-1cc71428c050

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
variable {W : Scheme.{u}} {ι' : Type*} (V : ι' → W.Opens) (g : ∀ c, Γ(W, V c))
variable {V g}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {x : W} (c) (hc : x ∈ V c) :
    dsK V g x = Ideal.span {W.presheaf.germ (V c) x hc (g c)} := by
  unfold dsK
  apply le_antisymm
  · exact iInf₂_le c hc
  · refine le_iInf₂ fun c' hc' => ?_
    obtain ⟨u, hu⟩ := hg c c' x hc hc'
    rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨↑u, by rw [hu, mul_comm]⟩
end ReciprocityTheory.AnForm.R
