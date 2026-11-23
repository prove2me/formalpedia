-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mem_dsJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:55.795407+00:00
-- url     : https://prove2.me/submissions/20b9dd96-d468-4e18-a3ae-e50d89342941

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
variable (V g)
variable {V g}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {U : W.affineOpens} {f : Γ(W, U)} :
    f ∈ dsJ V g U ↔ ∀ x (hx : x ∈ U.1), W.presheaf.germ U.1 x hx f ∈ dsK V g x := by
  unfold dsJ
  simp only [Submodule.mem_iInf, Ideal.mem_comap]
  all_goals exact Iff.rfl
end ReciprocityTheory.AnForm.R
