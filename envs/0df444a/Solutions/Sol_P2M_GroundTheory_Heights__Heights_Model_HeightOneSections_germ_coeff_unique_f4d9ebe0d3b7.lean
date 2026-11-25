-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_coeff_unique_f4d9ebe0d3b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:53.880527+00:00
-- url     : https://prove2.me/submissions/de613583-958d-46ee-89e6-1d0df023669a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_comb_8d6e321d74e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_comb_res_b8d8455008cb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]
omit [IsIntegral X]
namespace GroundTheory.Heights₂.Heights.Model.HeightOneSections
theorem _root_.solution (E : X.Modules) {V : X.Opens} {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (x : X) (hxV : x ∈ V) {W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ V)
    (hx : x ∈ W) (hx' : x ∈ W') (r : Fin n → Γ(X, W)) (r' : Fin n → Γ(X, W'))
    (e : ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x hxV (s i) =
      ∑ i, X.presheaf.germ W' x hx' (r' i) • E.presheaf.germ V x hxV (s i)) (i : Fin n) :
    X.presheaf.germ W x hx (r i) = X.presheaf.germ W' x hx' (r' i) := by
  rw [← germ_comb E s W h r x hx, ← germ_comb E s W' h' r' x hx'] at e
  obtain ⟨W'', hx'', iU, iV, e'⟩ := E.presheaf.germ_eq x hx hx' _ _ e
  have hU : iU = homOfLE iU.le := rfl
  have hV : iV = homOfLE iV.le := rfl
  rw [hU, hV, comb_res, comb_res] at e'
  have := (hs W'' (iU.le.trans h)).1 e'
  have hi := congrFun this i
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf iU x hx'' (r i),
    ← TopCat.Presheaf.germ_res_apply X.presheaf iV x hx'' (r' i)]
  exact congrArg (X.presheaf.germ W'' x hx'') hi
end GroundTheory.Heights₂.Heights.Model.HeightOneSections
