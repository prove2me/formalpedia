-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_cand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:05.556215+00:00
-- url     : https://prove2.me/submissions/224e6f7e-51e1-4b7b-8563-4ce66188b676

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.Semi.Transport
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
variable {X : Scheme.{0}}
private theorem gUres_lemma {O O' : X.Opens} (hle : O' ≤ O) (x : X) (hx : x ∈ O')
    (s : Γ(X, O)ˣ) : gU x hx (res hle s) = gU x (hle hx) s :=
  gU_res hle x hx s
section Transport
variable {A B : LB X}
private theorem cand_lemma {G : Type*} [CommGroup G] (g a d w w' b b' : G) (h1 : w = d * w')
    (hd : d = g * a⁻¹) (h3 : a = 1) (h2 : b = g * b') : w⁻¹ * b = w'⁻¹ * b' := by
  subst h1 hd h3 h2
  simp only [inv_one, mul_one, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
private theorem gUcand_lemma (w : LB.Iso A B) (b : LB.Gen B) (q : A.ι) (p : B.ι) (x : X)
    (hx : x ∈ A.U q ⊓ B.U p) :
    gU x hx (cand w b q p) = (gU x (le_divU p q hx) (w.s (pq p q)))⁻¹ * gU x hx.2 (b.s p) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (gUres_lemma _ _ _ _)))
    (gUres_lemma _ _ _ _))
end Transport
section InvComp
variable {A B C : LB X}
end InvComp
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Transport
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
variable {X : Scheme.{0}}
variable {A B : LB X}
namespace ReciprocityTheory.ChartRestriction.G.Semi.Transport
theorem _root_.solution (hA : A.IsLB) (w : LB.Iso A B) (hw : w.IsGen) (b : LB.Gen B) (hb : b.IsGen)
    (q : A.ι) (p p' : B.ι) (x : X) (hx : x ∈ A.U q ⊓ B.U p) (hx' : x ∈ A.U q ⊓ B.U p') :
    gU x hx (cand w b q p) = gU x hx' (cand w b q p') := by
  have h1 := gU_isGen hw x (le_divU p q hx) (le_divU p' q hx')
  have hd := gU_div B A (pq p q) (pq p' q) x (le_divU p q hx) (le_divU p' q hx')
  have h3 := gU_self hA x hx.1
  have h2 := gU_isGen hb x hx.2 hx'.2
  exact (gUcand_lemma w b q p x hx).trans ((cand_lemma _ _ _ _ _ _ _ h1 hd h3 h2).trans
    (gUcand_lemma w b q p' x hx').symm)
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
