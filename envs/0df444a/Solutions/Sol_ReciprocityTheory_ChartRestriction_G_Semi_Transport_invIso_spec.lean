-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.invIso_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:08.823094+00:00
-- url     : https://prove2.me/submissions/fa59560e-fae0-41e3-ae3d-0863474134ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_cg
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
private theorem isGenOfGerm_lemma {L : LB X} (t : LB.Gen L)
    (h : ∀ i j (x : X) (hx : x ∈ L.U i ⊓ L.U j),
      gU x hx.1 (t.s i) = gU x hx (L.g i j) * gU x hx.2 (t.s j)) : t.IsGen := by
  intro i j
  apply unit_ext
  intro x hx
  rw [map_mul, gUres_lemma, gUres_lemma]
  exact h i j x hx
private theorem mapsOfGerm_lemma {A B : LB X} (w : LB.Iso A B) (a : LB.Gen A) (b : LB.Gen B)
    (h : ∀ p q (x : X) (hx : x ∈ B.U p ⊓ A.U q),
      gU x hx.1 (b.s p) = gU x hx (w.s (p, q)) * gU x hx.2 (a.s q)) : LB.Gen.Maps w a b := by
  rintro ⟨p, q⟩
  apply unit_ext
  intro x hx
  rw [map_mul, gUres_lemma, gUres_lemma]
  exact h p q x hx
private theorem germOfMaps_lemma {A B : LB X} (w : LB.Iso A B) (a : LB.Gen A) (b : LB.Gen B)
    (hab : LB.Gen.Maps w a b) (p : B.ι) (q : A.ι) (x : X) (hx : x ∈ B.U p ⊓ A.U q) :
    gU x hx.1 (b.s p) = gU x hx (w.s (p, q)) * gU x hx.2 (a.s q) :=
  (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x hx) (hab (p, q))).trans
    ((map_mul _ _ _).trans (congrArg (_ * ·) (gUres_lemma _ _ _ _))))
section Transport
variable {A B : LB X}
end Transport
section InvComp
variable {A B C : LB X}
private theorem invgerm_lemma (w : LB.Iso A B) (q : A.ι) (p : B.ι) (x : X)
    (hx : x ∈ A.U q ⊓ B.U p) :
    gU x hx ((invIso w).s (q, p)) = (gU x (le_divU p q hx) (w.s (pq p q)))⁻¹ :=
  (map_inv _ _).trans (congrArg (·⁻¹) (gUres_lemma _ _ _ _))
private theorem inv_lemma' {G : Type*} [CommGroup G] (w w' bg a d : G) (hg : w = bg * a⁻¹ * w')
    (hd : d = a * bg⁻¹) : w⁻¹ = d * w'⁻¹ := by
  subst hg hd
  exact cg a bg w'
private theorem inv_lemma_2 {G : Type*} [CommGroup G] (aa w bb : G) (e : bb = w * aa) :
    aa = w⁻¹ * bb := by
  subst e
  exact (inv_mul_cancel_left w aa).symm
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
variable {A B C : LB X}
namespace ReciprocityTheory.ChartRestriction.G.Semi.Transport
theorem _root_.solution (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen) :
    (invIso w).IsGen ∧ ∀ (a : LB.Gen A) (b : LB.Gen B), LB.Gen.Maps w a b →
      LB.Gen.Maps (invIso w) b a := by
  refine ⟨isGenOfGerm_lemma _ ?_, fun a b hab => mapsOfGerm_lemma _ _ _ ?_⟩
  · rintro ⟨q, p⟩ ⟨q', p'⟩ x hx
    have hg := gU_iso w hw p p' q q' x hx.1 hx.2
    have hd := gU_div A B (q, p) (q', p') x hx.1 hx.2
    have i1 := invgerm_lemma w q p x hx.1
    have i2 := invgerm_lemma w q' p' x hx.2
    exact i1.trans ((inv_lemma' _ _ _ _ _ hg hd).trans (congrArg (_ * ·) i2.symm))
  · intro q p x hx
    have e := germOfMaps_lemma w a b hab p q x ⟨hx.2, hx.1⟩
    have i1 := invgerm_lemma w q p x hx
    exact (inv_lemma_2 _ _ _ e).trans (congrArg (· * _) i1.symm)
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
