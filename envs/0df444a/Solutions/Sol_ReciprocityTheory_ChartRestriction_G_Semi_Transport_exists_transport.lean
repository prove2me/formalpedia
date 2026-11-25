-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.exists_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:20.356257+00:00
-- url     : https://prove2.me/submissions/61b317e9-4460-42ad-8dd3-5b54d3ba969f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_glueU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_cand
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
section Transport
variable {A B : LB X}
private theorem gUcand_lemma (w : LB.Iso A B) (b : LB.Gen B) (q : A.ι) (p : B.ι) (x : X)
    (hx : x ∈ A.U q ⊓ B.U p) :
    gU x hx (cand w b q p) = (gU x (le_divU p q hx) (w.s (pq p q)))⁻¹ * gU x hx.2 (b.s p) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (gUres_lemma _ _ _ _)))
    (gUres_lemma _ _ _ _))
private theorem tr_lemma {G : Type*} [CommGroup G] (si sj wi wj d c a bb : G) (e1 : si = wi⁻¹ * bb)
    (e2 : sj = wj⁻¹ * bb) (h1 : wi = d * wj) (hd : d = c * a⁻¹) (h3 : c = 1) : si = a * sj := by
  subst e1 e2 h1 hd h3
  simp only [one_mul, mul_inv_rev, inv_inv, mul_assoc]
  exact mul_left_comm _ _ _
private theorem tr_lemma_2 {G : Type*} [CommGroup G] (s w bb : G) (e : s = w⁻¹ * bb) : bb = w * s := by
  subst e
  exact (mul_inv_cancel_left w bb).symm
private theorem trgerm_lemma (w : LB.Iso A B) (b : LB.Gen B) (q : A.ι) (p : B.ι) (sq : Γ(X, A.U q)ˣ)
    (hsq : res (inf_le_left : A.U q ⊓ B.U p ≤ A.U q) sq = cand w b q p) (x : X)
    (hx : x ∈ A.U q ⊓ B.U p) :
    gU x hx.1 sq = (gU x (le_divU p q hx) (w.s (pq p q)))⁻¹ * gU x hx.2 (b.s p) :=
  (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x hx) hsq).trans (gUcand_lemma w b q p x hx))
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
theorem _root_.solution (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen) (b : LB.Gen B)
    (hb : b.IsGen) : ∃ a : LB.Gen A, a.IsGen ∧ LB.Gen.Maps w a b := by
  have hxB : ∀ x : X, ∃ p, x ∈ B.U p := fun x =>
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hB.cover]; simp)
  have hc : ∀ q, A.U q ≤ ⨆ p, A.U q ⊓ B.U p := fun q =>
    le_of_eq (by rw [← inf_iSup_eq, hB.cover, inf_top_eq])
  choose s hs using fun q => glueU (A.U q) (fun p => A.U q ⊓ B.U p) (fun _ => inf_le_left) (hc q)
    (fun p => cand w b q p) (fun p p' x hx => gU_cand hA w hw b hb q p p' x hx.1 hx.2)
  refine ⟨⟨s⟩, isGenOfGerm_lemma _ (fun i j x hx => ?_), mapsOfGerm_lemma w _ b (fun p q x hx => ?_)⟩
  · obtain ⟨p, hp⟩ := hxB x
    have e1 := trgerm_lemma w b i p (s i) (hs i p) x ⟨hx.1, hp⟩
    have e2 := trgerm_lemma w b j p (s j) (hs j p) x ⟨hx.2, hp⟩
    have h1 := gU_isGen hw x (le_divU p i ⟨hx.1, hp⟩) (le_divU p j ⟨hx.2, hp⟩)
    have hd := gU_div B A (pq p i) (pq p j) x (le_divU p i ⟨hx.1, hp⟩) (le_divU p j ⟨hx.2, hp⟩)
    have h3 := gU_self hB x hp
    exact tr_lemma _ _ _ _ _ _ _ _ e1 e2 h1 hd h3
  · have e := trgerm_lemma w b q p (s q) (hs q p) x ⟨hx.2, hx.1⟩
    exact tr_lemma_2 _ _ _ e
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
