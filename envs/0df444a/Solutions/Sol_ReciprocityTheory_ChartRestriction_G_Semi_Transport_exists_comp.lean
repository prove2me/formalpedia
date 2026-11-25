-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.exists_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:51:37.433663+00:00
-- url     : https://prove2.me/submissions/2f5bec18-f994-49f5-9166-8b860a764e96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_glueU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_cg4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_cg5
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
private theorem comploc_lemma (w1 : LB.Iso A B) (w2 : LB.Iso B C) (r : C.ι) (q : A.ι) (p : B.ι)
    (x : X) (hx : x ∈ C.U r ⊓ A.U q ⊓ B.U p) :
    gU x hx (res (show C.U r ⊓ A.U q ⊓ B.U p ≤ C.U r ⊓ B.U p from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (w2.s (r, p)) *
      res (show C.U r ⊓ A.U q ⊓ B.U p ≤ B.U p ⊓ A.U q from
        le_inf inf_le_right (inf_le_left.trans inf_le_right)) (w1.s (p, q))) =
      gU x (⟨hx.1.1, hx.2⟩ : x ∈ C.U r ⊓ B.U p) (w2.s (r, p)) *
        gU x (⟨hx.2, hx.1.2⟩ : x ∈ B.U p ⊓ A.U q) (w1.s (p, q)) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gUres_lemma _ _ _ _) (gUres_lemma _ _ _ _))
private theorem compgerm_lemma (w1 : LB.Iso A B) (w2 : LB.Iso B C) (r : C.ι) (q : A.ι) (p : B.ι)
    (srq : Γ(X, C.U r ⊓ A.U q)ˣ)
    (hs : res (inf_le_left : C.U r ⊓ A.U q ⊓ B.U p ≤ C.U r ⊓ A.U q) srq =
      res (show C.U r ⊓ A.U q ⊓ B.U p ≤ C.U r ⊓ B.U p from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (w2.s (r, p)) *
      res (show C.U r ⊓ A.U q ⊓ B.U p ≤ B.U p ⊓ A.U q from
        le_inf inf_le_right (inf_le_left.trans inf_le_right)) (w1.s (p, q)))
    (x : X) (hx : x ∈ C.U r ⊓ A.U q ⊓ B.U p) :
    gU x hx.1 srq = gU x (⟨hx.1.1, hx.2⟩ : x ∈ C.U r ⊓ B.U p) (w2.s (r, p)) *
        gU x (⟨hx.2, hx.1.2⟩ : x ∈ B.U p ⊓ A.U q) (w1.s (p, q)) :=
  (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x hx) hs).trans (comploc_lemma w1 w2 r q p x hx))
private theorem comp_lemma {G : Type*} [CommGroup G] (w1 w1' d1 w2 w2' d2 bg a c : G)
    (h1 : w1 = d1 * w1') (hd1 : d1 = bg * a⁻¹) (ha : a = 1) (h2 : w2 = d2 * w2')
    (hd2 : d2 = c * bg⁻¹) (hc : c = 1) : w2 * w1 = w2' * w1' := by
  subst h1 hd1 ha h2 hd2 hc
  simp only [inv_one, mul_one, one_mul]
  exact cg4 bg w2' w1'
private theorem comp_lemma_2 {G : Type*} [CommGroup G] (s s' w2 w2' w1 w1' d2 d1 d3 c bb a : G)
    (e1 : s = w2 * w1) (e2 : s' = w2' * w1') (h2 : w2 = d2 * w2') (hd2 : d2 = c * bb⁻¹)
    (h1 : w1 = d1 * w1') (hd1 : d1 = bb * a⁻¹) (hbb : bb = 1) (hd3 : d3 = c * a⁻¹) :
    s = d3 * s' := by
  subst e1 e2 h2 hd2 h1 hd1 hbb hd3
  simp only [inv_one, mul_one, one_mul]
  exact cg5 c a w2' w1'
private theorem comp_lemma_3 {G : Type*} [CommGroup G] (s w2 w1 aa bb cc : G) (e : s = w2 * w1)
    (eb : bb = w1 * aa) (ec : cc = w2 * bb) : cc = s * aa := by
  subst e eb ec
  exact (mul_assoc w2 w1 aa).symm
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
theorem _root_.solution (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) (w1 : LB.Iso A B) (hw1 : w1.IsGen)
    (w2 : LB.Iso B C) (hw2 : w2.IsGen) :
    ∃ w3 : LB.Iso A C, w3.IsGen ∧ ∀ (a : LB.Gen A) (b : LB.Gen B) (c : LB.Gen C),
      LB.Gen.Maps w1 a b → LB.Gen.Maps w2 b c → LB.Gen.Maps w3 a c := by
  have hxB : ∀ x : X, ∃ p, x ∈ B.U p := fun x =>
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hB.cover]; simp)
  have hcv : ∀ rq : C.ι × A.ι, C.U rq.1 ⊓ A.U rq.2 ≤ ⨆ p, C.U rq.1 ⊓ A.U rq.2 ⊓ B.U p :=
    fun rq => le_of_eq (by rw [← inf_iSup_eq, hB.cover, inf_top_eq])
  choose s hs using fun rq : C.ι × A.ι => glueU (C.U rq.1 ⊓ A.U rq.2)
    (fun p => C.U rq.1 ⊓ A.U rq.2 ⊓ B.U p) (fun _ => inf_le_left) (hcv rq)
    (fun p => res (show C.U rq.1 ⊓ A.U rq.2 ⊓ B.U p ≤ C.U rq.1 ⊓ B.U p from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (w2.s (rq.1, p)) *
      res (show C.U rq.1 ⊓ A.U rq.2 ⊓ B.U p ≤ B.U p ⊓ A.U rq.2 from
        le_inf inf_le_right (inf_le_left.trans inf_le_right)) (w1.s (p, rq.2)))
    (fun p p' x hx => by
      have h1 := gU_isGen (i := (p, rq.2)) (j := (p', rq.2)) hw1 x
        (⟨hx.1.2, hx.1.1.2⟩ : x ∈ B.U p ⊓ A.U rq.2) (⟨hx.2.2, hx.1.1.2⟩ : x ∈ B.U p' ⊓ A.U rq.2)
      have hd1 := gU_div B A (p, rq.2) (p', rq.2) x
        (⟨hx.1.2, hx.1.1.2⟩ : x ∈ B.U p ⊓ A.U rq.2) (⟨hx.2.2, hx.1.1.2⟩ : x ∈ B.U p' ⊓ A.U rq.2)
      have ha := gU_self hA x hx.1.1.2
      have h2 := gU_isGen (i := (rq.1, p)) (j := (rq.1, p')) hw2 x
        (⟨hx.1.1.1, hx.1.2⟩ : x ∈ C.U rq.1 ⊓ B.U p) (⟨hx.1.1.1, hx.2.2⟩ : x ∈ C.U rq.1 ⊓ B.U p')
      have hd2 := gU_div C B (rq.1, p) (rq.1, p') x
        (⟨hx.1.1.1, hx.1.2⟩ : x ∈ C.U rq.1 ⊓ B.U p) (⟨hx.1.1.1, hx.2.2⟩ : x ∈ C.U rq.1 ⊓ B.U p')
      have hc1 := gU_self hC x hx.1.1.1
      exact (comploc_lemma w1 w2 rq.1 rq.2 p x hx.1).trans
        ((comp_lemma _ _ _ _ _ _ _ _ _ h1 hd1 ha h2 hd2 hc1).trans
          (comploc_lemma w1 w2 rq.1 rq.2 p' x hx.2).symm))
  refine ⟨⟨s⟩, isGenOfGerm_lemma _ ?_, fun a b c hab hbc => mapsOfGerm_lemma _ _ _ ?_⟩
  · rintro ⟨r, q⟩ ⟨r', q'⟩ x hx
    obtain ⟨p, hp⟩ := hxB x
    have e1 := compgerm_lemma w1 w2 r q p (s (r, q)) (hs (r, q) p) x ⟨hx.1, hp⟩
    have e2 := compgerm_lemma w1 w2 r' q' p (s (r', q')) (hs (r', q') p) x ⟨hx.2, hp⟩
    have h2 := gU_isGen (i := (r, p)) (j := (r', p)) hw2 x
      (⟨hx.1.1, hp⟩ : x ∈ C.U r ⊓ B.U p) (⟨hx.2.1, hp⟩ : x ∈ C.U r' ⊓ B.U p)
    have hd2 := gU_div C B (r, p) (r', p) x
      (⟨hx.1.1, hp⟩ : x ∈ C.U r ⊓ B.U p) (⟨hx.2.1, hp⟩ : x ∈ C.U r' ⊓ B.U p)
    have h1 := gU_isGen (i := (p, q)) (j := (p, q')) hw1 x
      (⟨hp, hx.1.2⟩ : x ∈ B.U p ⊓ A.U q) (⟨hp, hx.2.2⟩ : x ∈ B.U p ⊓ A.U q')
    have hd1 := gU_div B A (p, q) (p, q') x
      (⟨hp, hx.1.2⟩ : x ∈ B.U p ⊓ A.U q) (⟨hp, hx.2.2⟩ : x ∈ B.U p ⊓ A.U q')
    have hbb := gU_self hB x hp
    have hd3 := gU_div C A (r, q) (r', q') x hx.1 hx.2
    exact comp_lemma_2 _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 h2 hd2 h1 hd1 hbb hd3
  · intro r q x hx
    obtain ⟨p, hp⟩ := hxB x
    have e := compgerm_lemma w1 w2 r q p (s (r, q)) (hs (r, q) p) x ⟨hx, hp⟩
    have eb := germOfMaps_lemma w1 a b hab p q x ⟨hp, hx.2⟩
    have ec := germOfMaps_lemma w2 b c hbc r p x ⟨hx.1, hp⟩
    exact comp_lemma_3 _ _ _ _ _ _ e eb ec
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
