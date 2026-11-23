-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.maps_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:53.445024+00:00
-- url     : https://prove2.me/submissions/aa03341f-7c87-4c28-8adf-25c0f48a79b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
section Stalk
variable {X Y Z : Scheme.{0}}
variable {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
private theorem mem_wchart_lemma {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (x : Y) : x ∈ LB.wchart L φ j ↔ ∀ k, φ k x ∈ L.U (j k) := by
  simp [LB.wchart]
private theorem gm_lin_lemma_2 (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Z Y' : Scheme.{0}}
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (P : K → PUnit → L.ι) (q : K → L'.ι)
    (hz : r z ∈ LB.wchart (L.pull F) φ' P ⊓ LB.wchart L' φ' q) :
    gm r z (LB.wchart (L.pull F) φ' P ⊓ LB.wchart L' φ' q) ((LB.linCombIso w φ' ε).s (P, q)) =
      ∏ k, gw w (r ≫ φ' k) z (P k PUnit.unit) (q k) ^ ε k := by
  dsimp only [LB.linCombIso]
  refine (map_prod (gm r z (LB.wchart (L.pull F) φ' P ⊓ LB.wchart L' φ' q)) _ _).trans ?_
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (map_zpow _ _ _).trans ?_
  congr 1
  have hk : r z ∈ φ' k ⁻¹ᵁ ((L.pull F).U (P k) ⊓ L'.U (q k)) :=
    ⟨(mem_wchart_lemma _ _ _ _).1 hz.1 k, (mem_wchart_lemma _ _ _ _).1 hz.2 k⟩
  erw [gm_res r z _ hz]
  exact gm_pull r (φ' k) z ((L.pull F).U (P k) ⊓ L'.U (q k)) hk (w.s (P k, q k))
end Stalk
section Tri
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
variable {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')}
  {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L' φ' ε)} {t'' : LB.Gen (LB.LinComb L'' φ'' ε)}
  {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
end Tri
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
variable {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (b : LB.Gen (LB.LinComb (L.pull F) φ' ε))
    (hle : ∀ j : K → PUnit → L.ι, LB.wchart (L.pull F) φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j k PUnit.unit))
    (hb : ∀ j, b.s j = res (hle j) (pullU h _ (t.s (fun k => j k PUnit.unit)))) :
    LB.Gen.Maps (LB.linCombIso w φ' ε) a b ↔ PMaps w φ' φ ε a t h := by
  constructor
  · intro hM Z r z p q hp hq
    have hz : r z ∈ LB.wchart (L.pull F) φ' (fun k _ => p k) ⊓ LB.wchart L' φ' q :=
      ⟨(mem_wchart_lemma _ _ _ _).2 fun k => mem_pull (J := fun _ => p k) |>.2 (hp k),
        (mem_wchart_lemma _ _ _ _).2 hq⟩
    have e := congrArg (gm r z _) (hM ((fun k _ => p k), q))
    erw [map_mul, gm_res r z _ hz, hb, gm_res r z _ hz.1, gm_pull r h z _ (hle _ hz.1),
      gm_lin_lemma_2 w φ' ε r z _ q hz, gm_res r z _ hz] at e
    exact e
  · intro hP p
    apply unit_ext
    intro x hx
    have e := hP Y' (𝟙 Y') x (fun k => p.1 k PUnit.unit) p.2
      (fun k => mem_pull.1 ((mem_wchart_lemma _ _ _ _).1 hx.1 k)) ((mem_wchart_lemma _ _ _ _).1 hx.2)
    erw [map_mul, gm_res _ x _ hx, hb, gm_res _ x _ hx.1, gm_pull _ h x _ (hle _ hx.1),
      gm_lin_lemma_2 w φ' ε (𝟙 Y') x p.1 p.2 hx, gm_res _ x _ hx]
    exact e
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
