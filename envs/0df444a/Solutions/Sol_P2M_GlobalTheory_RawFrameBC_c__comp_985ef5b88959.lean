-- Prove2me | solution 1 for P2M_GlobalTheory_RawFrameBC_c__comp_985ef5b88959
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:51.376256+00:00
-- url     : https://prove2.me/submissions/8aa01bc4-3db8-4a7d-8785-a5f9c045cc45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RawFrameBC
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)
private theorem padd_lemma_2 {T T' : Over Xo.X} (ρ : T' ⟶ T) (a b : T ⟶ Xo.univ.t.G) :
    ρ ≫ padd Xo.univ.t.G a b = padd Xo.univ.t.G (ρ ≫ a) (ρ ≫ b) := by
  unfold padd
  rw [← Category.assoc, comp_lift]
private theorem pzero_lemma_3 {T T' : Over Xo.X} (ρ : T' ⟶ T) :
    ρ ≫ pzero Xo.univ.t.G T = pzero Xo.univ.t.G T' := by
  unfold pzero
  rw [← Category.assoc]
  congr 1
  exact toUnit_unique _ _
private theorem foldr_lemma_4 {T T' : Over Xo.X} (ρ : T' ⟶ T) {n : ℕ} (v : Fin n → (T ⟶ Xo.univ.t.G))
    (v' : Fin n → (T' ⟶ Xo.univ.t.G)) (hv : ∀ k, v' k = ρ ≫ v k) (l : List (Fin n)) :
    ρ ≫ l.foldr (fun k acc => padd Xo.univ.t.G (v k) acc) (pzero Xo.univ.t.G T) =
      l.foldr (fun k acc => padd Xo.univ.t.G (v' k) acc) (pzero Xo.univ.t.G T') := by
  induction l with
  | nil => exact pzero_lemma_3 ρ
  | cons k l ih => simp only [List.foldr_cons]; rw [padd_lemma_2, ih, hv]
end
end GlobalTheory.RawFrameBC
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawFrameBC
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)
namespace GlobalTheory.RawFrameBC
theorem _root_.solution {T T' : Over Xo.X} (ρ : T' ⟶ T) (a b : T ⟶ Xo.univ.t.G) :
    cφ ![ρ ≫ a, ρ ≫ b] = fun I => ρ.left ≫ cφ ![a, b] I := by
  funext I
  unfold cφ psum
  exact (congrArg Over.Hom.left (foldr_lemma_4 ρ ![a, b] ![ρ ≫ a, ρ ≫ b] (fun k => by fin_cases k <;> rfl) _)).symm
end GlobalTheory.RawFrameBC
