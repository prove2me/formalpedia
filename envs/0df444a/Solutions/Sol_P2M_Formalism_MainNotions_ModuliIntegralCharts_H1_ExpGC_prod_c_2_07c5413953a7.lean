-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_prod_c_2_07c5413953a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:02.722809+00:00
-- url     : https://prove2.me/submissions/2df6fc68-b71d-4ea0-84f9-a4c85c222d2a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
private theorem padd_eq_lemma_2 {T : Over Xo.X} (a b : T ⟶ Xo.univ.t.G) :
    padd Xo.univ.t.G a b = a * b := rfl
private theorem pzero_eq_lemma_3 (T : Over Xo.X) : pzero Xo.univ.t.G T = 1 := rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
set_option maxHeartbeats 800000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
theorem _root_.solution {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 2 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : ULift (Finset (Fin 2)), h (cφ xs I) ^ cε 2 I =
      h (1 : T ⟶ Xo.univ.t.G).left * (h (xs 0 * 1).left)⁻¹ * (h (xs 1 * 1).left)⁻¹ * h (xs 0 * (xs 1 * 1)).left := by
  have hsum : ∀ F : ULift (Finset (Fin 2)) → U,
      ∏ I : ULift (Finset (Fin 2)), F I = ∏ s : Finset (Fin 2), F (ULift.up s) :=
    fun F => Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)
  have hU : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have f0 : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  have f1 : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  have f2 : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  have f3 : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  have c3 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  rw [hsum, hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [cφ, cε, psum, f0, f1, f2, f3, c3, List.foldr_cons, List.foldr_nil, padd_eq_lemma_2,
    pzero_eq_lemma_3, Finset.card_empty, Finset.card_singleton]
  clear hsum hU f0 f1 f2 f3 c3
  try norm_num only
  try simp only [zpow_one, zpow_neg, zpow_neg_one]
  rw [mul_assoc (h (Over.Hom.left (1 : T ⟶ Xo.univ.t.G))),
    mul_assoc (h (Over.Hom.left (1 : T ⟶ Xo.univ.t.G))), mul_assoc (h (xs 0 * 1).left)⁻¹]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
