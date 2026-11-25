-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_th__a85f9d38c14f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:41:19.290803+00:00
-- url     : https://prove2.me/submissions/f02793d8-854a-4b75-b61f-b480e6b239ec

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil

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
private theorem comp_psum_lemma {T T' : Over Xo.X} (f : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G))
    (S : Finset (Fin n)) :
    f ≫ psum Xo.univ.t.G xs S = psum Xo.univ.t.G (fun i => f ≫ xs i) S := by
  unfold psum
  generalize (List.finRange n).filter (· ∈ S) = L
  induction L with
  | nil =>
    simp only [List.foldr_nil, pzero]
    first
      | simp
      | rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
  | cons k L ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    simp only [padd]
    first
      | rw [CartesianMonoidalCategory.comp_lift_assoc]
      | simp
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
theorem _root_.solution {T T' : Over Xo.X} (f : T' ⟶ T) (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) (I : thK) :
    f.left ≫ thφ Xo.univ.t.G xs I = thφ Xo.univ.t.G (fun i => f ≫ xs i) I := by
  simp only [thφ]
  rw [← Over.comp_left, comp_psum_lemma]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
