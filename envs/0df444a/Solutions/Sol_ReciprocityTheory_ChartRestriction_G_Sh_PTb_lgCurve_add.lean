-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:36:27.659558+00:00
-- url     : https://prove2.me/submissions/a53d1bdc-abba-4928-92f1-3a740156e0f8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_hasSubst_F
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
private theorem hs_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact hasSubst_of_constantCoeff_zero ha0
  | exact HasSubst.of_constantCoeff_zero' ha0
  | exact hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
  | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) {ga gb : Fin d → PowerSeries C}
    (ha : ∀ b, PowerSeries.constantCoeff (ga b) = 0)
    (hb : ∀ b, PowerSeries.constantCoeff (gb b) = 0) (a : Fin d) :
    G.lgCurve (G.add ga gb) a = G.lgCurve ga a + G.lgCurve gb a := by
  have hE0 : ∀ s, constantCoeff (Sum.elim ga gb s) = 0 := by
    rintro (s | s)
    · exact ha s
    · exact hb s
  have hE : HasSubst (Sum.elim ga gb) := hs_lemma_2 hE0
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma_2 (fun b => constantCoeff_X _)
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma_2 (fun b => constantCoeff_X _)
  show subst (fun b => subst (Sum.elim ga gb) (G.F b)) (G.lg a) =
    subst ga (G.lg a) + subst gb (G.lg a)
  rw [← subst_comp_subst_apply (hasSubst_F G) hE, G.lg_F a, subst_add hE,
    subst_comp_subst_apply hl hE, subst_comp_subst_apply hr hE]
  simp only [subst_X hE, Sum.elim_inl, Sum.elim_inr]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
