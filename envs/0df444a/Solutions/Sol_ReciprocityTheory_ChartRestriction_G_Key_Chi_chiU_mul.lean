-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:43.764939+00:00
-- url     : https://prove2.me/submissions/91e1fe25-6850-40e1-8758-ceb8dbda9940

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_det_jAut_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_expArg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_A
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_zAct_mul
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} {x y : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hx : x ∈ Matrix.symplecticGroup (Fin g) ℤ) (hy : y ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (Hx : ChiAtU g x) (Hy : ChiAtU g y) : ChiAtU g (x * y) := by
  intro n n'
  obtain ⟨k, k', c, hc, H⟩ := Hy n n'
  obtain ⟨m, m', c', hc', H'⟩ := Hx k k'
  refine ⟨m, m', c' * c, by rw [mul_pow, hc, hc', one_mul], ?_⟩
  intro τ hτ z
  obtain ⟨hj, hs⟩ := spAct_holds g y hy τ hτ
  have hj' := (spAct_holds g x hx _ hs).1
  have hA := sp_A hy hτ.1 hj
  rw [zAct_mul x y τ hj, spAct_mul x y τ hj, H' _ hs, H τ hτ z, det_jAut_mul x y τ hj,
    expArg_mul x y τ hj hj' hA, eC_add]
  ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi
