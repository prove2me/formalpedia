-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.lmulL_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:09.642274+00:00
-- url     : https://prove2.me/submissions/45e7a862-0098-419d-b9d8-e2fdec7da96d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_embF_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
theorem _root_.solution (N : Frame X.Ψ r) (e e' : Ent X) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Ent X)) (Pi.basisFun ℂ (Ent X)) (lmulL X N) e e' =
      if e.1 = e'.1 ∧ e.2.1.2 = e'.2.1.2 then N e.1 e.2.1.1 e'.2.1.1 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  show ∑ x, N e.1 e.2.1.1 x * embF X (Pi.single e' 1) e.1 x e.2.1.2 = _
  simp only [embF_single, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single e'.2.1.1]
    · rw [if_pos ⟨h.1, rfl, h.2⟩]
    · intro x _ hx
      rw [if_neg]
      exact fun h' => hx h'.2.1
    · simp
  · refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨h'.1, h'.2.2⟩
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
