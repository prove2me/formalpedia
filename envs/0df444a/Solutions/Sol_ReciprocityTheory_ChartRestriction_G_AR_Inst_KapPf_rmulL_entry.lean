-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.rmulL_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:27.540817+00:00
-- url     : https://prove2.me/submissions/e917428c-4113-4495-a81b-abfdb1c146b4

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
theorem _root_.solution (b : Frame X.Ψ r) (e e' : Ent X) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Ent X)) (Pi.basisFun ℂ (Ent X)) (rmulL X b) e e' =
      if e.1 = e'.1 ∧ e.2.1.1 = e'.2.1.1 then b e.1 e'.2.1.2 e.2.1.2 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  show ∑ y, embF X (Pi.single e' 1) e.1 e.2.1.1 y * b e.1 y e.2.1.2 = _
  simp only [embF_single, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single e'.2.1.2]
    · rw [if_pos ⟨h.1, h.2, rfl⟩]
    · intro y _ hy
      rw [if_neg]
      exact fun h' => hy h'.2.2
    · simp
  · refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨h'.1, h'.2.1⟩
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
