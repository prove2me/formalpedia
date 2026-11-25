-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.phla_kapW_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:11.541694+00:00
-- url     : https://prove2.me/submissions/a58913c0-fc73-45f0-b525-c2d06ec984a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_log_densF_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_sbp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_Lm_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_Lm_last_cpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    phla X (kapW X) (cpt X x0 z) = Real.log (densF X x0 z) := by
  have hx : cpt X x0 z ∈ X.dom := hz
  rw [phla_eq X hx, log_densF_eq X x0 hz]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℝ,
      L = fun n => if h : n < r + 1 then Lm X (cpt X x0 z) τ ⟨n, h⟩ else 0 := ⟨_, rfl⟩
  have h1 : ∀ i : Fin r, Lm X (cpt X x0 z) τ i.succ = L ((i : ℕ) + 1) := fun i => by
    rw [hL]
    dsimp only
    rw [dif_pos (show (i : ℕ) + 1 < r + 1 by have := i.isLt; omega)]
    try rfl
  have h2 : ∀ i : Fin r, Lm X (cpt X x0 z) τ i.castSucc = L (i : ℕ) := fun i => by
    rw [hL]
    dsimp only
    rw [dif_pos (show (i : ℕ) < r + 1 by have := i.isLt; omega)]
    try rfl
  have hk : ∀ i : Fin r, ((kapW X τ i : ℤ) : ℝ) = (2 * (i : ℕ) : ℝ) - ((r : ℝ) - 1) := fun i => by
    simp only [kapW]
    push_cast
    try ring
  have hr : L r = 0 := by
    rw [hL]
    dsimp only
    rw [dif_pos (show r < r + 1 by omega)]
    exact Lm_last_cpt X x0 ho z τ
  have e0 : (⟨0, Nat.succ_pos r⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
  have h0 : L 0 = 0 := by
    rw [hL]
    dsimp only
    rw [dif_pos (show 0 < r + 1 by omega), e0]
    exact Lm_zero X _ τ
  simp only [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((2 * i : ℝ) - ((r : ℝ) - 1)) * (L (i + 1) - L i)) r,
    Fin.sum_univ_eq_sum_range (fun i => (-2) * L i) r, sbp L r, hr, h0, ← Finset.mul_sum]
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
