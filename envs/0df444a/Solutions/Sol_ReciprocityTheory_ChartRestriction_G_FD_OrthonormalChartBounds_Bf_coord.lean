-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:19.88834+00:00
-- url     : https://prove2.me/submissions/e0ec698a-10e5-46d7-a2fc-eefd922f879c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BfSubRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Lv_p
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Lv_n
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma sum_eq_sum_castLE_p0_add_sum_nI (g : Fin r → ℂ) :
    ∑ c, g c = ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) + ∑ m, g (nI X m) := by
  have hr : X.p0 + (r - X.p0) = r := Nat.add_sub_cancel' X.p0_le
  rw [← Fintype.sum_equiv (finCongr hr) (fun i => g (finCongr hr i)) g (fun _ => rfl),
    Fin.sum_univ_add]
  rfl
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) :
    Bf X Z τ v w = ∑ a, Pv X v a * conj (Pv X w a) - ∑ m, Nv X Z τ v m * conj (Nv X Z τ w m) := by
  have hG : ∀ a b, Gp X Z τ a b =
      ∑ c : Fin r, X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * conj (X.lowBlock Z τ c b) := by
    intro a b
    simp [Gp, Matrix.mul_apply, Matrix.diagonal_apply]
  have h1 : Bf X Z τ v w = ∑ c : Fin r, ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (∑ a, X.lowBlock Z τ c a * v a) *
      conj (∑ b, X.lowBlock Z τ c b * w b) := by
    calc Bf X Z τ v w = ∑ a, ∑ b, ∑ c : Fin r, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) := by
          unfold Bf
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [hG, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ a, ∑ c : Fin r, ∑ b, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c : Fin r, ∑ a, ∑ b, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [map_mul]
          ring
  rw [h1, sum_eq_sum_castLE_p0_add_sum_nI X, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Lv_p X, Lv_p X]
    simp [sgn, Pv]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Lv_n X, Lv_n X]
    simp [sgn, nI]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
