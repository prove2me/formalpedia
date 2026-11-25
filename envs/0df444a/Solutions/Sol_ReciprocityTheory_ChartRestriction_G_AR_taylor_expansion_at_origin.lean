-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:15:27.006746+00:00
-- url     : https://prove2.me/submissions/0dec58da-6168-4592-9407-6f3c566a4348

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_multilinear_diagonal_homogeneous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isBigO_pow_of_iteratedFDeriv_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_iteratedFDeriv_eq_zero_of_isBigO_alt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_zd_iteratedFDeriv_comp_perm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR
open Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR
theorem _root_.solution {n a : ℕ} (G : V n → ℂ) (U : Set (V n)) (hU : IsOpen U) (h0 : (0 : V n) ∈ U)
    (hG : DifferentiableOn ℂ G U) (hO : G =O[𝓝 0] fun u => ‖u‖ ^ a) :
    ∃ b : (Fin n → ℕ) → ℂ,
      (fun u => G u - ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, u k ^ α k)
        =O[𝓝 0] fun u => ‖u‖ ^ (a + 1) := by
  have hc : ContDiffOn ℂ ∞ G U := contDiffOn_of_differentiableOn n G U hU hG
  set D := iteratedFDeriv ℂ a G 0 with hD
  set M := (a.factorial : ℂ)⁻¹ • D with hM
  obtain ⟨b, hb⟩ := multilinear_diagonal_homogeneous M
  refine ⟨b, ?_⟩
  set p : V n → ℂ := fun u => M (fun _ => u) with hp
  have hpc : ContDiff ℂ ∞ p := M.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
  have hpO : p =O[𝓝 0] fun u => ‖u‖ ^ a := by
    refine IsBigO.of_bound ‖M‖ (Eventually.of_forall fun u => ?_)
    rw [norm_pow, norm_norm]
    have := M.le_opNorm (fun _ => u)
    simpa [Finset.prod_const] using this
  set H : V n → ℂ := fun u => G u - p u with hH
  have hHc : ContDiffOn ℂ ∞ H U := hc.sub hpc.contDiffOn
  have hHO : H =O[𝓝 0] fun u => ‖u‖ ^ a := hO.sub hpO
  have hcG : ContDiffAt ℂ a G 0 := (hc.contDiffAt (hU.mem_nhds h0)).of_le (by exact_mod_cast le_top)
  have hcp : ContDiffAt ℂ a p 0 := hpc.contDiffAt.of_le (by exact_mod_cast le_top)
  have hpa : iteratedFDeriv ℂ a p 0 = D := by
    ext v
    rw [hp, M.iteratedFDeriv_comp_diagonal]
    have hs : ∀ σ : Equiv.Perm (Fin a), M (fun i => v (σ i)) = M v := by
      intro σ
      simp only [hM, ContinuousMultilinearMap.smul_apply]
      congr 1
      exact zd_iteratedFDeriv_comp_perm hU hc a 0 h0 σ v
    rw [Finset.sum_congr rfl (fun σ _ => hs σ), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, hM, ContinuousMultilinearMap.smul_apply, nsmul_eq_mul,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos a).ne'), one_mul]
  have hzero : ∀ k < a + 1, iteratedFDeriv ℂ k H 0 = 0 := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      exact iteratedFDeriv_eq_zero_of_isBigO_alt m H U 0 hU h0 hHc (by simpa using hHO) k (by omega)
    · rw [hH, show (fun u => G u - p u) = G - p from rfl, iteratedFDeriv_sub_apply hcG hcp, hpa,
        sub_self]
  have := isBigO_pow_of_iteratedFDeriv_zero (a + 1) H U 0 hU h0 hHc hzero
  refine (this.congr_left fun u => ?_).congr_right fun u => by rw [sub_zero]
  simp only [hH, hp, hb]
end ReciprocityTheory.ChartRestriction.G.AR
