-- Prove2me | solution 1 for SNumbers.L1Linf.half_le_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:27:15.136458+00:00
-- url     : https://prove2.me/submissions/7f820414-a0e9-430c-b6d7-61c3f043080d

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
public import Theorems.Thm_SNumbers_L1Linf_incl_apply
public import Theorems.Thm_SNumbers_L1Linf_norm_incl_le
public import Theorems.Thm_SNumbers_L1Linf_e_apply_self
public import Theorems.Thm_SNumbers_L1Linf_e_apply_ne
public import Theorems.Thm_SNumbers_L1Linf_norm_e
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_deviationFromRestriction_nonneg
public import Theorems.Thm_SNumbers_le_gelfandNumber
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_signedSum_empty
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] SNumbers.signedSum_empty
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.L1Linf.incl_apply
attribute [local simp] SNumbers.L1Linf.e_apply_self

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (n : ℕ) :
    (1 : ℝ) / 2 ≤ gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by
  refine le_gelfandNumber (fun N hN_closed hN_rank => ?_)
  have : FiniteDimensional 𝕜 (L1 𝕜 ⧸ N) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hN_rank (Cardinal.natCast_lt_aleph0))
  have : ProperSpace (L1 𝕜 ⧸ N) := FiniteDimensional.proper 𝕜 _
  set D : ℝ := deviationFromRestriction (incl : L1 𝕜 →L[𝕜] Linf 𝕜) N with hD
  have hD_nn : 0 ≤ D := deviationFromRestriction_nonneg _ _
  -- Operator-norm bound on the restriction: `‖I x‖ ≤ D · ‖x‖` for `x ∈ N`.
  have hopbound : ∀ x : L1 𝕜, x ∈ N →
      ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ ≤ D * ‖x‖ := by
    intro x hx
    have h := ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp N.subtypeL).le_opNorm (⟨x, hx⟩ : N)
    rwa [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h
  -- Key ratio estimate for every `ε' > 0`.
  have key : ∀ ε' : ℝ, 0 < ε' → 1 - 2 * ε' ≤ D * (2 + 2 * ε') := by
    intro ε' hε'
    set g : ℕ → L1 𝕜 ⧸ N := fun i => Submodule.Quotient.mk (e i) with hg
    have hg_bdd : ∀ i, g i ∈ Metric.closedBall (0 : L1 𝕜 ⧸ N) 1 := by
      intro i
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖g i‖ ≤ ‖(e i : L1 𝕜)‖ := Submodule.Quotient.norm_mk_le N (e i)
        _ = 1 := norm_e i
    obtain ⟨a, -, φ, hφ_mono, hφ_tendsto⟩ :=
      tendsto_subseq_of_bounded Metric.isBounded_closedBall hg_bdd
    rw [Metric.tendsto_atTop] at hφ_tendsto
    obtain ⟨K, hK⟩ := hφ_tendsto (ε' / 2) (by positivity)
    have hi_ne : φ K ≠ φ (K + 1) := (hφ_mono (Nat.lt_succ_self K)).ne
    have hclose : dist (g (φ K)) (g (φ (K + 1))) < ε' := by
      calc dist (g (φ K)) (g (φ (K + 1)))
          ≤ dist (g (φ K)) a + dist a (g (φ (K + 1))) := dist_triangle _ _ _
        _ = dist (g (φ K)) a + dist (g (φ (K + 1))) a := by rw [dist_comm a]
        _ < ε' / 2 + ε' / 2 := add_lt_add (hK K (le_refl _)) (hK (K + 1) (Nat.le_succ _))
        _ = ε' := by ring
    set d : L1 𝕜 := e (φ K) - e (φ (K + 1)) with hd_def
    have hmk_small : ‖(Submodule.Quotient.mk d : L1 𝕜 ⧸ N)‖ < ε' := by
      have hmk_eq : (Submodule.Quotient.mk d : L1 𝕜 ⧸ N) = g (φ K) - g (φ (K + 1)) := by
        rw [hg, hd_def, Submodule.Quotient.mk_sub]
      rw [hmk_eq, ← dist_eq_norm]; exact hclose
    obtain ⟨y, hy_mk, hy_lt⟩ :=
      Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk d : L1 𝕜 ⧸ N) hε'
    set x : L1 𝕜 := d - y with hx_def
    have hx_mem : x ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, hx_def, Submodule.Quotient.mk_sub, hy_mk, sub_self]
    have hy_2 : ‖y‖ < 2 * ε' := by linarith [hy_lt, hmk_small]
    have hx_l1 : ‖x‖ ≤ 2 + 2 * ε' := by
      calc ‖x‖ = ‖d - y‖ := by rw [hx_def]
        _ ≤ ‖d‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ (‖(e (φ K) : L1 𝕜)‖ + ‖(e (φ (K + 1)) : L1 𝕜)‖) + ‖y‖ := by
            gcongr; rw [hd_def]; exact norm_sub_le _ _
        _ ≤ (1 + 1) + 2 * ε' := by rw [norm_e, norm_e]; linarith [hy_2]
        _ = 2 + 2 * ε' := by ring
    have hx_linf : 1 - 2 * ε' ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := by
      have hcoord : ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) d) (φ K) = (1 : 𝕜) := by
        rw [incl_apply, hd_def]
        simp only [lp.coeFn_sub, Pi.sub_apply, e_apply_self, e_apply_ne hi_ne, sub_zero]
      have h_incl_d : (1 : ℝ) ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d‖ := by
        have hb := lp.norm_apply_le_norm (show (∞ : ℝ≥0∞) ≠ 0 by simp)
          ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) d) (φ K)
        rwa [hcoord, norm_one] at hb
      have h_incl_y : ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ ≤ ‖y‖ :=
        ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).le_opNorm y).trans
          (mul_le_of_le_one_left (norm_nonneg y) norm_incl_le)
      have hxeq : (incl : L1 𝕜 →L[𝕜] Linf 𝕜) x
          = (incl : L1 𝕜 →L[𝕜] Linf 𝕜) d - (incl : L1 𝕜 →L[𝕜] Linf 𝕜) y := by
        rw [hx_def, map_sub]
      calc 1 - 2 * ε'
          ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d‖ - ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ := by
            linarith [h_incl_d, h_incl_y, hy_2]
        _ ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d - (incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ :=
            norm_sub_norm_le _ _
        _ = ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := by rw [hxeq]
    calc 1 - 2 * ε'
        ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := hx_linf
      _ ≤ D * ‖x‖ := hopbound x hx_mem
      _ ≤ D * (2 + 2 * ε') := mul_le_mul_of_nonneg_left hx_l1 hD_nn
  -- Let `ε' → 0`.
  show (1 : ℝ) / 2 ≤ D
  have h2D : (1 : ℝ) ≤ 2 * D := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have h1D : (0 : ℝ) < 1 + D := by linarith
    set ε' : ℝ := δ / (2 * (1 + D)) with hε'_def
    have hε'_pos : 0 < ε' := by positivity
    have hk := key ε' hε'_pos
    have hδeq : 2 * ε' * (1 + D) = δ := by
      rw [hε'_def]; field_simp
    nlinarith [hk, hδeq]
  linarith
end SNumbers.L1Linf
