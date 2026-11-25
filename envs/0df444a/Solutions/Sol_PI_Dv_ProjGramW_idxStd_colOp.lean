-- Prove2me | solution 1 for PI.Dv.ProjGramW.idxStd_colOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:15:04.339156+00:00
-- url     : https://prove2.me/submissions/187fea65-6ce6-4000-890c-f6111b98c50b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_span_O_famC
import Theorems.Thm_PI_Dv_ProjGramW_idx_self
import Theorems.Thm_PI_Dv_ProjGramW_famC_std_apply
import Theorems.Thm_PI_Dv_ProjGramW_sums_eq
import Theorems.Thm_PI_Dv_ProjGramW_std_sum_at
import Theorems.Thm_PI_Dv_ProjGramW_col_sum_at
import Theorems.Thm_PI_Dv_ProjGramW_algebraMap_eq_zero
import Theorems.Thm_PI_Dv_ProjGramW_span_single_fam
import Theorems.Thm_PI_Dv_ProjGramW_idx_rank_one
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (j0 : Fin d) (v : Fin d → K)
    (hv : v j0 ≠ 0) (hdet : (colOp j0 v).det ≠ 0) : idxStd w (colOp j0 v) = vAdd w (v j0) := by
  classical
  set M := Submodule.span (𝓞 K) (Set.range (stdE (K := K) d)) with hM
  set N := Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) (colOp j0 v))) with hN
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range _)
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span K (M : Set (Fin d →₀ K)) = Submodule.span K (N : Set (Fin d →₀ K)) :=
    (span_O_famC (V := Fin d →₀ K) _ _ hdet).symm
  set φ : (Fin d →₀ K) →ₗ[K] K := Finsupp.lapply j0 with hφ
  have h3 := (hI K (Fin d →₀ K) w M N hMfg hNfg hsp).2.2.1 K φ
  have hkeq : M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) := by
    ext x
    constructor
    · rintro ⟨hxM, hx0⟩
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hxM
      have h0 : (∑ k, r k • stdE (K := K) d k) j0 = 0 := hx0
      rw [std_sum_at] at h0
      have hr0 := algebraMap_eq_zero h0
      refine ⟨?_, hx0⟩
      rw [← sums_eq j0 v r hr0]
      exact (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨r, rfl⟩
    · rintro ⟨hxN, hx0⟩
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hxN
      have h0 : (∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k) j0 = 0 := hx0
      rw [col_sum_at] at h0
      have hr0 : r j0 = 0 :=
        algebraMap_eq_zero ((mul_eq_zero.mp h0).resolve_right hv)
      refine ⟨?_, hx0⟩
      rw [sums_eq j0 v r hr0]
      exact (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨r, rfl⟩
  have hm1 : M.map (φ.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) {(1 : K)} := by
    rw [hM, Submodule.map_span, ← Set.range_comp]
    rw [span_single_fam j0 _ (fun k hk => by simp [hφ, stdE, hk])]
    simp [hφ, stdE]
  have hm2 : N.map (φ.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) {v j0} := by
    rw [hN, Submodule.map_span, ← Set.range_comp]
    rw [span_single_fam j0 _ (fun k hk => by
      simp only [Function.comp_apply, LinearMap.restrictScalars_apply, hφ, Finsupp.lapply_apply]
      rw [famC_std_apply]; simp [colOp, hk, Ne.symm hk])]
    simp only [Function.comp_apply, LinearMap.restrictScalars_apply, hφ, Finsupp.lapply_apply]
    rw [famC_std_apply]
    simp [colOp]
  have hkfg : (N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)).FG := Submodule.FG.of_le hNfg inf_le_left
  unfold idxStd
  rw [h3, hkeq, idx_self hI w hkfg, zero_add, hm1, hm2]
  exact idx_rank_one hI w hv
end PI.Dv.ProjGramW
