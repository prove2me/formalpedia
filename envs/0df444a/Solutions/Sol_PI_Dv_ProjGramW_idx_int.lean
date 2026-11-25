-- Prove2me | solution 1 for PI.Dv.ProjGramW.idx_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:17.126446+00:00
-- url     : https://prove2.me/submissions/ea94eb92-0690-4f6f-93d4-c549d5e3676e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_idx_add
import Theorems.Thm_PI_Dv_ProjGramW_algebraMap_eq_zero
import Theorems.Thm_PI_Dv_ProjGramW_span_top_of_mem
import Theorems.Thm_PI_Dv_ProjGramW_one_not_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_ProjGramW_idx_eq_zero_of_loc
import Theorems.Thm_PI_Dv_ProjGramW_locLe_zero_iff
import Theorems.Thm_PI_Dv_ProjGramW_vAdd_algebraMap_nonneg
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
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) {r : 𝓞 K} (hr : r ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) {y}) (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r * y}) =
      vAdd w (algebraMap (𝓞 K) K r) := by
  classical
  have hv0 := vAdd_algebraMap_nonneg w r
  set F : ℕ := (vAdd w (algebraMap (𝓞 K) K r)).toNat with hFdef
  have hF : (F : ℤ) = vAdd w (algebraMap (𝓞 K) K r) := Int.toNat_of_nonneg hv0
  have hne := w.intValuation_ne_zero r hr
  have hval : w.intValuation r = WithZero.exp (-(F : ℤ)) := by
    rw [hF]
    unfold vAdd
    rw [HeightOneSpectrum.valuation_of_algebraMap, neg_neg, WithZero.exp_log hne]
  have hmem : r ∈ w.asIdeal ^ F := (w.intValuation_le_pow_iff_mem r F).mp (le_of_eq hval)
  obtain ⟨J, hJ⟩ := (w.intValuation_le_pow_iff_dvd r F).mp (le_of_eq hval)
  have hJw : ¬ J ≤ w.asIdeal := by
    intro hle
    have hd : w.asIdeal ^ (F + 1) ∣ Ideal.span {r} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have := (w.intValuation_le_pow_iff_dvd r (F + 1)).mpr hd
    rw [hval, WithZero.exp_le_exp] at this
    push_cast at this
    linarith
  obtain ⟨t, htJ, htw⟩ := SetLike.not_le_iff_exists.mp hJw
  set X := Submodule.span (𝓞 K) {y} with hX
  set Y := Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r * y} with hY
  set Z := (w.asIdeal ^ F) • X with hZ
  have hry : algebraMap (𝓞 K) K r * y = r • y := (Algebra.smul_def r y).symm
  have hry0 : algebraMap (𝓞 K) K r * y ≠ 0 :=
    mul_ne_zero (fun h => hr (algebraMap_eq_zero h)) hy
  have hyX : y ∈ X := Submodule.mem_span_singleton_self y
  have hryZ : algebraMap (𝓞 K) K r * y ∈ Z := by
    rw [hry]; exact Submodule.smul_mem_smul hmem hyX
  have hXfg : X.FG := Submodule.fg_span (Set.finite_singleton _)
  have hYfg : Y.FG := Submodule.fg_span (Set.finite_singleton _)
  have hZfg : Z.FG := Submodule.FG.of_le hXfg Submodule.smul_le_right
  have hsX : Submodule.span K (X : Set K) = ⊤ := span_top_of_mem hyX hy
  have hsY : Submodule.span K (Y : Set K) = ⊤ := span_top_of_mem (Submodule.mem_span_singleton_self _) hry0
  have hsZ : Submodule.span K (Z : Set K) = ⊤ := span_top_of_mem hryZ hry0
  have hYZ : LocLe w 0 Y Z := by
    rw [locLe_zero_iff]
    intro z hz
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨1, one_not_mem w, ?_⟩
    rw [one_smul, hry, smul_smul]
    exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ m hmem) hyX
  have hZY : LocLe w 0 Z Y := by
    rw [locLe_zero_iff]
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Submodule.mem_smul_span_singleton.mp hz
    have hit : i * t ∈ Ideal.span {r} := by rw [hJ]; exact Ideal.mul_mem_mul hi htJ
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hit
    refine ⟨t, htw, ?_⟩
    have e : t • i • y = m • (algebraMap (𝓞 K) K r * y) := by
      rw [hry, smul_smul, smul_smul, hm, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ m (Submodule.mem_span_singleton_self _)
  have hrk : Formalism.HN.rkK X = 1 := by
    unfold Formalism.HN.rkK
    rw [hsX, finrank_top, Module.finrank_self]
  have h5 := (hI K K w X X hXfg hXfg rfl).2.2.2.2.1 F
  have hadd := idx_add hI w hXfg hZfg hYfg (hsX.trans hsZ.symm) (hsY.trans hsZ.symm)
  have h0 := idx_eq_zero_of_loc hI w hZfg hYfg hZY hYZ
  rw [hadd, h5, h0, hrk, ← hF]
  simp
end PI.Dv.ProjGramW
