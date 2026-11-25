-- Prove2me | solution 1 for PI.OmLocU.CntFF.fFInert2_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:40:00.725805+00:00
-- url     : https://prove2.me/submissions/66180ef2-b624-4ab0-91ac-872674cc91f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds
import Theorems.Thm_PI_OmLocU_CntFF_exists_orth2
import Theorems.Thm_PI_OmLocU_CntFF_card_diag2
import Theorems.Thm_PI_OmLocU_CntFF_exists_tr_ne
import Theorems.Thm_PI_VolStabSW_FFHS_card_norm_fiber
import Theorems.Thm_PI_VolStabSW_FFHS_ffH_isHS
import Theorems.Thm_PI_VolStabSW_FFHS_frob_of_ne
import Theorems.Thm_PI_VolStabSW_FFHS_linIndep_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.CntFF
open Module PI.VolStabSW PI.VolStabSW.FFHS
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.OmLocU.CntFF
theorem _root_.solution : FFInert2 := by
  intro k K _ _ _ _ σ hσ hrank hne M a haM J hJ hJd T hT hTd
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI : FiniteDimensional k K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite K := Module.finite_of_finite k
  haveI : Fintype K := Fintype.ofFinite K
  have hq0 : 0 < Fintype.card k := Fintype.card_pos
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), hrank]
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := hσ
  have h2 := exists_tr_ne σ hne
  have hfrob := frob_of_ne σ hrank hne
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Fintype.card k + 1 :=
    fun d hd => card_norm_fiber σ hfrob hrank d hd
  have hTs := ffH_isHS hσ' T hT hTd
  obtain ⟨f, hf1, hf2⟩ := exists_orth2 h2 a (Fin a → K) (ffH (σ : K →+* K) T) hTs
    (Module.finrank_fin_fun K)
  have hPu : IsUnit (Matrix.of f) :=
    (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of f)).mp
      (linIndep_orth hTs.toIsSq f hf1 hf2)
  have hPdet : IsUnit (Matrix.of f).det := (Matrix.isUnit_iff_isUnit_det _).mp hPu
  have hPm : IsUnit ((Matrix.of f).map (σ : K →+* K)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      ((RingHom.map_det (σ : K →+* K) (Matrix.of f)) ▸ hPdet.map (σ : K →+* K))
  have hPt : IsUnit (Matrix.transpose (Matrix.of f)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr ((Matrix.det_transpose (Matrix.of f)).symm ▸ hPdet)
  have hG : ∀ {b c : ℕ} (A : Matrix (Fin c) (Fin c) K) (X : Matrix (Fin b) (Fin c) K),
      ffGram (σ : K →+* K) A X = X.map (σ : K →+* K) * A * Matrix.transpose X := by
    intro b c A X
    ext i j
    simp only [ffGram, ffH, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      Finset.sum_mul]
    exact Finset.sum_comm
  have hD : ∀ i j, ffGram (σ : K →+* K) T (Matrix.of f) i j =
      if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rfl
    · rw [if_neg hij]
      exact hf1 i j hij
  let E : (Fin a → Fin M → K) ≃ (Fin a → Fin M → K) :=
    { toFun := fun X => (Matrix.of f * Matrix.of X : Matrix (Fin a) (Fin M) K)
      invFun := fun Y => ((Matrix.of f)⁻¹ * Matrix.of Y : Matrix (Fin a) (Fin M) K)
      left_inv := fun X => by
        change (Matrix.of f)⁻¹ * (Matrix.of f * Matrix.of X) = Matrix.of X
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPdet, Matrix.one_mul]
      right_inv := fun Y => by
        change Matrix.of f * ((Matrix.of f)⁻¹ * Matrix.of Y) = Matrix.of Y
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPdet, Matrix.one_mul] }
  have hiff : ∀ X : Fin a → Fin M → K, ffGram (σ : K →+* K) J X = T ↔
      ∀ i j, ffH (σ : K →+* K) J (E X i) (E X j) =
        if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0 := by
    intro X
    have hG1 : ffGram (σ : K →+* K) J (Matrix.of f * Matrix.of X) =
        (Matrix.of f).map (σ : K →+* K) * ffGram (σ : K →+* K) J X * Matrix.transpose (Matrix.of f) := by
      rw [hG J (Matrix.of f * Matrix.of X), hG J X, Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      try rfl
    have hD' : ffGram (σ : K →+* K) T (Matrix.of f) =
        (Matrix.of f).map (σ : K →+* K) * T * Matrix.transpose (Matrix.of f) := hG T (Matrix.of f)
    constructor
    · intro hX i j
      have h3 : ffGram (σ : K →+* K) J (Matrix.of f * Matrix.of X) =
          ffGram (σ : K →+* K) T (Matrix.of f) := by
        rw [hG1, hX, hD']
      exact (congrFun (congrFun h3 i) j).trans (hD i j)
    · intro hY
      have h3 : ffGram (σ : K →+* K) J (Matrix.of f * Matrix.of X) =
          ffGram (σ : K →+* K) T (Matrix.of f) := by
        ext i j
        exact (hY i j).trans (hD i j).symm
      rw [hG1, hD'] at h3
      exact hPm.mul_left_cancel (hPt.mul_right_cancel h3)
  have hcd := card_diag2 (Fintype.card k) hq0 hK hσ' h2 hN a M haM (Fin M → K)
    (ffH (σ : K →+* K) J) (ffH_isHS hσ' J hJ hJd) (Module.finrank_fin_fun K)
    (fun i => ffH (σ : K →+* K) T (f i) (f i))
    (fun i => (hTs.herm (f i) (f i)).symm) (fun i => hf2 i)
  have hE : {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} ≃
      {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0} :=
    E.subtypeEquiv hiff
  rw [Nat.card_congr hE]
  rw [hcd]
  rw [Nat.card_eq_fintype_card]
end PI.OmLocU.CntFF
