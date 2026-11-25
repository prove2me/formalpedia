-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.placeDecomp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:52:16.966575+00:00
-- url     : https://prove2.me/submissions/a3d867c4-dc89-4a1e-96bc-9a4e6368685f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstPlace
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_Kset_star
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_Jm_single
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_fix_sum
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_col_entry
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_REAL_Jm_mul_self
import Theorems.Thm_Formalism_REAL_ballOpen
import Theorems.Thm_Formalism_REAL_expUJ
import Theorems.Thm_Formalism_REAL_hSBall
import Theorems.Thm_Formalism_REAL_kFacts
import Theorems.Thm_Formalism_REAL_pChar
import Theorems.Thm_Formalism_REAL_polar
import Theorems.Thm_Formalism_REAL_uJEmb
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
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (hE : InstExpFix) (hAB : InstAdaptBasis) : InstPlaceDecomp := by
  intro n ε ι _ _ B hBG g hg hgB
  obtain ⟨A, ε', T, hA, hT1, hT2⟩ := hAB n ε ι B hBG
  have hJ'J' : Formalism.REAL.Jm ε' * Formalism.REAL.Jm ε' = 1 := Formalism.REAL.Jm_mul_self ε'

  have hAdet : IsUnit A.det := by
    have h1 : IsUnit (Aᴴ * Formalism.REAL.Jm ε * A).det := by
      rw [hA]; exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_, _, hJ'J', hJ'J'⟩, rfl⟩
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨Ai, hAi⟩ : ∃ Ai, Ai = A⁻¹ := ⟨_, rfl⟩
  have hAAi : A * Ai = 1 := by rw [hAi]; exact Matrix.mul_nonsing_inv A hAdet
  have hAiA : Ai * A = 1 := by rw [hAi]; exact Matrix.nonsing_inv_mul A hAdet
  have hAiJ : Aiᴴ * Formalism.REAL.Jm ε' * Ai = Formalism.REAL.Jm ε := by
    rw [← hA]
    have h2 : Aiᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hAAi, Matrix.conjTranspose_one]
    calc Aiᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * Ai = (Aiᴴ * Aᴴ) * Formalism.REAL.Jm ε * (A * Ai) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, hAAi, Matrix.one_mul, Matrix.mul_one]
  have tr1 : ∀ m, Formalism.REAL.inUJ ε m → Formalism.REAL.inUJ ε' (Ai * m * A) := by
    intro m hm
    unfold Formalism.REAL.inUJ at *
    have : (Ai * m * A)ᴴ * Formalism.REAL.Jm ε' * (Ai * m * A) =
        Aᴴ * (mᴴ * (Aiᴴ * Formalism.REAL.Jm ε' * Ai) * m) * A := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hAiJ, hm, hA]
  have tr2 : ∀ m, Formalism.REAL.inUJ ε' m → Formalism.REAL.inUJ ε (A * m * Ai) := by
    intro m hm
    unfold Formalism.REAL.inUJ at *
    have : (A * m * Ai)ᴴ * Formalism.REAL.Jm ε * (A * m * Ai) =
        Aiᴴ * (mᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * m) * Ai := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hA, hm, hAiJ]
  have back : ∀ m, (∀ i ∈ T, m *ᵥ Pi.single i 1 = Pi.single i 1) → A * m * Ai * B = B := by
    intro m hm
    refine Matrix.ext_of_mulVec_single fun j => ?_
    obtain ⟨c, hc0, hc⟩ := hT2 j
    simp only [← Matrix.mulVec_mulVec]
    rw [hc, Matrix.mulVec_mulVec c Ai A, hAiA, Matrix.one_mulVec, inst_fix_sum m T hm c hc0]

  obtain ⟨g', hg'def⟩ : ∃ g', g' = Ai * g * A := ⟨_, rfl⟩
  have hg' : Formalism.REAL.inUJ ε' g' := hg'def ▸ tr1 g hg
  have hg'fix : ∀ i ∈ T, g' *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    obtain ⟨c, hc⟩ := hT1 i hi
    rw [hg'def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_mulVec c g B, hgB, ← hc,
      Matrix.mulVec_mulVec, hAiA, Matrix.one_mulVec]

  obtain ⟨k', X', hk', hX', hgkX⟩ := (Formalism.REAL.polar n ε').1 g' hg'
  have hXc := ((Formalism.REAL.pChar n ε' X').1.mp hX')
  have hXh : X'.IsHermitian := hXc.1
  obtain ⟨p', hp'def⟩ : ∃ p', p' = NormedSpace.exp X' := ⟨_, rfl⟩
  rw [← hp'def] at hgkX
  have hk'u : star k' * k' = 1 := Matrix.mem_unitaryGroup_iff'.mp hk'.1
  have hk'u2 : k' * star k' = 1 := Matrix.mem_unitaryGroup_iff.mp hk'.1
  have hp'H : p'ᴴ = p' := by rw [hp'def]; exact hXh.exp
  have hgg : g'ᴴ * g' = NormedSpace.exp (X' + X') := by
    rw [Matrix.exp_add_of_commute X' X' (Commute.refl X'), ← hp'def, hgkX, Matrix.conjTranspose_mul, hp'H,
      ← Matrix.star_eq_conjTranspose]
    calc p' * star k' * (k' * p') = p' * (star k' * k') * p' := by simp only [Matrix.mul_assoc]
      _ = p' * p' := by rw [hk'u, Matrix.mul_one]
  have hgHfix : ∀ i ∈ T, g'ᴴ *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    have h1 := congrArg (fun M => M *ᵥ Pi.single i (1 : ℂ)) hg'
    simp only [← Matrix.mulVec_mulVec, hg'fix i hi, inst_Jm_single, Matrix.mulVec_smul] at h1
    have hs : (if ε' i then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
    exact smul_right_injective _ hs h1
  have hXfix : ∀ i ∈ T, X' *ᵥ Pi.single i 1 = 0 := by
    intro i hi
    have h2 : NormedSpace.exp (X' + X') *ᵥ Pi.single i 1 = Pi.single i 1 := by
      rw [← hgg, ← Matrix.mulVec_mulVec, hg'fix i hi, hgHfix i hi]
    have h3 := (hE n (X' + X') (hXh.add hXh) _).mp h2
    have h4 : (2 : ℂ) • (X' *ᵥ Pi.single i 1) = 0 := by rw [two_smul, ← Matrix.add_mulVec]; exact h3
    exact (smul_eq_zero.mp h4).resolve_left two_ne_zero
  have hpfix : ∀ i ∈ T, p' *ᵥ Pi.single i 1 = Pi.single i 1 := fun i hi => by
    rw [hp'def]; exact (hE n X' hXh _).mpr (hXfix i hi)
  have hkfix : ∀ i ∈ T, k' *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    have h1 := hg'fix i hi
    rw [hgkX, ← Matrix.mulVec_mulVec, hpfix i hi] at h1
    exact h1

  obtain ⟨σ', hσdef⟩ : ∃ σ' : Matrix (Fin n) (Fin n) ℂ,
      σ' = Matrix.diagonal fun i => if i ∈ T then (1 : ℂ) else (if ε' i then 1 else -1) := ⟨_, rfl⟩
  have hσσ' : σ' * σ' = 1 := by
    rw [hσdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> norm_num
  have hσ'UJ : Formalism.REAL.inUJ ε' σ' := by
    unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    rw [hσdef, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; simp only [Pi.star_apply]; split_ifs <;> simp
  have hσfix : ∀ i ∈ T, σ' *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    funext r
    rw [hσdef, Matrix.mulVec_diagonal]
    by_cases hr : r = i
    · subst hr; simp [hi]
    · simp [Pi.single_apply, hr]
  have hcol : ∀ i ∈ T, ∀ r, p' r i = if r = i then 1 else 0 := fun i hi r =>
    inst_col_entry p' i (hpfix i hi) r
  have hrow : ∀ i ∈ T, ∀ r, p' i r = if r = i then 1 else 0 := by
    intro i hi r
    have h1 : p' i r = star (p' r i) := by
      conv_lhs => rw [← hp'H]
      rfl
    rw [h1, hcol i hi r]
    split_ifs <;> simp
  have hkey : σ' * p' * σ' = Formalism.REAL.Jm ε' * p' * Formalism.REAL.Jm ε' := by
    ext r c
    simp only [hσdef, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hr : r ∈ T
    · rw [hrow r hr c]
      by_cases hrc : c = r
      · subst hrc; simp only [hr, if_true]; split_ifs <;> norm_num
      · simp [hrc]
    · by_cases hc : c ∈ T
      · rw [hcol c hc r]
        by_cases hrc : r = c
        · subst hrc; exact absurd hc hr
        · simp [hrc]
      · simp [hr, hc]
  have hJinv : (Formalism.REAL.Jm ε')⁻¹ = Formalism.REAL.Jm ε' := Matrix.inv_eq_left_inv hJ'J'
  have hJX : Formalism.REAL.Jm ε' * X' * Formalism.REAL.Jm ε' = -X' := ((Formalism.REAL.pChar n ε' X').2 hX')
  have hJp : Formalism.REAL.Jm ε' * p' * Formalism.REAL.Jm ε' = NormedSpace.exp (-X') := by
    have := Matrix.exp_conj (Formalism.REAL.Jm ε') X' ⟨⟨_, _, hJ'J', hJ'J'⟩, rfl⟩
    rw [hJinv, hJX] at this
    rw [hp'def, this]
  have hσp' : σ' * p' * σ' * p' = 1 := by
    rw [hkey, hJp, hp'def, ← Matrix.exp_add_of_commute _ _ (Commute.refl X').neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have hk'UJ : Formalism.REAL.inUJ ε' k' := (Formalism.REAL.kFacts n ε').1 k' hk'
  have hp'UJ : Formalism.REAL.inUJ ε' p' := by
    have := Formalism.REAL.expUJ n ε' X' hX'.1 1
    simpa [hp'def] using this

  refine ⟨A * k' * Ai, A * p' * Ai, A * σ' * Ai, tr2 _ hk'UJ, tr2 _ hp'UJ, tr2 _ hσ'UJ, back _ hkfix,
    back _ hpfix, back _ hσfix, ?_, ?_, ?_, ?_⟩
  · have : g = A * g' * Ai := by
      rw [hg'def]
      calc g = (A * Ai) * g * (A * Ai) := by rw [hAAi, Matrix.one_mul, Matrix.mul_one]
        _ = A * (Ai * g * A) * Ai := by simp only [Matrix.mul_assoc]
    rw [this, hgkX]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul, ← Matrix.mul_assoc σ' σ', hσσ', Matrix.one_mul, hAAi]
  · have : A * σ' * Ai * (A * p' * Ai) * (A * σ' * Ai) * (A * p' * Ai) = A * (σ' * p' * σ' * p') * Ai := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul, ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul,
        ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]
    rw [this, hσp', Matrix.mul_one, hAAi]
  ·
    set R : ℝ := (n : ℝ) + 1 with hR
    have hemb := (Formalism.REAL.uJEmb n ε).1
    refine ⟨{x : Formalism.REAL.UJ ε | Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A) ≤ R}, ?_, ?_, ?_⟩
    · have hcomp : IsCompact ((fun m => A * m * Ai) '' {m | Formalism.REAL.inUJ ε' m ∧ Formalism.REAL.hs m ≤ R}) :=
        ((Formalism.REAL.hSBall n ε').1 R).image ((continuous_const.mul continuous_id).mul continuous_const)
      have hset : {x : Formalism.REAL.UJ ε | Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A) ≤ R} =
          (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) ⁻¹'
            ((fun m => A * m * Ai) '' {m | Formalism.REAL.inUJ ε' m ∧ Formalism.REAL.hs m ≤ R}) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
        constructor
        · intro hx
          refine ⟨Ai * Formalism.MainNotions.S.uMat x * A, ⟨tr1 _ x.2, hx⟩, ?_⟩
          simp only [Matrix.mul_assoc]
          rw [hAAi, Matrix.mul_one, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
        · rintro ⟨m, ⟨_, hm2⟩, hm⟩
          have : Ai * Formalism.MainNotions.S.uMat x * A = m := by
            have hx : Formalism.MainNotions.S.uMat x = A * m * Ai := hm.symm
            rw [hx]
            simp only [Matrix.mul_assoc]
            rw [hAiA, Matrix.mul_one, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
          rw [this]; exact hm2
      rw [hset]
      exact hemb.isCompact_preimage hcomp
    · obtain ⟨U, hUo, h1U, hU⟩ := Formalism.REAL.ballOpen n R (by rw [hR]; linarith)
      refine mem_interior.mpr ⟨(fun x : Formalism.REAL.UJ ε => Ai * Formalism.MainNotions.S.uMat x * A) ⁻¹' U, ?_, ?_, ?_⟩
      · intro x hx
        exact (hU _ hx).le
      · exact hUo.preimage ((continuous_const.mul hemb.continuous).mul continuous_const)
      · show Ai * Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) * A ∈ U
        have h1 : Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl
        rw [h1, Matrix.mul_one, hAiA]
        exact h1U
    · intro x y hxy
      have h1 : Ai * Formalism.MainNotions.S.uMat y * A * k' = k' * (Ai * Formalism.MainNotions.S.uMat x * A) := by
        have := congrArg (fun M => Ai * M * A) hxy
        simp only [Matrix.mul_assoc] at this ⊢
        rw [hAiA, Matrix.mul_one, ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul] at this
        exact this
      have h2 : Ai * Formalism.MainNotions.S.uMat y * A = k' * (Ai * Formalism.MainNotions.S.uMat x * A) * star k' := by
        rw [← h1, Matrix.mul_assoc _ k', hk'u2, Matrix.mul_one]
      have h3 : Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat y * A) = Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A) := by
        rw [h2, ((Formalism.REAL.hSBall n ε').2 _ _ (inst_Kset_star ε' hk')).1,
          ((Formalism.REAL.hSBall n ε').2 _ _ hk').2]
      simp only [Set.mem_ofPred_eq, h3]
end PI.ScMuExists.UnitaryGroupMassFormula
