-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_proof_c751fd7b093e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:07.248316+00:00
-- url     : https://prove2.me/submissions/13903fb3-5ce8-47ca-aa14-6a09c4e2dd69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_lintegral_pi_prod_752dfe38d72d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_entryConst_pos_36bb65c93ccf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_measurable_ballInd_516d08b4ae20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_entry_bound_ba231565ac76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_integrand_le_9fff8f12eb82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_prod_entry_eq_0ac10606d8ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution : LeadBlockGaussTail.Statement := by
  intro m k hm
  set N : ℝ := (Fintype.card (Equiv.Perm (Fin m)) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hK := entryConst_pos
  refine ⟨N * (N * entryConst ^ (m * (m + k))), fun r => ?_⟩
  have hφ : ∀ s j : Fin (m + k), Measurable (entryFn r (Fin.castAdd k ⟨0, hm⟩) s j) := fun s j =>
    ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))).mul (measurable_ballInd _)
  have hrowm : ∀ σ : Equiv.Perm (Fin m), ∀ i : Fin m, Measurable fun x : Fin (m + k) → ℂ =>
      ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (x j) :=
    fun σ i => Finset.measurable_prod _ fun j _ => (hφ _ j).comp (measurable_pi_apply j)
  have hq : 0 < (1 + r ^ 2) ^ (m + 1) := by positivity
  calc _ ≤ ∫⁻ π : Fin m → Fin (m + k) → ℂ, ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) :=
        lintegral_mono (integrand_le hm r)
    _ = ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ∏ i, ∏ j, ∫⁻ z, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j z := by
        have hmeas : ∀ σ : Equiv.Perm (Fin m), Measurable fun π : Fin m → Fin (m + k) → ℂ =>
            ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) :=
          fun σ => Finset.measurable_prod _ fun i _ => (hrowm σ i).comp (measurable_pi_apply i)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun σ _ => hmeas σ)]
        congr 1
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [volume_pi, lintegral_pi_prod _ m _ (hrowm σ)]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [volume_pi, lintegral_pi_prod _ (m + k) _ (fun j => hφ _ j)]
    _ ≤ ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, ∏ j : Fin (m + k),
          ENNReal.ofReal (entryConst / (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
            ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1)) := by
        gcongr with σ _ i _ j _
        exact entry_bound _ _ (by split_ifs <;> omega)
    _ = ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ENNReal.ofReal (entryConst ^ (m * (m + k)) / (1 + r ^ 2) ^ (m + 1)) := by
        congr 1
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_congr rfl fun i _ =>
            (ENNReal.ofReal_prod_of_nonneg fun j _ => div_nonneg hK.le (by positivity)).symm,
          ← ENNReal.ofReal_prod_of_nonneg fun i _ =>
            Finset.prod_nonneg fun j _ => div_nonneg hK.le (by positivity),
          prod_entry_eq hm]
    _ = ENNReal.ofReal (N * (N * entryConst ^ (m * (m + k))) / (1 + r ^ 2) ^ (m + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul hN0]
        congr 1
        rw [hN]
        ring
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
