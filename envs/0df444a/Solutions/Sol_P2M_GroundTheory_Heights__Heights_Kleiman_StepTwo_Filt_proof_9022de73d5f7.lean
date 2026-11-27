-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepTwo_Filt_proof_9022de73d5f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:04:13.28654+00:00
-- url     : https://prove2.me/submissions/315b5d08-79d8-4f4d-b870-fe1db7199928

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepTwoFilt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_of_piece_eq_7de61d87ab1c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_mem_filtPiece_dc3e1604a1b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_bot_0d6ee714c8d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_mono_1da95a728efe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_sup_19ebee9ad0cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_top_9f718a593fcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isProjStable_bot_02612d522831
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isProjStable_sup_eea02c2477b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_finite_53e2c0015aff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_d36d759dd77d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_of_5b80ebceba38


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace StepTwo.Filt
theorem _root_.solution (h : PrimeFiltration.Exists.Statement.{u, v, w}) :
    StepTwo.Filt.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ hle J hJ
  classical
  obtain ⟨⟨F⟩, -⟩ := h S Ω N x (quotLaurent M₁ M₂) (quotLaurentGraded M₁ M₂) (quotLaurent_finite M₁ M₂)
    fun p hp y => quotLaurent_smul_eq_zero M₁ M₂ hp y
  have hrep : ∀ k, ∃ g : M₁.piece (F.deg k), quotIota M₁ M₂ (F.deg k) g = F.gen k :=
    fun k => LinearMap.mem_range.mp (F.gen_mem k)
  choose g hg using hrep
  have hstab : ∀ k : Fin (F.n + 1), IsProjStable M₁ M₂ (F.step k) := by
    intro k
    induction k using Fin.induction with
    | zero => rw [F.step_zero]; exact isProjStable_bot
    | succ k ih => rw [F.step_succ k, ← hg k]; exact isProjStable_sup ih (g k)
  have hfg : ∀ k : Fin (F.n + 1), ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → E),
      (∀ j, gen j ∈ filtPiece M₁ M₂ (F.step k) (deg j)) ∧
      ∀ c, filtPiece M₁ M₂ (F.step k) c ≤ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
        f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f • gen j} := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [F.step_zero]
      simp only [filtPiece_bot hle]
      exact M₂.fg
    | succ k ih =>
      obtain ⟨n, deg, gen, hmem, hspan⟩ := ih
      have hsup := filtPiece_sup (hstab k.castSucc) (g k)
      rw [F.step_succ k, ← hg k]
      refine ⟨n + 1, Fin.cons (F.deg k) deg, Fin.cons (g k : E) gen, fun j => ?_, fun c => ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · rw [Fin.cons_zero, Fin.cons_zero, hsup]
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, ?_⟩)
          rw [map_one, one_smul]
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact filtPiece_mono le_sup_left _ (hmem j)
      · rw [hsup]
        refine sup_le ((hspan c).trans (Submodule.span_mono ?_)) (Submodule.span_mono ?_)
        · rintro _ ⟨j, f, e, hf, he, rfl⟩
          exact ⟨j.succ, f, e, hf, by rw [Fin.cons_succ]; exact he, by rw [Fin.cons_succ]⟩
        · rintro _ ⟨f, d, hf, hd, rfl⟩
          exact ⟨0, f, d, hf, by rw [Fin.cons_zero]; omega, by rw [Fin.cons_zero]⟩
  refine ⟨F.n, fun k => filtSub M₁ M₂ (F.step k) (hfg k), fun k => (g k : E), F.deg, F.prime, ?_, ?_,
    fun k => ⟨F.isPrime k, F.isHomogeneous k, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine FinGradedSub.eq_of_piece_eq (funext fun c => ?_)
    change filtPiece M₁ M₂ (F.step 0) c = _
    rw [F.step_zero, filtPiece_bot hle]
  · refine FinGradedSub.eq_of_piece_eq (funext fun c => ?_)
    change filtPiece M₁ M₂ (F.step (Fin.last F.n)) c = _
    rw [F.step_last, filtPiece_top]
  · exact fun p hp => F.ann_le k
      (Module.mem_annihilator.mpr fun y => quotLaurent_smul_eq_zero M₁ M₂ hp y)
  · exact fun f e hf he => F.ann_le k
      (Module.mem_annihilator.mpr fun y => quotLaurent_smul_eq_zero_of M₁ M₂ he (hJ f e hf he) y)
  · change ((g k : M₁.piece (F.deg k)) : E) ∈ filtPiece M₁ M₂ (F.step k.succ) (F.deg k)
    rw [coe_mem_filtPiece, hg k, F.step_succ]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · intro c
    change filtPiece M₁ M₂ (F.step k.succ) c = filtPiece M₁ M₂ (F.step k.castSucc) c ⊔ _
    rw [F.step_succ, ← hg k, filtPiece_sup (hstab k.castSucc) (g k) c]
  · intro f d hf
    rw [F.mem_prime, ← hg k, smul_quotIota M₁ M₂ hf]
    exact (coe_mem_filtPiece _).symm
end StepTwo.Filt
end GroundTheory.Heights₂.Heights.Kleiman
