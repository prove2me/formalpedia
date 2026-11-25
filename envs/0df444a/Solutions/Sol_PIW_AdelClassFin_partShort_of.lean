-- Prove2me | solution 1 for PIW.AdelClassFin.partShort_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:25:06.650134+00:00
-- url     : https://prove2.me/submissions/93098212-6601-4aa2-97da-7a1836b71137

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
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
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix ComplexOrder
namespace PIW.AdelClassFin
theorem _root_.solution (hM : PartMink) (hMaj : SvMajE) (hCod : SvCodiff) (hB : SvBasis)
    (hD : SvGramDet) (hR : SvReal) : PartShort := by
  intro F E _ _ _ _ _ _ hCM m d hm hd
  obtain ⟨δ, hδ1, hδ⟩ := hCod E
  have hn1 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hN1 : 1 ≤ m * Module.finrank ℚ E :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨Kc, hK⟩ := hM _ hN1
  set S : ℝ := max Kc 0 * ((d * δ : ℕ) : ℝ) with hS
  refine ⟨((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℚ), fun p hp => ?_⟩
  obtain ⟨hherm, hdet, hfg, hspan, -, -⟩ := id hp
  obtain ⟨H, hH⟩ := hMaj F E hCM m p.1 hherm hdet
  obtain ⟨e, hlin, hemem, hegen⟩ := hB E m p.2 hfg hspan
  obtain ⟨hgd, hgb⟩ := hD F E hCM m d δ hd hδ1 hδ p hp e hlin hemem hegen
  obtain ⟨R, hRpd, hRdet, hRle⟩ := hR F E hCM m p.1 hherm H hH e hgd
  obtain ⟨c, hc0, hcR⟩ := hK R hRpd
  set x : Fin m → E := ∑ i, (c i : E) • e i with hx
  have hxmem : x ∈ p.2 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul E]
    exact p.2.toAddSubgroup.zsmul_mem (hemem i) (c i)
  have hx0 : x ≠ 0 := by
    intro h0
    apply hc0
    funext i
    have h0' : ∑ i, (c i : ℚ) • e i = 0 := by
      rw [← h0, hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul ℚ, Int.cast_smul_eq_zsmul E]
    exact_mod_cast Fintype.linearIndependent_iff.1 hlin _ h0' i
  refine ⟨x, hxmem, hx0, ?_⟩
  set a := hform (starRingEnd E) p.1 x x with ha
  have hsumle : ∑ φ : E →+* ℂ, ‖φ a‖ ≤ S := by
    have h1 := hRle c
    have hdetR : R.det ≤ ((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E) := by
      rw [hRdet]
      have h' : ((|(gramTr p.1 e).det| : ℚ) : ℝ) ≤
          ((((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E) : ℚ) : ℝ) := by exact_mod_cast hgb
      rw [Rat.cast_abs, Rat.cast_pow, Rat.cast_natCast] at h'
      exact h'
    have hR0 : 0 ≤ R.det := hRpd.det_pos.le
    have hroot : R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) ≤ ((d * δ : ℕ) : ℝ) := by
      calc R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ))
          ≤ (((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E)) ^
              ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
            Real.rpow_le_rpow hR0 hdetR (by positivity)
        _ = ((d * δ : ℕ) : ℝ) := by
            rw [one_div]; exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
    have hroot0 : 0 ≤ R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := Real.rpow_nonneg hR0 _
    calc ∑ φ : E →+* ℂ, ‖φ a‖ ≤ _ := h1
      _ ≤ Kc * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := hcR
      _ ≤ max Kc 0 * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hroot0
      _ ≤ S := mul_le_mul_of_nonneg_left hroot (le_max_right _ _)
  have hnorm : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ S ^ Module.finrank ℚ E := by
    have h2 := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
    simp only [norm_prod] at h2
    rw [show ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ a)‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| by simp] at h2
    rw [Rat.cast_abs, h2]
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ ≤ ∏ σ : E →ₐ[ℚ] ℂ, S :=
          Finset.prod_le_prod (fun σ _ => norm_nonneg _) (fun σ _ =>
            (Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ a‖) (fun φ _ => norm_nonneg _)
              (Finset.mem_univ (σ : E →+* ℂ))).trans hsumle)
      _ = S ^ Module.finrank ℚ E := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card ℚ E ℂ]
  have hfin : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ ((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℝ) :=
    hnorm.trans (Nat.le_ceil _)
  exact_mod_cast hfin
end PIW.AdelClassFin
