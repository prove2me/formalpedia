-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cC_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:59:34.625283+00:00
-- url     : https://prove2.me/submissions/c30eed5e-4c70-422b-a81b-e872d1fa7b5c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cC_c_nonneg
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cC_Psi_ck
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cC_cost
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Rw_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_leib_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_nrm_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sub_LR
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dw_clm
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_unitLie
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_wP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {d Q o mm₀ : ℕ} {A₀ : ℝ} {φ : B.Mat k (j + ρ) → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {Cφ : ℝ}
    (hWB : WB (fun X => costP k j ρ X + d) φ (Q + o) Cφ 0) {w : List (B.Mat k (j + ρ))}
    (hw : ∀ X ∈ w, B.inLie k (j + ρ) X) (hwo : w.length ≤ o) (hQ : Q + o ≤ mm₀) :
    ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ (f : B.Mat k (j + ρ) → E) (c : ℝ), B.CCle A₀ mm₀ f c →
      ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u → unitP k j ρ v → u.length + v.length ≤ Q →
        ∀ g ∈ B.GV k (j + ρ), ‖B.dLR u v (B.Rw w (fun g => φ g • f g)) g‖ ≤
          CΨ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
  classical
  have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := j + ρ)
  have hCφ : 0 ≤ Cφ := by
    have h := hWB [] [] (by simp) (by simp) (by simp) 1 h1
    have hX := Real.rpow_pos_of_pos (gN_pos h1)
      ((0 : ℝ) + ((([] ++ [] : List (B.Mat k (j + ρ))).map (fun X => costP k j ρ X + d)).sum : ℕ))
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hX
    linarith [norm_nonneg (B.dLR [] [] φ 1)]
  have hw'lie : ∀ X ∈ w.map nrm, B.unitLie k (j + ρ) X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact nrm_unit (hw Y hY)
  obtain ⟨a, ha⟩ : ∃ a : B.Mat k (j + ρ) → (E →L[ℂ] E),
      a = fun g => φ g • ContinuousLinearMap.id ℂ E := ⟨_, rfl⟩
  have ha_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a := by
    rw [ha]
    exact hφ.smul contDiff_const
  have hφU : ∀ n : ℕ∞, B.CkOn n Set.univ φ := fun n g₀ _ =>
    ⟨Set.univ, φ, isOpen_univ, trivial, hφ.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top),
      fun _ _ _ => rfl⟩
  refine ⟨|((w.map nz).prod : ℝ)| * 2 ^ (Q + o) * Cφ, mul_nonneg (by positivity) hCφ,
    fun f c hf u v hu hv hl g hg => ?_⟩
  have hc : 0 ≤ c := cC_c_nonneg hf
  have hgN := gN_ge_one hg
  have hgN0 := gN_pos hg
  have hG : B.CkOn ((u.length + v.length : ℕ) : ℕ∞) (B.GV k (j + ρ))
      (B.Rw (w.map nrm) (fun g => φ g • f g)) :=
    cC_Psi_ck hφ hf.1 (fun X hX => (hw'lie X hX).1) (by simp only [List.length_map]; omega)
  obtain ⟨V, G', hVo, hgV, hG'c, hG'eq⟩ := hG g hg
  have hGV : B.CkOn ((u.length + v.length : ℕ) : ℕ∞) V (B.Rw (w.map nrm) (fun g => φ g • f g)) :=
    fun g₀ hg₀ => ⟨V, G', hVo, hg₀, hG'c, hG'eq⟩
  have hscale := cA_Dw_clm (E' := E) ((((w.map nz).prod : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) hVo
    (wL u ++ wR v) (fun x hx => ((cB_wP hu hv) x hx).1.1) (by simpa [wL, wR] using hGV) g hg hgV
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hscale
  have hsplit : Dw (wL u ++ wR (v ++ w.map nrm)) (fun g => φ g • f g) =
      Dw (wL u ++ wR v) (B.Rw (w.map nrm) (fun g => φ g • f g)) := by
    rw [show wR (v ++ w.map nrm) = wR v ++ wR (w.map nrm) from List.map_append,
      ← List.append_assoc, Dw_append, Dw_wR]
  have hF : (fun g => φ g • f g) = ap a f := by
    funext g
    simp [ap, ha]
  have hW'lie : ∀ x ∈ wL u ++ wR (v ++ w.map nrm), B.inLie k (j + ρ) x.2 := by
    intro x hx
    simp only [wL, wR, List.map_append, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1.1
    · exact (hv X hX).1.1
    · exact (hw'lie X (List.mem_map.2 hX)).1
  have hlen : (wL u ++ wR (v ++ w.map nrm)).length = u.length + v.length + w.length := by
    simp [wL, wR]
    omega
  have hPr : Pr ∅ Set.univ ((wL u ++ wR (v ++ w.map nrm)).length : ℕ∞) a f := by
    refine ⟨fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial,
      ha_smooth.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top), fun _ _ _ => rfl⟩, fun g₀ hg₀ => ?_,
      fun g _ hg => absurd hg (Set.notMem_empty g)⟩
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf.1 g₀ hg₀
    refine ⟨U, f', hU, hgU, hf'.of_le ?_, hff⟩
    rw [hlen]
    exact_mod_cast (by omega : u.length + v.length + w.length ≤ mm₀)
  have hbound : ∀ w₁ w₂ : List (Bool × B.Mat k (j + ρ)), w₁.Sublist (wL u ++ wR (v ++ w.map nrm)) →
      w₂.Sublist (wL u ++ wR (v ++ w.map nrm)) → w₁.length + w₂.length = (wL u ++ wR (v ++ w.map nrm)).length →
      ‖Dw w₁ a g‖ * ‖Dw w₂ f g‖ ≤ Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
    intro w₁ w₂ hw₁ hw₂ _
    obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hw₁
    obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hw₂
    have hunit : ∀ X ∈ v ++ w.map nrm, B.unitLie k (j + ρ) X := by
      intro X hX
      rcases List.mem_append.1 hX with hX | hX
      · exact cB_unitLie hv X hX
      · exact hw'lie X hX
    have hA : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ Cφ * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) := by
      have hDa := cA_Dw_clm (E := ℂ) (E' := E →L[ℂ] E)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ E))
        isOpen_univ (wL u₁ ++ wR v₁) (fun x hx => hW'lie x (hw₁.subset hx)) (hφU _) g hg trivial
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] at hDa
      rw [ha, hDa, norm_smul, ← dLR_eq]
      have hWB1 := hWB u₁ v₁ (fun X hX => cB_unitLie hu X (hu₁.subset hX))
        (fun X hX => hunit X (hv₁.subset hX))
        (by have := hu₁.length_le; have := hv₁.length_le; simp only [List.length_append, List.length_map] at *; omega) g hg
      have hcost := cC_cost hu hv hl hwo hu₁ hv₁ (d := d)
      have hexp : B.gN g ^ ((0 : ℝ) + ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ)) ≤
          B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hgN (by linarith)
      calc ‖B.dLR u₁ v₁ φ g‖ * ‖ContinuousLinearMap.id ℂ E‖ ≤ ‖B.dLR u₁ v₁ φ g‖ * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
        _ ≤ Cφ * B.gN g ^ ((0 : ℝ) + ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ)) := by
            rw [mul_one]; exact hWB1
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp hCφ
    have hB : ‖Dw (wL u₂ ++ wR v₂) f g‖ ≤ c * B.gN g ^ (-A₀) := by
      rw [← dLR_eq]
      have h2 := hf.2 u₂ v₂ (fun X hX => cB_unitLie hu X (hu₂.subset hX))
        (fun X hX => hunit X (hv₂.subset hX))
        (by have := hu₂.length_le; have := hv₂.length_le; simp only [List.length_append, List.length_map] at *; omega) g hg
      rw [Real.rpow_neg hgN0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgN0 _), mul_comm]
      exact h2
    calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) f g‖
        ≤ (Cφ * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ))) * (c * B.gN g ^ (-A₀)) :=
          mul_le_mul hA hB (norm_nonneg _) (mul_nonneg hCφ (Real.rpow_nonneg hgN0.le _))
      _ = Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
          rw [sub_eq_add_neg, Real.rpow_add hgN0 ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) (-A₀)]
          ring
  have hleib := leib_bound isOpen_empty (fun g _ => Or.inr trivial) g hg
    (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀)) (wL u ++ wR (v ++ w.map nrm)) a f
    hW'lie hPr hbound
  have hM : 0 ≤ Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) :=
    mul_nonneg (mul_nonneg hCφ hc) (Real.rpow_nonneg hgN0.le _)
  have hpow : (2 : ℝ) ^ (wL u ++ wR (v ++ w.map nrm)).length ≤ 2 ^ (Q + o) :=
    pow_le_pow_right₀ (by norm_num) (by rw [hlen]; omega)
  calc ‖B.dLR u v (B.Rw w (fun g => φ g • f g)) g‖
      = |((w.map nz).prod : ℝ)| * ‖Dw (wL u ++ wR (v ++ w.map nrm)) (ap a f) g‖ := by
        rw [Rw_scale, dLR_eq, hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← hF, hsplit]
    _ ≤ |((w.map nz).prod : ℝ)| * (2 ^ (wL u ++ wR (v ++ w.map nrm)).length *
          (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀))) :=
        mul_le_mul_of_nonneg_left hleib (abs_nonneg _)
    _ ≤ |((w.map nz).prod : ℝ)| * (2 ^ (Q + o) *
          (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hM) (abs_nonneg _)
    _ = |((w.map nz).prod : ℝ)| * 2 ^ (Q + o) * Cφ * c *
          B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by ring
end PI.UnitaryCorollaryDerivatives
