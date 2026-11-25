-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.zeta_cost_of_smooth_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:53.98184+00:00
-- url     : https://prove2.me/submissions/df097212-ef05-46a4-af67-9268992de415

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterC
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_list_prod_le_pow
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_max_one_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dx
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_mono
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_cF_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_cF_bound
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_contDiffOn_cF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_isOpen_det
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_iter_words
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_norm_inverse_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (hS : ZSmooth) (hD : ZDeriv) (hDS : DirSize) : ZCost := by
  intro hSM hRP hSZ hDP hS21 k p s ρ σ d hd hs K hK hK0 q
  obtain ⟨C₁, hC₁⟩ := hDS hDP k p s ρ σ
  obtain ⟨C₂, hC₂⟩ := hS21 k p s ρ σ d hd hs K hK hK0
  obtain ⟨Kc, hKc0, hKc⟩ := ZI.cF_bound s q
  obtain ⟨C, hC1, hC⟩ := ZI.iter_words (V := G.Mat s) (I := Fin s × Fin s × Bool) q Kc hKc0
  have hE'0 : (0 : ℝ) ≤ max 1 ‖ZI.eA s‖ := zero_le_one.trans (le_max_left _ _)
  set A : ℝ := (1 + |(|C₁| * C₂ ^ 4)|) * (max 1 ‖ZI.eA s‖ * (1 + |‖ZI.eA s‖ * C₂|)) with hA
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (mul_nonneg hE'0 (by positivity))
  refine ⟨C * A ^ q, ?_⟩
  intro E _ _ H β hH ξ Z γ hZ hγ hKg hw
  have hZ' : (Matrix.of Z).det ≠ 0 := hZ
  refine ⟨(hS hSM hRP k p s ρ σ d hd E H q hH ξ Z γ hZ hγ).2.2, ?_⟩
  obtain ⟨hg1, -, hRn, -, -, -, hb, -, -, -, -, hinv⟩ := hC₂ ξ Z γ hγ hKg
  set g := gaXi k ρ σ d ξ Z γ with hg
  set lam := max 1 (C₁ * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) with hlam
  set M := max 1 ‖ZI.eA s‖ * max 1 ‖Ring.inverse (ZI.eA s Z)‖ with hM
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  have hβ : 0 ≤ β := by
    have := hw [] (by simp) (by simp)
    simp only [List.map_nil, List.prod_nil, mul_one] at this
    exact (norm_nonneg _).trans this
  have hlet : ∀ i, inLieP k (p + s) ρ (dirZ k ρ ξ i) ∧ lsz (dirZ k ρ ξ i) ≤ lam := fun i =>
    ⟨(hC₁ ξ i).1, (hC₁ ξ i).2.trans (le_max_right _ _)⟩
  have key := hC (α := B.Mat k (p + s + ρ)) (E := E)
    (fun b H' => B.CkOn (b : ℕ∞) (B.GV k (p + s + ρ)) H')
    (fun i H' => RdV (dirZ k ρ ξ i) H') (fun Z' => gaXi k ρ σ d ξ Z' γ)
    {Z' : G.Mat s | (Matrix.of Z').det ≠ 0} (fun i => ZI.cF s i) Z M lam
    (ZI.isOpen_det s) hZ' hM1 hlam1
    (fun b H' h => P.BetaSesquilinearity.CkOn_mono (by exact_mod_cast Nat.le_succ b) h)
    (fun b H' i h => by
      have h' : B.CkOn ((b : ℕ∞) + 1) (B.GV k (p + s + ρ)) H' := by simpa using h
      have := P.BetaSesquilinearity.CkOn_Dx (x := (false, dirZ k ρ ξ i)) (hlet i).1.1 h'
      simpa [P.BetaSesquilinearity.Dx] using this)
    (fun b H' h z hz => (hS hSM hRP k p s ρ σ d hd E H' b h ξ z γ hz hγ).2.2)
    (fun b H' h z hz => by
      ext1 W
      rw [hD hSM hRP hSZ k p s ρ σ d hd E H'
        (P.BetaSesquilinearity.CkOn_mono (by exact_mod_cast Nat.le_add_left 1 b) h) ξ z γ hz hγ W]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZI.cF_apply s i hz]
      rfl)
    (fun i n => ZI.contDiffOn_cF s i n)
    (fun i a ha => hKc Z hZ' i a ha)
    q le_rfl H β hH (fun w hwl => by
      have e : w.foldr (fun i H' => RdV (dirZ k ρ ξ i) H') H = B.Rw (w.map (dirZ k ρ ξ)) H := by
        simp [B.Rw, List.foldr_map]
      rw [e]
      refine (hw (w.map (dirZ k ρ ξ)) (fun X hX => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
          exact (hlet i).1) (by rw [List.length_map]; exact hwl)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hβ
      have := list_prod_le_pow ((w.map (dirZ k ρ ξ)).map lsz) lam (by
        intro x hx
        obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
        exact ⟨zero_le_one.trans (le_max_left _ _), (hlet i).2⟩)
      simpa using this)

  have hg0 : 0 ≤ B.gN g := by linarith
  have hR0 : 0 ≤ B.gN (Rn k (p + s) ρ ξ.1.2) := Real.sqrt_nonneg _
  have hlamb : lam ≤ (1 + |(|C₁| * C₂ ^ 4)|) * B.gN g ^ (2 * (p + s) + 2 * p) := by
    refine max_one_le _ _ (one_le_pow₀ hg1) _ ?_
    have h1 : B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 ≤ (C₂ * B.gN g ^ (p + s)) ^ 2 := pow_le_pow_left₀ hR0 hRn 2
    have h2 : (1 + ‖ξ.2.1.2‖) ^ 2 ≤ (C₂ * B.gN g ^ p) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
    have hpow : B.gN g ^ (2 * (p + s) + 2 * p) = (B.gN g ^ (p + s)) ^ 2 * (B.gN g ^ p) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    calc C₁ * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2
        = C₁ * (B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by ring
      _ ≤ |C₁| * (B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₁| * ((C₂ * B.gN g ^ (p + s)) ^ 2 * (C₂ * B.gN g ^ p) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) (abs_nonneg _)
      _ = (|C₁| * C₂ ^ 4) * B.gN g ^ (2 * (p + s) + 2 * p) := by rw [hpow]; ring
  have hMb : M ≤ max 1 ‖ZI.eA s‖ * ((1 + |‖ZI.eA s‖ * C₂|) * B.gN g ^ (p + s - 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hE'0
    refine max_one_le _ _ (one_le_pow₀ hg1) _ ?_
    calc ‖Ring.inverse (ZI.eA s Z)‖ ≤ ‖ZI.eA s‖ * ‖ZI.invF s Z‖ := ZI.norm_inverse_le s hZ'
      _ ≤ ‖ZI.eA s‖ * (C₂ * B.gN g ^ (p + s - 1)) := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = ‖ZI.eA s‖ * C₂ * B.gN g ^ (p + s - 1) := by ring
  have hLM : lam * M ≤ A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1)) := by
    calc lam * M ≤ ((1 + |(|C₁| * C₂ ^ 4)|) * B.gN g ^ (2 * (p + s) + 2 * p)) *
          (max 1 ‖ZI.eA s‖ * ((1 + |‖ZI.eA s‖ * C₂|) * B.gN g ^ (p + s - 1))) :=
          mul_le_mul hlamb hMb (by linarith) (by positivity)
      _ = A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1)) := by rw [hA, pow_add]; ring
  have hexp : (2 * (p + s) + 2 * p + (p + s - 1)) * q ≤ 5 * (p + s + ρ) * q :=
    Nat.mul_le_mul_right q (by omega)
  have hrp : B.gN g ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) = B.gN g ^ (5 * (p + s + ρ) * q) := by
    rw [← Real.rpow_natCast]; congr 1; push_cast; ring
  rw [hrp]
  calc ‖iteratedFDeriv ℝ q (fun Z' => H (gaXi k ρ σ d ξ Z' γ)) Z‖ ≤ C * β * (lam * M) ^ q := key
    _ ≤ C * β * (A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1))) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLM q) (by positivity)
    _ = C * β * (A ^ q * B.gN g ^ ((2 * (p + s) + 2 * p + (p + s - 1)) * q)) := by rw [mul_pow, pow_mul]
    _ ≤ C * β * (A ^ q * B.gN g ^ (5 * (p + s + ρ) * q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg1 hexp) (by positivity))
          (by positivity)
    _ = C * A ^ q * β * B.gN g ^ (5 * (p + s + ρ) * q) := by ring
end PI.UnitaryGroupMassFormula.UsCost
