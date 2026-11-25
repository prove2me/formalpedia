-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.top_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:01.285917+00:00
-- url     : https://prove2.me/submissions/1aa91f73-574a-4e80-93f5-339f3ded8baf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
import Theorems.Thm_PI_OneCosetSharp_W_C2_facts
import Theorems.Thm_PI_OneCosetSharp_W_C2_ent_unit
import Theorems.Thm_PI_OneCosetSharp_W_C2_chiV_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
open Classical
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k)
    (hC : (∀ p', p' < k₀ + m - 1 → ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p' p' = 1) ∧
      (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' →
        ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' ≠ 0 → Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p')) :
    chiV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
      ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) s.1 s'.1)) = 1 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hdet : Matrix.det (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) s.1 s'.1) = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro s _
      have hs1 := s.isLt
      rw [Matrix.of_apply]
      by_cases hs : s.1 < k₀ + m - 1
      · exact hC.1 s.1 hs
      · rw [ent_unit hN τ (by omega) (by omega) (by omega), if_pos rfl]
    · intro s s' hss
      have hss' : s'.1 < s.1 := hss
      have hs1 := s.isLt
      have hs2 := s'.isLt
      rw [Matrix.of_apply]
      by_cases hcol : s'.1 ≤ k₀ ∨ k₀ + c < s'.1
      · rw [ent_unit hN τ (by omega) (by omega) hcol, if_neg (by omega)]
      · by_contra hne
        have hA := hC.2 s.1 s'.1 (by omega) hs2 (by omega) hne
        unfold PI.OneCosetSharp.Allow at hA
        split_ifs at hA <;> omega
  rw [hdet, chiV_one]
end PI.OneCosetSharp.W.C2
