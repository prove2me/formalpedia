-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.prod_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:00:53.299666+00:00
-- url     : https://prove2.me/submissions/5182820f-aa88-4fa5-a85b-f8e4239bde67

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
    (τ : FC n' (c + 1) n c → k) :
    ∏ i ∈ Finset.range (j - 1), chiV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
      ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) (k₀ + m - 1 + i * t + s.1) (k₀ + m - 1 + i * t + s'.1))) = 1 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  apply Finset.prod_eq_one
  intro i hi
  rw [Finset.mem_range] at hi
  have hit : i * t + t ≤ (j - 1) * t := by
    have h := Nat.mul_le_mul (show i + 1 ≤ j - 1 by omega) (le_refl t)
    rwa [add_mul, one_mul] at h
  have hM : (Matrix.of fun s s' : Fin t =>
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) (k₀ + m - 1 + i * t + s.1)
        (k₀ + m - 1 + i * t + s'.1)) = 1 := by
    ext s s'
    have hs1 := s.isLt
    have hs2 := s'.isLt
    rw [Matrix.of_apply, ent_unit hN τ (by omega) (by omega) (by omega), Matrix.one_apply]
    by_cases h : s = s'
    · subst h
      simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (Fin.ext (by omega))
  rw [hM, Matrix.det_one, chiV_one]
end PI.OneCosetSharp.W.C2
