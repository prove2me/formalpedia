-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.entryRV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:05.389777+00:00
-- url     : https://prove2.me/submissions/35a4e874-2370-4dcc-9c48-126869449fc1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_entry_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_eq_frobVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_normRV_u

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {s : Bool} {g : Matrix (Fin n) (Fin n) ℂ} {u : Matrix (Fin n) (SgIxV ε s) ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hg : hs g ≤ R ^ 2) (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) (i : Fin n) (j : SgIxV ε s) :
    ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  have hw := normRV_u hu
  have hg' : ‖g‖ ≤ R := by
    rw [hs_eq_frobVG] at hg
    exact le_of_pow_le_pow_left₀ two_ne_zero hR hg
  have h1 : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have h0 := hsRV_entry_le (g * u) i j
    rw [hsRV_eq] at h0
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h0
  have h2 : ‖g * u‖ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
  have h3 : ‖g‖ * ‖u‖ ≤ R * (Real.sqrt n + 1) := mul_le_mul hg' (by linarith) (norm_nonneg _) hR
  linarith
end ReciprocityTheory.ChartRestriction.DS.S7
