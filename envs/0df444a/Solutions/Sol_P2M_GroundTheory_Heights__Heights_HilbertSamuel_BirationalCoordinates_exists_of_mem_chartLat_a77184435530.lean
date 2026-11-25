-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_exists_of_mem_chartLat_a77184435530
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:06.964839+00:00
-- url     : https://prove2.me/submissions/e3f3dddc-aedd-4591-b940-fea6cb2115a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_chartRingZ_eq_335699c6df6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx
omit [Fintype κ]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (a : Unit → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ chartLat (ι := GlobalTheory κ) x a τ) : ∃ s' : Ω'', μ ^ ((τ : ℤ) * a ()) * j s' = s := by
  have h := hs (fun _ => c) (fun _ => hc)
  simp only [Fintype.prod_unique] at h
  rw [chartRingZ_eq j hμ hx, Subalgebra.mem_map] at h
  obtain ⟨t, -, ht⟩ := h
  rw [RingHom.toIntAlgHom_apply] at ht
  have hyc : y ⟨(), c⟩ ≠ 0 := fun h0 => hc (by rw [hx, h0, map_zero, mul_zero])
  refine ⟨t * y ⟨(), c⟩ ^ ((τ : ℤ) * a ()), ?_⟩
  rw [map_mul, ht, map_zpow₀]
  change μ ^ ((τ : ℤ) * a ()) * (s * x ⟨(), c⟩ ^ (-((τ : ℤ) * a ())) * j (y ⟨(), c⟩) ^ ((τ : ℤ) * a ())) = s
  rw [hx, mul_zpow, zpow_neg]
  have h1 : μ ^ ((τ : ℤ) * a ()) ≠ 0 := zpow_ne_zero _ hμ
  have h2 : j (y ⟨(), c⟩) ^ ((τ : ℤ) * a ()) ≠ 0 := zpow_ne_zero _ (map_ne_zero j |>.2 hyc)
  field_simp
  rw [zpow_neg, inv_mul_cancel_right₀ h2]
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
