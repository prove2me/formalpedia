-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.translate_pullbackSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:28:21.956634+00:00
-- url     : https://prove2.me/submissions/a8296382-7288-4f27-81ba-9d8d85046df6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_eps_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) {k : Fin n → Vsp X.dim}
    (hk : ∀ j, π (k j) ∈ X.L) (v : Fin n → Vsp X.dim) :
    X.U q k (s0 X π s) v = (∏ j, (X.eps (π (k j)) : ℂ)) * s0 X π s v := by
  have key : ∀ j, s (fun _ => π ((v - k) j)) = (X.eps (π (k j)) : ℂ) *
      cexp (-((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2)) *
        s (fun _ => π (v j)) := by
    intro j
    have h := hs.2 (fun _ => π (k j)) (fun _ => hk j) (fun _ => π ((v - k) j))
    have e1 : (fun _ : Fin 1 => π ((v - k) j)) + (fun _ => π (k j)) = (fun _ => π (v j)) := by
      funext; simp [← map_add]
    rw [e1] at h
    simp only [HC, Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, hπ.2.2.1,
      pow_one] at h
    rw [h]
    have he : (X.eps (π (k j)) : ℂ) * X.eps (π (k j)) = 1 := by
      rw [← sq]; exact nA_eps_sq X (hk j)
    set A : ℂ := (q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2
    have hA : ((1 : ℕ) : ℂ) * Real.pi * ((q : ℂ) * Hf ((v - k) j) (k j)) +
        ((1 : ℕ) : ℂ) * Real.pi * ((q : ℂ) * Hf (k j) (k j)) / 2 = A := by
      push_cast; ring
    rw [hA]
    calc s (fun _ => π ((v - k) j))
        = ((X.eps (π (k j)) : ℂ) * X.eps (π (k j))) * (cexp (-A) * cexp A) *
            s (fun _ => π ((v - k) j)) := by
          rw [he, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]; ring
      _ = _ := by ring
  unfold PT.U s0
  simp_rw [key]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hz : (q : ℂ) * Real.pi * HC v k - q * Real.pi * HC k k / 2 +
      ∑ j, -((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2) = 0 := by
    have : ∑ j, -((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2) =
        -((q : ℂ) * Real.pi * HC (v - k) k + q * Real.pi * HC k k / 2) := by
      simp only [HC, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    rw [this, nA_HC_sub_left]; ring
  calc cexp ((q : ℂ) * Real.pi * HC v k - q * Real.pi * HC k k / 2) *
        ((∏ j, (X.eps (π (k j)) : ℂ)) *
          cexp (∑ j, -((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2)) *
          ∏ j, s fun _ => π (v j))
      = (∏ j, (X.eps (π (k j)) : ℂ)) *
          cexp ((q : ℂ) * Real.pi * HC v k - q * Real.pi * HC k k / 2 +
            ∑ j, -((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2)) *
          ∏ j, s fun _ => π (v j) := by rw [Complex.exp_add]; ring
    _ = _ := by rw [hz, Complex.exp_zero, mul_one]
end ReciprocityTheory.ChartRestriction.G.I2
