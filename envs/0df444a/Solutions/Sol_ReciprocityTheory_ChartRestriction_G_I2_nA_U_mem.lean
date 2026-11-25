-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_U_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:55.505857+00:00
-- url     : https://prove2.me/submissions/a9a065e3-dd8e-47fc-9ff5-786db41d0ccf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_int_im
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_exp_antisymm_eq_one

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
theorem _root_.solution {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n)
    {b : Fin n → Vsp X.dim} (hb : ∀ k, (q : ℂ) • b k ∈ X.L) : X.U q b F ∈ X.Sec q n := by
  refine ⟨?_, fun γ hγ v => ?_⟩
  · unfold PT.U
    have h1 : Differentiable ℂ (fun v : Fin n → Vsp X.dim => F (v - b)) :=
      hF.1.comp (differentiable_id.sub_const b)
    have h2 : Differentiable ℂ (fun v : Fin n → Vsp X.dim =>
        (q : ℂ) * Real.pi * HC v b - q * Real.pi * HC b b / 2) := by
      unfold HC Hf
      fun_prop
    exact (h2.cexp).mul h1
  · unfold PT.U
    have e1 : v + γ - b = (v - b) + γ := by abel
    rw [e1, hF.2 γ hγ (v - b)]
    obtain ⟨m, hm⟩ := nA_int_im X hγ hb
    have h1 := nA_exp_antisymm_eq_one X q γ b m hm
    have hsplit : (q : ℂ) * Real.pi * HC (v + γ) b - q * Real.pi * HC b b / 2 +
        ((q : ℂ) * Real.pi * HC (v - b) γ + q * Real.pi * HC γ γ / 2) =
        ((q : ℂ) * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2) +
        ((q : ℂ) * Real.pi * HC v b - q * Real.pi * HC b b / 2) +
        (q : ℂ) * Real.pi * (HC γ b - HC b γ) := by
      rw [nA_HC_add_left, nA_HC_sub_left]; ring
    calc cexp ((q : ℂ) * Real.pi * HC (v + γ) b - q * Real.pi * HC b b / 2) *
          ((∏ k, (X.eps (γ k) : ℂ)) ^ q * cexp ((q : ℂ) * Real.pi * HC (v - b) γ +
            q * Real.pi * HC γ γ / 2) * F (v - b))
        = (∏ k, (X.eps (γ k) : ℂ)) ^ q *
            cexp ((q : ℂ) * Real.pi * HC (v + γ) b - q * Real.pi * HC b b / 2 +
              ((q : ℂ) * Real.pi * HC (v - b) γ + q * Real.pi * HC γ γ / 2)) * F (v - b) := by
          simp only [Complex.exp_add]; ring
      _ = _ := by
          rw [hsplit, Complex.exp_add, Complex.exp_add, h1]; ring
end ReciprocityTheory.ChartRestriction.G.I2
