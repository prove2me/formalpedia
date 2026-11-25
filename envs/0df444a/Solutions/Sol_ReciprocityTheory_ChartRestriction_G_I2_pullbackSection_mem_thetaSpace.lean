-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pullbackSection_mem_thetaSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:17:51.443107+00:00
-- url     : https://prove2.me/submissions/c3e3255f-74e3-4a04-ae3f-47927ec3ad10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_pi_diff

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
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) : s0 X (n := n) π s ∈ X.Sec q n := by
  refine ⟨?_, fun γ hγ v => ?_⟩
  · unfold s0
    have hk : ∀ k : Fin n, Differentiable ℂ (fun v : Fin n → Vsp X.dim => s fun _ => π (v k)) :=
      fun k => hs.1.comp (nA_pi_diff X (q := q) k)
    have hp : ∀ t : Finset (Fin n),
        Differentiable ℂ (fun v : Fin n → Vsp X.dim => ∏ k ∈ t, s fun _ => π (v k)) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert a t ha ih =>
        simp only [Finset.prod_insert ha]
        exact (hk a).mul ih
    exact hp Finset.univ
  · have key : ∀ k, s (fun _ => π ((v + γ) k)) = (X.eps (γ k) : ℂ) ^ q *
        cexp ((q : ℂ) * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) *
          s (fun _ => π (v k)) := by
      intro k
      have h := hs.2 (fun _ => π (γ k)) (fun _ => hπ.2.1 _ (hγ k)) (fun _ => π (v k))
      have e1 : (fun _ : Fin 1 => π ((v + γ) k)) = (fun _ => π (v k)) + (fun _ => π (γ k)) := by
        funext; simp [map_add]
      rw [e1, h]
      simp only [HC, Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, hπ.2.2.1,
        hπ.2.2.2 _ (hγ k), pow_one]
      push_cast
      ring_nf
    unfold s0
    simp_rw [key]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, ← Complex.exp_sum]
    congr 3
    simp only [HC, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_div]
end ReciprocityTheory.ChartRestriction.G.I2
