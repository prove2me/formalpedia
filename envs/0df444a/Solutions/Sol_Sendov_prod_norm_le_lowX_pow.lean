-- Prove2me | solution 1 for Sendov.prod_norm_le_lowX_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:02.871061+00:00
-- url     : https://prove2.me/submissions/221bc9aa-8fe7-41fa-ad6a-4a7e2d56050f

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_lowX_nonneg
import Theorems.Thm_Sendov_norm_le_lowX
import Theorems.Thm_Sendov_prod_map_norm_nonneg
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) :
    ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
        ≤ lowX a t ^ q.card := by
  intro q
  induction q using Multiset.induction_on with
  | empty => intro _; simp
  | cons v s ih =>
    intro hq
    have hv := hq v (Multiset.mem_cons_self v s)
    have hs : ∀ u ∈ s, ‖u‖ ≤ 1 := fun u hu => hq u (Multiset.mem_cons_of_mem hu)
    have hX0 : 0 ≤ lowX a t := lowX_nonneg ha0 ha1 ht0
    have h3 : 0 ≤ (s.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod :=
      prod_map_norm_nonneg s _
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖
          * (s.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
        ≤ lowX a t * lowX a t ^ s.card :=
          mul_le_mul (norm_le_lowX ha0 ha1 ht0 hv) (ih hs) h3 hX0
      _ = lowX a t ^ s.card * lowX a t := by ring
end Sendov
