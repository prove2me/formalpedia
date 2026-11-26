-- Prove2me | solution 1 for P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:33.873322+00:00
-- url     : https://prove2.me/submissions/9f134162-e133-44ed-92b6-4ae599cef568

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_FixedOrderFactor_sum_rootOfUnity_mul

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : 0 < s) (c : ℕ) :
    ∑ t ∈ range s, orbitAvg s (c * t) = if s ∣ c then (s : ℂ) else 0 := by
  unfold orbitAvg
  rw [← mul_sum, sum_comm]
  have hu : ∀ u ∈ (range s).filter s.Coprime,
      ∑ t ∈ range s, rootOfUnity s (u * (c * t)) = if s ∣ c then (s : ℂ) else 0 := by
    intro u hu
    have hcop : s.Coprime u := (mem_filter.1 hu).2
    simp_rw [show ∀ t, u * (c * t) = (u * c) * t from fun t => by ring]
    rw [sum_rootOfUnity_mul hs]
    by_cases hc : s ∣ c
    · rw [ite_eq_left_iff.2 (fun h => absurd (dvd_mul_of_dvd_right hc u) h),
        ite_eq_left_iff.2 (fun h => absurd hc h)]
    · have hn : ¬ s ∣ u * c := fun h => hc (hcop.dvd_of_dvd_mul_left h)
      rw [ite_eq_right_iff.2 (fun h => absurd h hn), ite_eq_right_iff.2 (fun h => absurd h hc)]
  rw [sum_congr rfl hu, sum_const, nsmul_eq_mul]
  have hcard : ((range s).filter s.Coprime).card = s.totient := (Nat.totient_eq_card_coprime s).symm
  rw [hcard]
  have : (s.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hs).ne'
  field_simp
end FixedOrderFactor
