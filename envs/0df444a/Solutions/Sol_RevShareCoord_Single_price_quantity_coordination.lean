-- Prove2me | solution 1 for RevShareCoord.Single.price_quantity_coordination
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:01:13.517149+00:00
-- url     : https://prove2.me/submissions/e81db066-0267-4e72-8894-b688152d8038

import Mathlib
import Definitions.Def_RevShareCoord_Single_Newsvendor
import Definitions.Def_RevShareCoord_Single_PriceQuantity



namespace RevShareCoord.Single

theorem bb_core (p c φ q D : ℝ) :
    bbRetailerRealized p (p * (1 - φ)) (p * (1 - φ) + φ * c) q D =
        rsRetailerRealized p φ (φ * c) q D ∧
      bbSupplierRealized (p * (1 - φ)) (p * (1 - φ) + φ * c) c q D =
        rsSupplierRealized p φ (φ * c) c q D := by
  unfold bbRetailerRealized rsRetailerRealized bbSupplierRealized rsSupplierRealized
  rcases le_total q D with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; constructor <;> ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; constructor <;> ring

theorem pq_core (Rev : ℝ → ℝ → ℝ) (c φ : ℝ) (hc : 0 < c)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (P : Set ℝ) (qI pI : ℝ) (hqI : 0 ≤ qI) (hpI : pI ∈ P)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => pqChainProfit Rev c x.1 x.2) (Set.Ici 0 ×ˢ P) (qI, pI))
    (huniq : ∀ x ∈ Set.Ici (0 : ℝ) ×ˢ P,
      IsMaxOn (fun x : ℝ × ℝ => pqChainProfit Rev c x.1 x.2) (Set.Ici 0 ×ˢ P) x → x = (qI, pI)) :
    (∀ q p : ℝ, pqRetailerProfit Rev φ (φ * c) q p = φ * pqChainProfit Rev c q p) ∧
    IsMaxOn (fun x : ℝ × ℝ => pqRetailerProfit Rev φ (φ * c) x.1 x.2) (Set.Ici 0 ×ˢ P) (qI, pI) ∧
    ∀ x ∈ Set.Ici (0 : ℝ) ×ˢ P,
      IsMaxOn (fun x : ℝ × ℝ => pqRetailerProfit Rev φ (φ * c) x.1 x.2) (Set.Ici 0 ×ˢ P) x →
        x = (qI, pI) := by
  have hid : ∀ q p : ℝ, pqRetailerProfit Rev φ (φ * c) q p = φ * pqChainProfit Rev c q p := by
    intro q p; unfold pqRetailerProfit pqChainProfit; ring
  refine ⟨hid, ?_, ?_⟩
  · intro y hy
    have := hopt hy
    simp only [Set.mem_setOf_eq, hid] at this ⊢
    exact mul_le_mul_of_nonneg_left this hφ0.le
  · intro x hx hmax
    apply huniq x hx
    intro y hy
    have := hmax hy
    simp only [Set.mem_setOf_eq, hid] at this ⊢
    exact le_of_mul_le_mul_left this hφ0

end RevShareCoord.Single

open RevShareCoord.Single


theorem solution (Rev : ℝ → ℝ → ℝ) (c φ : ℝ) (hc : 0 < c)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (P : Set ℝ) (qI pI : ℝ) (hqI : 0 ≤ qI) (hpI : pI ∈ P)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => pqChainProfit Rev c x.1 x.2) (Set.Ici 0 ×ˢ P) (qI, pI))
    (huniq : ∀ x ∈ Set.Ici (0 : ℝ) ×ˢ P,
      IsMaxOn (fun x : ℝ × ℝ => pqChainProfit Rev c x.1 x.2) (Set.Ici 0 ×ˢ P) x → x = (qI, pI)) :
    (∀ q p : ℝ, pqRetailerProfit Rev φ (φ * c) q p = φ * pqChainProfit Rev c q p) ∧
    IsMaxOn (fun x : ℝ × ℝ => pqRetailerProfit Rev φ (φ * c) x.1 x.2) (Set.Ici 0 ×ˢ P) (qI, pI) ∧
    ∀ x ∈ Set.Ici (0 : ℝ) ×ˢ P,
      IsMaxOn (fun x : ℝ × ℝ => pqRetailerProfit Rev φ (φ * c) x.1 x.2) (Set.Ici 0 ×ˢ P) x →
        x = (qI, pI) := by
  exact pq_core Rev c φ hc hφ0 hφ1 P qI pI hqI hpI hopt huniq
