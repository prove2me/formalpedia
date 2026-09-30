-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_ideal_order
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T14:55:32.430376+00:00
-- url     : https://prove2.me/submissions/5270f51d-91f9-4a12-a10b-78dcfb27e9b8

import Theorems.Thm_WeierstrassEllipticZeta_finite_contact_ideal_sum
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension

noncomputable section
open WeierstrassEllipticZeta

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (m n : V → ℕ) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (m v)
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    (I ≤ J ↔ ∀ v : V, n v ≤ m v) ∧
      (I = J ↔ m = n) ∧
      (I < J ↔ (∀ v : V, n v ≤ m v) ∧ ∃ v : V, n v < m v) := by
  classical
  have horder (a b : V → ℕ) :
      (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (a v)) ≤
          (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (b v)) ↔
        ∀ v : V, b v ≤ a v := by
    constructor
    · intro hle
      have hdim := (finite_contact_ideal_sum g₂ g₃ c V a b).2.2.1
      rw [sup_eq_right.mpr hle] at hdim
      have hsum : (∑ v : V, min (a v) (b v)) = ∑ v : V, b v :=
        hdim.symm.trans (elliptic_extension_contact_quotient_dimension g₂ g₃ c V b).2.1
      intro v
      by_contra hv
      have hlt : (∑ w : V, min (a w) (b w)) < ∑ w : V, b w := by
        apply Finset.sum_lt_sum (fun w _ => min_le_right (a w) (b w))
        exact ⟨v, Finset.mem_univ v, by omega⟩
      omega
    · intro hle p hp
      apply (Submodule.mem_iInf _).mpr
      intro v
      have hmono : extensionChartContactIdeal g₂ g₃ c v.val (a v) ≤
          extensionChartContactIdeal g₂ g₃ c v.val (b v) :=
        Ideal.span_mono fun q hq j hj => hq j (hj.trans_le (hle v))
      exact hmono ((Submodule.mem_iInf _).mp hp v)
  refine ⟨horder m n, ?_, ?_⟩
  · constructor
    · intro h
      funext v
      exact le_antisymm ((horder n m).mp h.ge v) ((horder m n).mp h.le v)
    · intro h
      subst n
      rfl
  · rw [lt_iff_le_not_ge, horder m n, horder n m]
    constructor
    · rintro ⟨hle, hnot⟩
      obtain ⟨v, hv⟩ := not_forall.mp hnot
      exact ⟨hle, v, Nat.lt_of_not_ge hv⟩
    · rintro ⟨hle, v, hv⟩
      exact ⟨hle, fun h => (Nat.not_le_of_gt hv) (h v)⟩

