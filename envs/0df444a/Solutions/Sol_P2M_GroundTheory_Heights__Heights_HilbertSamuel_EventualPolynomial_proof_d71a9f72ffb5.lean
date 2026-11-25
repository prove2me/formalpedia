-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_proof_d71a9f72ffb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:13.190337+00:00
-- url     : https://prove2.me/submissions/c85cc6c5-744f-482f-b76c-b601f7aa5c21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_newton_2741b236fc44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_eq_mixedDiff_6117ca062b3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open EventualPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace EventualPolynomial
theorem _root_.solution : EventualPolynomial.Statement := by
  intro K _ _ n f hf
  have hall : ∀ᶠ m in Filter.atTop, ∀ v : Fin (n + 1) → K,
      mixedDiff (fun i => (Pi.single (v i) 1 : K → ℤ)) f m = 0 :=
    Filter.eventually_all.mpr fun v => hf _
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp hall
  set c : ℕ := ∑ k, (m₁ k).toNat with hcdef
  have hc : ∀ k, m₁ k ≤ (c : ℤ) := fun k => by
    have h1 : (m₁ k).toNat ≤ c := single_le_sum (f := fun k => (m₁ k).toNat) (fun _ _ => Nat.zero_le _) (mem_univ k)
    have h2 := Int.self_le_toNat (m₁ k)
    omega
  have hL : ∀ L : List K, L.length = n + 1 →
      listDiff L (fun t => (f (fun k => (c : ℤ) + t k) : ℚ)) = 0 := by
    intro L hlen
    funext t
    rw [listDiff_eq_mixedDiff]
    obtain ⟨v, rfl⟩ : ∃ v : Fin (n + 1) → K, List.ofFn v = L :=
      ⟨fun i => L[i.val]'(by have := i.isLt; omega),
        List.ext_getElem (by simp [hlen]) fun j _ _ => by rw [List.getElem_ofFn]⟩
    have hv := hm₁ (fun k => (c : ℤ) + t k + (List.ofFn v).count k)
      (fun k => by have := hc k; dsimp; omega) v
    have hmap : (List.ofFn v).map (fun k => (Pi.single k 1 : K → ℤ)) =
        List.ofFn (fun i => (Pi.single (v i) 1 : K → ℤ)) := by rw [List.map_ofFn]; rfl
    rw [hmap]
    change ((mixedDiff (fun i => (Pi.single (v i) 1 : K → ℤ)) f _ : ℤ) : ℚ) = 0
    rw [hv]
    simp
  obtain ⟨P, hdeg, -, hval⟩ := newton c univ n _ hL
  refine ⟨P, c, hdeg, fun a ha => ?_⟩
  have h1 : ((f fun k => (c : ℤ) + ((a k - c : ℕ) : ℤ) : ℤ) : ℚ) =
      eval (fun i => ((a i - c : ℕ) : ℚ) + c) P :=
    hval (fun k => a k - c) fun i hi => absurd (mem_univ i) hi
  have e1 : (fun k => (c : ℤ) + ((a k - c : ℕ) : ℤ)) = fun k => (a k : ℤ) :=
    funext fun k => by have := ha k; omega
  have e2 : (fun i => ((a i - c : ℕ) : ℚ) + c) = fun k => (a k : ℚ) :=
    funext fun k => by rw [Nat.cast_sub (ha k)]; ring
  rw [e1, e2] at h1
  exact h1
end EventualPolynomial
end GroundTheory.Heights₂.Heights.HilbertSamuel
