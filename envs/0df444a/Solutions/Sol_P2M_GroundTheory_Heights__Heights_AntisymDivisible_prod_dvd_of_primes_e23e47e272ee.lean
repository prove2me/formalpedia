-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_prod_dvd_of_primes_e23e47e272ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:19.983895+00:00
-- url     : https://prove2.me/submissions/0fdb4282-cdc7-44a2-b709-643f8fc4a0b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (P : MvPolynomial σ ℝ) (hp : ∀ i ∈ s, Prime (f i))
    (hnd : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → ¬ f i ∣ f k) (hd : ∀ i ∈ s, f i ∣ P) :
    ∏ i ∈ s, f i ∣ P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    obtain ⟨Q, hQ⟩ := ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))
      (fun a ha b hb hab => hnd a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab)
      (fun k hk => hd k (Finset.mem_insert_of_mem hk))
    have hpi := hp i (Finset.mem_insert_self i s)
    have hiP := hd i (Finset.mem_insert_self i s)
    rw [hQ] at hiP
    rcases hpi.dvd_or_dvd hiP with h | h
    · exfalso
      obtain ⟨k, hk, hik⟩ := (hpi.dvd_finsetProd_iff f).1 h
      exact hnd i (Finset.mem_insert_self i s) k (Finset.mem_insert_of_mem hk)
        (by rintro rfl; exact hi hk) hik
    · obtain ⟨R, rfl⟩ := h
      exact ⟨R, by rw [hQ]; ring⟩
end GroundTheory.Heights₂.Heights.AntisymDivisible
