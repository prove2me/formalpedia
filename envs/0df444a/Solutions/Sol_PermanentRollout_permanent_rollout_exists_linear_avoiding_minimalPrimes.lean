-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_exists_linear_avoiding_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/df476143-dee7-4ee5-855d-7890d36584e7

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (hcoordinate : ∀ p ∈ I.minimalPrimes,
      ∃ i : Fin m, MvPolynomial.X i ∉ p) :
    ∃ c : Fin m → ℂ,
      ∀ p ∈ I.minimalPrimes,
        (∑ i, c i • MvPolynomial.X i) ∉ p := by
  classical
  let index := {p : Ideal (MvPolynomial (Fin m) ℂ) //
    p ∈ I.minimalPrimes}
  letI : Fintype index :=
    (I.finite_minimalPrimes_of_isNoetherianRing
      (MvPolynomial (Fin m) ℂ)).fintype
  let bad : index → Submodule ℂ (Fin m → ℂ) :=
    fun p => (p.val.restrictScalars ℂ).comap
      (permanentRolloutLinearCoordinateCombination m)
  have hbad : ∀ p : index, bad p ≠ ⊤ := by
    intro p htop
    obtain ⟨i, hi⟩ := hcoordinate p.val p.property
    let unit : Fin m → ℂ := Pi.single i (1 : ℂ)
    have hsingle : unit ∈ bad p := by
      rw [htop]
      trivial
    apply hi
    change
      (∑ j, unit j •
        MvPolynomial.X j) ∈ p.val at hsingle
    simpa [unit] using hsingle
  obtain ⟨c, hc⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨c, ?_⟩
  intro p hp
  exact hc ⟨p, hp⟩
end PermanentRollout
