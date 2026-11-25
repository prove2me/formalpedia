-- Prove2me | solution 1 for PI.VolStabW.OrbR.orb_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:36.601605+00:00
-- url     : https://prove2.me/submissions/a74f8f1f-f156-4949-81ae-35c2be326e12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbRing
import Theorems.Thm_PI_VolStabW_OrbR_hform_mem
import Theorems.Thm_PI_VolStabW_OrbR_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabW.OrbR
theorem _root_.solution (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det) :
    ∀ (k : ℕ) (x y : Fin k → Fin n → S), (∀ i j, i ≠ j → hform s J (x i) (x j) = 0) →
      (∀ i j, hform s J (y i) (y j) = hform s J (x i) (x j)) →
      (∀ i, IsUnit (hform s J (x i) (x i))) →
      (∀ i (t : S), ∃ lam, lam * s lam = 1 ∧ IsUnit (hform s J (x i) (x i) - s lam * t)) →
      ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ x i = y i := by
  intro k
  induction k with
  | zero => intro x y _ _ _ _; exact ⟨1, one_mem _, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro x y ho hg hu hl
    obtain ⟨g', hg'U, hg'⟩ := ih (fun i => x i.succ) (fun i => y i.succ)
      (fun i j hij => ho _ _ (fun e => hij (Fin.succ_injective _ e))) (fun i j => hg _ _)
      (fun i => hu _) (fun i t => hl _ t)
    obtain ⟨a, ha⟩ : ∃ a, (g' : Matrix (Fin n) (Fin n) S) *ᵥ x 0 = a := ⟨_, rfl⟩
    have haa : hform s J a a = hform s J (x 0) (x 0) := by rw [← ha]; exact hform_mem s J g' hg'U _ _
    obtain ⟨lam, hlam, hc⟩ := hl 0 (hform s J (y 0) a)
    rw [← haa] at hc
    obtain ⟨g1, hg1U, hg1a, hg1z⟩ := step s J hs hJ hdet a (y 0) (by rw [haa]; exact hg 0 0)
      (haa ▸ hu 0) lam hlam hc
    refine ⟨g1 * g', mul_mem hg1U hg'U, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Units.val_mul, ← mulVec_mulVec, ha]; exact hg1a
    · have hi := hg' i
      rw [Units.val_mul, ← mulVec_mulVec, hi]
      apply hg1z
      · rw [← hi, ← ha, hform_mem s J g' hg'U]; exact ho 0 i.succ (Fin.succ_ne_zero i).symm
      · rw [hg 0 i.succ]; exact ho 0 i.succ (Fin.succ_ne_zero i).symm
end PI.VolStabW.OrbR
