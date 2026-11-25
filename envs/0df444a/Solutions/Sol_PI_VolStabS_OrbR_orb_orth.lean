-- Prove2me | solution 1 for PI.VolStabS.OrbR.orb_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:55.347202+00:00
-- url     : https://prove2.me/submissions/b83cf3d8-bd0f-4432-a252-31137932b30a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_OrbRing
import Theorems.Thm_PI_VolStabS_OrbR_hform_mem
import Theorems.Thm_PI_VolStabS_OrbR_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabS.OrbR
theorem _root_.solution (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det) :
    ∀ (k : ℕ) (x y : Fin k → Fin n → S), (∀ i j, i ≠ j → hform s J (x i) (x j) = 0) →
      (∀ i j, hform s J (y i) (y j) = hform s J (x i) (x j)) →
      (∀ i, IsUnit (hform s J (x i) (x i))) →
      (∀ i (t : S), ∃ lam, lam * s lam = 1 ∧ IsUnit (hform s J (x i) (x i) - s lam * t)) →
      ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ x i = y i := by
  intro k
  induction k with
  | zero =>
    intro x y _ _ _ _
    exact ⟨1, one_mem _, fun i => i.elim0⟩
  | succ k ih =>
    intro x y horth hgram hunit hlam
    obtain ⟨g, hg, hgx⟩ := ih (fun i => x i.castSucc) (fun i => y i.castSucc)
      (fun i j hij => horth _ _ (fun h => hij (Fin.castSucc_injective _ h))) (fun i j => hgram _ _)
      (fun i => hunit _) (fun i t => hlam _ t)
    have hpres := hform_mem s J g hg
    have hab : hform s J (y (Fin.last k)) (y (Fin.last k)) =
        hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k)) ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k)) := by
      rw [hpres, hgram]
    have hu : IsUnit (hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k))
        ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k))) := by
      rw [hpres]
      exact hunit _
    obtain ⟨lam, hl1, hl2⟩ := hlam (Fin.last k)
      (hform s J (y (Fin.last k)) ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k)))
    have hc : IsUnit (hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k))
        ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k)) - s lam *
        hform s J (y (Fin.last k)) ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k))) := by
      rw [hpres]
      exact hl2
    obtain ⟨g', hg', hg'a, hg'fix⟩ := step s J hs hJ hdet _ _ hab hu lam hl1 hc
    refine ⟨g' * g, mul_mem hg' hg, fun i => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    induction i using Fin.lastCases with
    | last => exact hg'a
    | cast j =>
      have hj := hgx j
      rw [hj]
      apply hg'fix
      · rw [← hj, hpres]
        exact horth _ _ (Fin.castSucc_lt_last j).ne'
      · rw [hgram]
        exact horth _ _ (Fin.castSucc_lt_last j).ne'
end PI.VolStabS.OrbR
