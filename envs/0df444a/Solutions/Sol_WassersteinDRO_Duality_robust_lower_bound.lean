-- Prove2me | solution 1 for WassersteinDRO.Duality.robust_lower_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:20:22.189373+00:00
-- url     : https://prove2.me/submissions/ad75c6e3-e4c9-4a98-927b-5f147b1ccd91

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The real line equipped with the trivial σ-algebra `⊥`. -/
def aux_rlb_E : Type := ℝ

noncomputable instance aux_rlb_nacg : NormedAddCommGroup aux_rlb_E :=
  inferInstanceAs (NormedAddCommGroup ℝ)

instance aux_rlb_ms : MeasurableSpace aux_rlb_E := ⊥

/-- A non-constant loss. -/
noncomputable def aux_rlb_loss (x : aux_rlb_E) : ℝ := by
  classical exact if x = 0 then 1 else 0

def aux_rlb_pt : aux_rlb_E := (1 : ℝ)

lemma aux_rlb_pt_ne : aux_rlb_pt ≠ 0 := by
  change (1 : ℝ) ≠ 0
  exact one_ne_zero

lemma aux_rlb_loss_zero : aux_rlb_loss 0 = 1 := by
  simp [aux_rlb_loss]

lemma aux_rlb_loss_pt : aux_rlb_loss aux_rlb_pt = 0 := by
  simp [aux_rlb_loss, aux_rlb_pt_ne]

lemma aux_rlb_measure_of_nonempty (Q : Measure aux_rlb_E) (s : Set aux_rlb_E)
    (hs : s.Nonempty) : Q s = Q Set.univ := by
  rw [← measure_toMeasurable s]
  have hm : MeasurableSet (toMeasurable Q s) := measurableSet_toMeasurable Q s
  rcases (MeasurableSpace.measurableSet_bot_iff).mp hm with h | h
  · exfalso
    obtain ⟨x, hx⟩ := hs
    have : x ∈ toMeasurable Q s := subset_toMeasurable Q s hx
    rw [h] at this
    exact this
  · rw [h]

lemma aux_rlb_not_integrable (Q : Measure aux_rlb_E) (hQ : Q Set.univ = 1) :
    ¬ Integrable aux_rlb_loss Q := by
  intro hI
  obtain ⟨g, hg, hfg⟩ := hI.aestronglyMeasurable
  obtain ⟨c, rfl⟩ := stronglyMeasurable_bot_iff.mp hg
  have hne : {x | aux_rlb_loss x ≠ c}.Nonempty := by
    by_cases hc : c = 1
    · refine ⟨aux_rlb_pt, ?_⟩
      change aux_rlb_loss aux_rlb_pt ≠ c
      rw [aux_rlb_loss_pt, hc]
      exact zero_ne_one
    · refine ⟨0, ?_⟩
      change aux_rlb_loss 0 ≠ c
      rw [aux_rlb_loss_zero]
      exact fun h => hc h.symm
  have h0 : Q {x | aux_rlb_loss x ≠ c} = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hfg
    simpa using hfg
  rw [aux_rlb_measure_of_nonempty Q _ hne, hQ] at h0
  exact one_ne_zero h0

end WassersteinDRO.Duality

open WassersteinDRO.Duality

theorem solution : ¬ (∀ {E : Type} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ),
    (⨆ (θ : Fin N → E)
        (_ : ∀ i, ξhat i + θ i ∈ Ξ)
        (_ : (∑ i, ‖θ i‖ ^ p) / (N : ℝ) ≤ ε ^ p),
        (((∑ i, ℓ (ξhat i + θ i)) / (N : ℝ) : ℝ) : EReal))
      ≤ worstCaseRisk ε p Ξ (empiricalDistribution ξhat) ℓ) := by
  intro h
  have H := @h aux_rlb_E aux_rlb_ms aux_rlb_nacg 0 1 le_rfl le_rfl Set.univ isClosed_univ
    1 one_pos (fun _ => 0) aux_rlb_loss
  have hR : worstCaseRisk (0 : ℝ) 1 (Set.univ : Set aux_rlb_E)
      (empiricalDistribution (fun _ : Fin 1 => (0 : aux_rlb_E))) aux_rlb_loss = ⊥ := by
    unfold worstCaseRisk
    refine iSup_eq_bot.mpr fun Q => iSup_eq_bot.mpr fun hQ => iSup_eq_bot.mpr fun hI => ?_
    exact absurd hI (aux_rlb_not_integrable Q hQ.1)
  rw [hR] at H
  have hL : ((((∑ i : Fin 1, aux_rlb_loss ((fun _ => (0 : aux_rlb_E)) i + (0 : aux_rlb_E))) /
      ((1 : ℕ) : ℝ) : ℝ) : EReal)) ≤ ⊥ := by
    refine le_trans ?_ H
    refine le_iSup_of_le (fun _ => (0 : aux_rlb_E)) ?_
    refine le_iSup_of_le (fun _ => by simp) ?_
    refine le_iSup_of_le ?_ le_rfl
    simp
  have : ((((∑ i : Fin 1, aux_rlb_loss ((fun _ => (0 : aux_rlb_E)) i + (0 : aux_rlb_E))) /
      ((1 : ℕ) : ℝ) : ℝ) : EReal)) ≠ ⊥ := EReal.coe_ne_bot _
  exact this (le_bot_iff.mp hL)
