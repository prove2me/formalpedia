-- Prove2me | solution 1 for PandoraBO.Private20261023.policy_capped_integrability_and_excess
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:23.296741+00:00
-- url     : https://prove2.me/submissions/bab84750-9f88-4ef7-903c-7b1659887e44

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_policy_rollout_structural
import Theorems.Thm_PandoraBO_Private20261023_policy_opening_regular
import Theorems.Thm_PandoraBO_Private20261023_coordinate_nonanticipative_factorization
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Integrability and expected opened-box excess

Nonanticipation factors each opening indicator from its box reward. Distinct
observed boxes permit reindexing the occupied-slot sum by boxes, so the
reservation-root identities cancel expected excess against inspection cost.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace PandoraBO.Private20261023.CappedExcess

attribute [local instance] Classical.propDecidable

private theorem seed_probability : IsProbabilityMeasure seedLaw := by
  constructor
  simp [seedLaw, Real.volume_Icc]

private theorem joint_probability {n : ℕ} (M : Instance n) :
    IsProbabilityMeasure (jointLaw M) := by
  letI : ∀ i, IsProbabilityMeasure (M.law i) := M.law_probability
  letI : IsProbabilityMeasure seedLaw := seed_probability
  dsimp [jointLaw]
  infer_instance

private theorem coordinate_integrable {n : ℕ} (M : Instance n) (i : Box n) :
    Integrable (fun ω : Outcome n => ω.1 i) (jointLaw M) := by
  letI : ∀ j, IsProbabilityMeasure (M.law j) := M.law_probability
  letI : IsProbabilityMeasure seedLaw := seed_probability
  have heval : MeasurePreserving (fun ω : Outcome n => ω.1 i)
      (jointLaw M) (M.law i) := by
    simpa only [jointLaw, Function.comp_def, Function.eval] using
      (measurePreserving_eval M.law i).comp
        (measurePreserving_fst (μ := Measure.pi M.law) (ν := seedLaw))
  simpa only [Function.comp_def] using
    heval.integrable_comp_of_integrable (M.reward_integrable i)

def openedIndicator {n : ℕ} (π : Policy n) (i : Box n) (ω : Outcome n) : ℝ :=
  if wasOpened (terminalHistory π ω) i then 1 else 0

def slotSurplus {n : ℕ} (π : Policy n) (z : Box n → ℝ) (ω : Outcome n) : ℝ :=
  ∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
    max (observedReward (terminalHistory π ω) k -
      z (observedBox (terminalHistory π ω) k)) 0 else 0

private theorem indicator_measurable {n : ℕ} (π : Policy n) (i : Box n) :
    Measurable (openedIndicator π i) :=
  Measurable.ite (policy_opening_regular π i).1 measurable_const measurable_const

private theorem indicator_norm_le {n : ℕ} (π : Policy n) (i : Box n) (ω : Outcome n) :
    ‖openedIndicator π i ω‖ ≤ 1 := by
  by_cases h : wasOpened (terminalHistory π ω) i <;> simp [openedIndicator, h]

private theorem indicator_integrable {n : ℕ} (M : Instance n) (π : Policy n) (i : Box n) :
    Integrable (openedIndicator π i) (jointLaw M) := by
  letI : IsProbabilityMeasure (jointLaw M) := joint_probability M
  exact (integrable_const (1 : ℝ)).mono' (indicator_measurable π i).aestronglyMeasurable
    (ae_of_all _ (indicator_norm_le π i))

private theorem indicator_nonanticipative {n : ℕ} (π : Policy n) (i : Box n)
    (r r' : Box n → ℝ) (u : ℝ) (hr : ∀ j, j ≠ i → r j = r' j) :
    openedIndicator π i (r, u) = openedIndicator π i (r', u) := by
  unfold openedIndicator
  rw [(policy_opening_regular π i).2 r r' u hr]

private theorem boxExcess_integrable {n : ℕ} (M : Instance n) (π : Policy n)
    (z : Box n → ℝ) (i : Box n) :
    Integrable (fun ω : Outcome n => openedIndicator π i ω * max (ω.1 i - z i) 0)
      (jointLaw M) := by
  letI : IsProbabilityMeasure (jointLaw M) := joint_probability M
  have hex : Integrable (fun ω : Outcome n => max (ω.1 i - z i) 0) (jointLaw M) :=
    ((coordinate_integrable M i).sub (integrable_const (z i))).sup (integrable_const 0)
  exact hex.bdd_mul (indicator_measurable π i).aestronglyMeasurable
    (ae_of_all _ (indicator_norm_le π i))

private theorem boxCost_integrable {n : ℕ} (M : Instance n) (π : Policy n) (i : Box n) :
    Integrable (fun ω : Outcome n => openedIndicator π i ω * M.cost i) (jointLaw M) :=
  (indicator_integrable M π i).mul_const (M.cost i)

private theorem sum_slots_eq_sum_boxes {n : ℕ} (h : History n) (hh : validHistory h)
    (f : Box n → ℝ) :
    (∑ k : Fin (n + 1), if occupied h k then f (observedBox h k) else 0) =
      ∑ i : Box n, if wasOpened h i then f i else 0 := by
  let active : Finset (Fin (n + 1)) := Finset.univ.filter (occupied h)
  have hinj : Set.InjOn (observedBox h) active := by
    intro k hk l hl heq
    exact hh.2.2 k l (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2 heq
  have himage : active.image (observedBox h) = Finset.univ.filter (wasOpened h) := by
    ext i
    simp [active, wasOpened]
  calc
    (∑ k : Fin (n + 1), if occupied h k then f (observedBox h k) else 0) =
        ∑ k ∈ active, f (observedBox h k) := by
      simp only [active, Finset.sum_filter]
    _ = ∑ i ∈ active.image (observedBox h), f i := (Finset.sum_image hinj).symm
    _ = ∑ i : Box n, if wasOpened h i then f i else 0 := by
      rw [himage]
      simp only [Finset.sum_filter]

private theorem cost_eq_boxSum {n : ℕ} (M : Instance n) (π : Policy n) (ω : Outcome n) :
    terminalCost M π ω = ∑ i : Box n, openedIndicator π i ω * M.cost i := by
  unfold terminalCost historyCost
  rw [sum_slots_eq_sum_boxes (terminalHistory π ω) (policy_rollout_structural M π ω).1]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : wasOpened (terminalHistory π ω) i <;> simp [openedIndicator, h]

private theorem surplus_eq_boxSum {n : ℕ} (M : Instance n) (π : Policy n)
    (z : Box n → ℝ) (ω : Outcome n) :
    slotSurplus π z ω = ∑ i : Box n, openedIndicator π i ω * max (ω.1 i - z i) 0 := by
  have hvalid := (policy_rollout_structural M π ω).1
  have hsample := (policy_rollout_structural M π ω).2.1
  calc
    slotSurplus π z ω =
        ∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
          max (ω.1 (observedBox (terminalHistory π ω) k) -
            z (observedBox (terminalHistory π ω) k)) 0 else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : occupied (terminalHistory π ω) k
      · simp only [if_pos h, hsample k h]
      · simp only [if_neg h]
    _ = ∑ i : Box n, if wasOpened (terminalHistory π ω) i then max (ω.1 i - z i) 0 else 0 :=
      sum_slots_eq_sum_boxes (terminalHistory π ω) hvalid (fun i => max (ω.1 i - z i) 0)
    _ = ∑ i : Box n, openedIndicator π i ω * max (ω.1 i - z i) 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : wasOpened (terminalHistory π ω) i <;> simp [openedIndicator, h]

private theorem cappedPayoff_integrable {n : ℕ} (M : Instance n) (z : Box n → ℝ) :
    Integrable (fun ω : Outcome n => fullInformationPayoff (fun i => min (ω.1 i) (z i)))
      (jointLaw M) := by
  letI : IsProbabilityMeasure (jointLaw M) := joint_probability M
  have hcoord : ∀ i : Box n,
      Integrable (fun ω : Outcome n => min (ω.1 i) (z i)) (jointLaw M) :=
    fun i => (coordinate_integrable M i).inf (integrable_const (z i))
  have hfold : ∀ (ks : List (Box n)) (v : Outcome n → ℝ), Integrable v (jointLaw M) →
      Integrable (fun ω => ks.foldl
        (fun incumbent i => max incumbent (min (ω.1 i) (z i))) (v ω)) (jointLaw M) := by
    intro ks
    induction ks with
    | nil => intro v hv; exact hv
    | cons k ks ih =>
        intro v hv
        exact ih (fun ω => max (v ω) (min (ω.1 k) (z k))) (hv.sup (hcoord k))
  exact hfold (List.finRange (n + 1)) (fun ω => min (ω.1 0) (z 0)) (hcoord 0)

private theorem surplus_integrable {n : ℕ} (M : Instance n) (π : Policy n) (z : Box n → ℝ) :
    Integrable (slotSurplus π z) (jointLaw M) := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ => boxExcess_integrable M π z i)
  exact hsum.congr (ae_of_all _ (fun ω => (surplus_eq_boxSum M π z ω).symm))

private theorem expected_box_excess {n : ℕ} (M : Instance n) (multiplier : ℝ)
    (z : Box n → ℝ) (hz : reservationIndices M multiplier z) (π : Policy n) (i : Box n) :
    (∫ ω : Outcome n, openedIndicator π i ω * max (ω.1 i - z i) 0 ∂jointLaw M) =
      multiplier * ∫ ω : Outcome n, openedIndicator π i ω * M.cost i ∂jointLaw M := by
  rw [coordinate_nonanticipative_factorization M i (openedIndicator π i)
    (fun y => max (y - z i) 0) (indicator_nonanticipative π i)]
  have hroot : (∫ y : ℝ, max (y - z i) 0 ∂M.law i) = multiplier * M.cost i := hz i
  rw [hroot, integral_mul_const]
  exact mul_left_comm _ _ _

private theorem expected_surplus {n : ℕ} (M : Instance n) (multiplier : ℝ)
    (z : Box n → ℝ) (hz : reservationIndices M multiplier z) (π : Policy n) :
    (∫ ω : Outcome n, slotSurplus π z ω ∂jointLaw M) = multiplier * expectedCost M π := by
  calc
    (∫ ω : Outcome n, slotSurplus π z ω ∂jointLaw M) =
        ∫ ω : Outcome n, ∑ i : Box n, openedIndicator π i ω * max (ω.1 i - z i) 0 ∂jointLaw M := by
      exact integral_congr_ae (ae_of_all _ (surplus_eq_boxSum M π z))
    _ = ∑ i : Box n, ∫ ω : Outcome n,
        openedIndicator π i ω * max (ω.1 i - z i) 0 ∂jointLaw M :=
      integral_finsetSum Finset.univ (fun i _ => boxExcess_integrable M π z i)
    _ = ∑ i : Box n, multiplier *
        ∫ ω : Outcome n, openedIndicator π i ω * M.cost i ∂jointLaw M := by
      apply Finset.sum_congr rfl
      intro i hi
      exact expected_box_excess M multiplier z hz π i
    _ = multiplier * ∑ i : Box n,
        ∫ ω : Outcome n, openedIndicator π i ω * M.cost i ∂jointLaw M := by
      rw [Finset.mul_sum]
    _ = multiplier * ∫ ω : Outcome n, ∑ i : Box n,
        openedIndicator π i ω * M.cost i ∂jointLaw M := by
      rw [integral_finsetSum Finset.univ (fun i _ => boxCost_integrable M π i)]
    _ = multiplier * expectedCost M π := by
      unfold expectedCost
      congr 1
      exact integral_congr_ae (ae_of_all _ (fun ω => (cost_eq_boxSum M π ω).symm))

theorem capped_integrability_and_excess_core {n : ℕ} (M : Instance n) (multiplier : ℝ)
    (z : Box n → ℝ) (hz : reservationIndices M multiplier z) (π : Policy n) :
    Integrable (fun ω : Outcome n => fullInformationPayoff (fun i => min (ω.1 i) (z i)))
      (jointLaw M) ∧
    Integrable (fun ω : Outcome n => ∑ k : Fin (n + 1),
      if occupied (terminalHistory π ω) k then
        max (observedReward (terminalHistory π ω) k -
          z (observedBox (terminalHistory π ω) k)) 0 else 0) (jointLaw M) ∧
    (∫ ω : Outcome n, ∑ k : Fin (n + 1),
      if occupied (terminalHistory π ω) k then
        max (observedReward (terminalHistory π ω) k -
          z (observedBox (terminalHistory π ω) k)) 0 else 0 ∂jointLaw M) =
      multiplier * expectedCost M π := by
  exact ⟨cappedPayoff_integrable M z, surplus_integrable M π z,
    expected_surplus M multiplier z hz π⟩

end PandoraBO.Private20261023.CappedExcess

attribute [local instance] Classical.propDecidable

theorem solution {n : ℕ} (M : PandoraBO.Instance n) (multiplier : ℝ)
    (z : PandoraBO.Box n → ℝ) (hz : PandoraBO.reservationIndices M multiplier z)
    (π : PandoraBO.Policy n) :
    Integrable (fun ω : PandoraBO.Outcome n =>
      PandoraBO.fullInformationPayoff (fun i => min (ω.1 i) (z i))) (PandoraBO.jointLaw M) ∧
    Integrable (fun ω : PandoraBO.Outcome n => ∑ k : Fin (n + 1),
      if PandoraBO.occupied (PandoraBO.terminalHistory π ω) k then
        max (PandoraBO.observedReward (PandoraBO.terminalHistory π ω) k -
          z (PandoraBO.observedBox (PandoraBO.terminalHistory π ω) k)) 0 else 0)
      (PandoraBO.jointLaw M) ∧
    (∫ ω : PandoraBO.Outcome n, ∑ k : Fin (n + 1),
      if PandoraBO.occupied (PandoraBO.terminalHistory π ω) k then
        max (PandoraBO.observedReward (PandoraBO.terminalHistory π ω) k -
          z (PandoraBO.observedBox (PandoraBO.terminalHistory π ω) k)) 0 else 0
      ∂PandoraBO.jointLaw M) = multiplier * PandoraBO.expectedCost M π := by
  exact PandoraBO.Private20261023.CappedExcess.capped_integrability_and_excess_core M multiplier z hz π
