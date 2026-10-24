-- Prove2me | solution 1 for PandoraBO.Private20261023.abstract_dual_convex_and_attains
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:48:41.108851+00:00
-- url     : https://prove2.me/submissions/52940537-1ba2-4a79-9d3c-e3b5b07ce269

import Definitions.Def_PandoraBO_Model
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set

namespace PandoraBO.Private20261023.DualEnvelope

/-- The dual envelope of a family of expected rewards and expected costs. -/
def envelope {ι : Type*} (R C : ι → ℝ) (B t : ℝ) : ℝ :=
  sSup (Set.range (fun i => R i - t * C i)) + t * B

/-- Abstract duality: pointwise finite affine envelopes are convex, and a
strictly feasible member forces attainment of their minimum on the half-line.
No existence of a maximizing member of the envelope is assumed. -/
theorem convex_and_attains {ι : Type*} (R C : ι → ℝ) (B : ℝ)
    (hbounded : ∀ t : ℝ, BddAbove (Set.range (fun i => R i - t * C i)))
    (hstrict : ∃ i : ι, C i < B) :
    (∀ x y a : ℝ, 0 ≤ a → a ≤ 1 →
      envelope R C B (a * x + (1 - a) * y) ≤
        a * envelope R C B x + (1 - a) * envelope R C B y) ∧
    ∃ t : ℝ, 0 ≤ t ∧ ∀ u : ℝ, 0 ≤ u → envelope R C B t ≤ envelope R C B u := by
  obtain ⟨i₀, hi₀⟩ := hstrict
  have hnonempty (t : ℝ) : (Set.range (fun i => R i - t * C i)).Nonempty :=
    ⟨R i₀ - t * C i₀, ⟨i₀, rfl⟩⟩
  have hbelow (i : ι) (t : ℝ) :
      R i - t * C i ≤ sSup (Set.range (fun j => R j - t * C j)) :=
    le_csSup (hbounded t) ⟨i, rfl⟩
  constructor
  · intro x y a ha ha₁
    have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha₁
    have hsup :
        sSup (Set.range (fun i => R i - (a * x + (1 - a) * y) * C i)) ≤
          a * sSup (Set.range (fun i => R i - x * C i)) +
            (1 - a) * sSup (Set.range (fun i => R i - y * C i)) := by
      apply csSup_le (hnonempty _)
      rintro _ ⟨i, rfl⟩
      calc
        R i - (a * x + (1 - a) * y) * C i =
            a * (R i - x * C i) + (1 - a) * (R i - y * C i) := by ring
        _ ≤ a * sSup (Set.range (fun j => R j - x * C j)) +
            (1 - a) * sSup (Set.range (fun j => R j - y * C j)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hbelow i x) ha)
            (mul_le_mul_of_nonneg_left (hbelow i y) hb)
    dsimp [envelope]
    nlinarith only [hsup]
  · have hsup_lsc : LowerSemicontinuous
        (fun t : ℝ => sSup (Set.range (fun i => R i - t * C i))) := by
      change LowerSemicontinuous (fun t : ℝ => ⨆ i, R i - t * C i)
      exact lowerSemicontinuous_ciSup hbounded
        (fun i => (continuous_const.sub (continuous_id.mul continuous_const)).lowerSemicontinuous)
    have hlsc : LowerSemicontinuous (envelope R C B) :=
      hsup_lsc.add (continuous_id.mul continuous_const).lowerSemicontinuous
    let d : ℝ := B - C i₀
    have hd : 0 < d := sub_pos.mpr hi₀
    let K : ℝ := max 0 ((envelope R C B 0 - R i₀) / d)
    have hK : 0 ≤ K := le_max_left _ _
    have htail (u : ℝ) (hu : K ≤ u) : envelope R C B 0 ≤ envelope R C B u := by
      have hquot : (envelope R C B 0 - R i₀) / d ≤ u :=
        (le_max_right _ _).trans hu
      have hmul : envelope R C B 0 - R i₀ ≤ u * d := (div_le_iff₀ hd).mp hquot
      have hlower : R i₀ - u * C i₀ + u * B ≤ envelope R C B u :=
        add_le_add (hbelow i₀ u) le_rfl
      dsimp [d] at hmul
      nlinarith only [hmul, hlower]
    have hne : (Set.Icc (0 : ℝ) K).Nonempty := ⟨0, ⟨le_rfl, hK⟩⟩
    have hcompact : IsCompact (Set.Icc (0 : ℝ) K) := isCompact_Icc
    obtain ⟨t, ht, hmin⟩ :=
      (hlsc.lowerSemicontinuousOn (Set.Icc 0 K)).exists_isMinOn hne hcompact
    refine ⟨t, ht.1, fun u hu => ?_⟩
    by_cases huK : u ≤ K
    · exact hmin ⟨hu, huK⟩
    · exact (hmin ⟨le_rfl, hK⟩).trans (htail u (le_of_not_ge huK))

end PandoraBO.Private20261023.DualEnvelope

/-- A standalone target exposing the abstract result without auxiliary definitions. -/
theorem solution {ι : Type*} (R C : ι → ℝ) (B : ℝ)
    (hbounded : ∀ t : ℝ, BddAbove (Set.range (fun i => R i - t * C i)))
    (hstrict : ∃ i : ι, C i < B) :
    (∀ x y a : ℝ, 0 ≤ a → a ≤ 1 →
      sSup (Set.range (fun i => R i - (a * x + (1 - a) * y) * C i)) +
          (a * x + (1 - a) * y) * B ≤
        a * (sSup (Set.range (fun i => R i - x * C i)) + x * B) +
        (1 - a) * (sSup (Set.range (fun i => R i - y * C i)) + y * B)) ∧
    ∃ t : ℝ, 0 ≤ t ∧ ∀ u : ℝ, 0 ≤ u →
      sSup (Set.range (fun i => R i - t * C i)) + t * B ≤
        sSup (Set.range (fun i => R i - u * C i)) + u * B :=
  PandoraBO.Private20261023.DualEnvelope.convex_and_attains R C B hbounded hstrict
