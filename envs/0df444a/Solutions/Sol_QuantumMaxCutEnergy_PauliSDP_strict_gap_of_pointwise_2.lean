-- Prove2me | solution 2 for QuantumMaxCutEnergy.PauliSDP.strict_gap_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T03:54:51.472303+00:00
-- url     : https://prove2.me/submissions/3e0ab04c-abd0-49e3-8945-51a27998ed0c

/-
Assembly layer for `QuantumMaxCutEnergy.PauliSDP.strict_gap_0595`.

The target statement separates into

* an *upper* half  `optimum G ≤ value 2 G`   (physical-state embedding, proved on the platform as
  `QuantumMaxCutEnergy.PauliSDP.physical_state_upper_bound`), and
* a *lower* half   `γ * value 2 G ≤ optimum G`,

where `value k G` is a supremum over the feasible moment assignments and `optimum G` is a
supremum over normalized wave functions.  This file proves, sorry-free, the two pieces of
bookkeeping that any proof of the lower half has to pass through:

* `value_le_of_pointwise` : a pointwise (per-moment-assignment) comparison implies the same
  comparison for the supremum `value`;
* `objective_le_of_per_edge` : a per-edge comparison against one wave function's per-edge gains
  implies the objective-level comparison (the arithmetic bridge);
* `strict_gap_of_pointwise` : the final reduction of `strict_gap_0595` to a pointwise input.

Nothing here assumes the (open) rounding analysis; the remaining mathematical content is exactly
a state-existence statement for each feasible level-2 moment assignment.
-/
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy.PauliSDP

/-! ### The identity moment assignment is feasible at every level -/

lemma localProduct_eq_zero_iff (a b : Label) : localProduct a b = 0 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> simp [localProduct]

lemma localPhase_self (a : Label) : localPhase a a = 1 := by
  fin_cases a <;> rfl

lemma wordProduct_eq_identity_iff {n : ℕ} (P Q : Word n) :
    wordProduct P Q = identityWord n ↔ P = Q := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [wordProduct, identityWord] at hi
    exact (localProduct_eq_zero_iff (P i) (Q i)).1 hi
  · rintro rfl
    funext i
    simp only [wordProduct, identityWord]
    exact (localProduct_eq_zero_iff (P i) (P i)).2 rfl

lemma wordPhase_self_apply {n : ℕ} (P : Word n) : wordPhase P P = 1 := by
  unfold wordPhase
  exact Finset.prod_eq_one (fun i _ => localPhase_self (P i))

/-- The moment assignment that is `1` on the identity word and `0` elsewhere is feasible:
its Gram matrix is the identity matrix. -/
theorem feasible_identityMoments (n k : ℕ) :
    Feasible k (fun P => if P = identityWord n then (1 : ℝ) else 0) := by
  constructor
  · simp
  · have hgram : realGram k (fun P => if P = identityWord n then (1 : ℝ) else 0)
        = (1 : Matrix (Index n k) (Index n k) ℝ) := by
      funext P Q
      by_cases hPQ : P = Q
      · subst hPQ
        simp [realGram, wordPhase_self_apply, wordProduct_eq_identity_iff]
      · have hprod : wordProduct P.val Q.val ≠ identityWord n := by
          intro h
          exact hPQ (Subtype.ext ((wordProduct_eq_identity_iff P.val Q.val).1 h))
        simp [realGram, hPQ, hprod]
    rw [hgram]
    exact Matrix.PosSemidef.one

/-! ### Per-edge to objective level -/

/-- If every edge term of the objective, scaled by `γ`, is dominated by the edge term of a
single assignment of edge gains `g`, then the same holds for the whole objective. -/
theorem objective_le_of_per_edge {n : ℕ} (w : QuantumMaxCutEnergy.Weights n)
    (L : Word n → ℝ) (γ : ℝ) (g : QuantumMaxCutEnergy.Edge n → ℝ)
    (h : ∀ e : QuantumMaxCutEnergy.Edge n,
      γ * ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2) ≤ g e) :
    γ * objective w L ≤ ∑ e, (w e : ℝ) * g e := by
  unfold objective
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  have hw : (0 : ℝ) ≤ (w e : ℝ) := by exact_mod_cast (w e).2
  have h1 := h e
  calc γ * ((w e : ℝ) * (1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2)
      = (w e : ℝ) * (γ *
          ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2)) := by ring
    _ ≤ (w e : ℝ) * g e := mul_le_mul_of_nonneg_left h1 hw

/-! ### Pointwise comparison to the supremum `value` -/

/-- If every feasible moment assignment satisfies `γ * objective ≤ optimum`, then the relaxation
value does too.  This is the `sSup` bookkeeping: `value` is a supremum over feasible moment
assignments, so it suffices to bound every element of the defining set. -/
theorem value_le_of_pointwise (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (h : ∀ (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) (L : Word n → ℝ),
      Feasible k L → γ * objective w L ≤ QuantumMaxCutEnergy.optimum ⟨n, w⟩) :
    ∀ G : QuantumMaxCutEnergy.Input, γ * value k G ≤ QuantumMaxCutEnergy.optimum G := by
  intro G
  have hne : ({v : ℝ | ∃ L : Word G.n → ℝ, Feasible k L ∧ v = objective G.weights L}).Nonempty :=
    ⟨objective G.weights (fun P => if P = identityWord G.n then (1 : ℝ) else 0),
      (fun P => if P = identityWord G.n then (1 : ℝ) else 0),
      feasible_identityMoments G.n k, rfl⟩
  have hub : ∀ v ∈ {v : ℝ | ∃ L : Word G.n → ℝ, Feasible k L ∧
      v = objective G.weights L}, v ≤ QuantumMaxCutEnergy.optimum G / γ := by
    rintro v ⟨L, hL, rfl⟩
    rw [le_div_iff₀ hγ]
    simpa [mul_comm] using h G.n G.weights L hL
  have hsup : value k G ≤ QuantumMaxCutEnergy.optimum G / γ := by
    show sSup {v : ℝ | ∃ L : Word G.n → ℝ, Feasible k L ∧ v = objective G.weights L} ≤ _
    exact csSup_le hne hub
  calc γ * value k G ≤ γ * (QuantumMaxCutEnergy.optimum G / γ) :=
        mul_le_mul_of_nonneg_left hsup (le_of_lt hγ)
    _ = γ * QuantumMaxCutEnergy.optimum G / γ := by rw [mul_div_assoc]
    _ = QuantumMaxCutEnergy.optimum G := by field_simp

/-! ### The final reduction of the target statement -/

/-- `strict_gap_0595` reduces to (i) a pointwise shielding estimate for feasible level-2 moment
assignments and (ii) the physical-state upper bound. -/
theorem strict_gap_of_pointwise (γ : ℚ≥0) (h0 : (0.595 : ℝ) < (γ : ℝ))
    (h1 : (γ : ℝ) ≤ 1)
    (hlow : ∀ (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) (L : Word n → ℝ),
      Feasible 2 L → (γ : ℝ) * objective w L ≤ QuantumMaxCutEnergy.optimum ⟨n, w⟩)
    (hhigh : ∀ G : QuantumMaxCutEnergy.Input,
      QuantumMaxCutEnergy.optimum G ≤ value 2 G) :
    ∃ γ : ℚ≥0, (0.595 : ℝ) < (γ : ℝ) ∧ (γ : ℝ) ≤ 1 ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (γ : ℝ) * value 2 G ≤ QuantumMaxCutEnergy.optimum G ∧
        QuantumMaxCutEnergy.optimum G ≤ value 2 G := by
  have hγ : (0 : ℝ) < (γ : ℝ) := by linarith
  exact ⟨γ, h0, h1, fun G => ⟨value_le_of_pointwise 2 (γ : ℝ) hγ hlow G, hhigh G⟩⟩

end QuantumMaxCutEnergy.PauliSDP

/-- The 0.595 reduction, packaged as the platform solution. -/
theorem solution (γ : ℚ≥0) (h0 : (0.595 : ℝ) < (γ : ℝ)) (h1 : (γ : ℝ) ≤ 1)
    (hlow : ∀ (n : ℕ) (w : QuantumMaxCutEnergy.Weights n)
      (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ),
      QuantumMaxCutEnergy.PauliSDP.Feasible 2 L →
        (γ : ℝ) * QuantumMaxCutEnergy.PauliSDP.objective w L ≤ QuantumMaxCutEnergy.optimum ⟨n, w⟩)
    (hhigh : ∀ G : QuantumMaxCutEnergy.Input,
      QuantumMaxCutEnergy.optimum G ≤ QuantumMaxCutEnergy.PauliSDP.value 2 G) :
    ∃ γ : ℚ≥0, (0.595 : ℝ) < (γ : ℝ) ∧ (γ : ℝ) ≤ 1 ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (γ : ℝ) * QuantumMaxCutEnergy.PauliSDP.value 2 G ≤ QuantumMaxCutEnergy.optimum G ∧
        QuantumMaxCutEnergy.optimum G ≤ QuantumMaxCutEnergy.PauliSDP.value 2 G :=
  QuantumMaxCutEnergy.PauliSDP.strict_gap_of_pointwise γ h0 h1 hlow hhigh

#print axioms solution
