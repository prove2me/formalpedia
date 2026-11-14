-- Prove2me | solution 1 for StabilityDichotomies.Solvability.horn_thinning_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:35:55.553208+00:00
-- url     : https://prove2.me/submissions/06ad32bc-dd0c-414a-a3e2-871ce0e369ff

import Theorems.Thm_StabilityDichotomies_Solvability_shared_mask_aggregate_transport_bound
import Theorems.Thm_StabilityDichotomies_Solvability_deleted_output_law_at_original_index
import Theorems.Thm_StabilityDichotomies_Solvability_horn_thinning_nonisolated_height_bound
import Theorems.Thm_StabilityDichotomies_Solvability_thinned_extremal_mono
import Theorems.Thm_StabilityDichotomies_Solvability_nonisolated_variables_bound
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

private theorem sum_over_occurrences {Γ : Language} {V : Type} (I : Instance Γ V)
    (f : Constraint Γ V → ℝ) :
    (I.constraints.map f).sum = ∑ i : Fin I.constraints.card, f (occurrenceAt I i) := by
  have hl : List.ofFn (occurrenceAt I) = I.constraints.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [occurrenceAt]
  calc
    _ = (I.constraints.toList.map f).sum := by simp
    _ = ((List.ofFn (occurrenceAt I)).map f).sum := by rw [hl]
    _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl

theorem solution (Γ : Language)
    (hHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (A : Solver Γ)
    (hLaw : ThinningOutputLaw Γ false ε A)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I) :
    averageSensitivity A I ≤ (maxArity Γ : ℝ) * ε⁻¹ := by
  let out : (Fin I.constraints.card → Bool) → V → Bool := fun mask =>
    extremalSolution (thinnedInstance I mask) false
  let U := I.constraints.toFinset.biUnion fun c => Finset.univ.image c.scope
  have hmono : Monotone out := by
    intro a b hab
    have hmask : ∀ i, a i = true → b i = true := by
      intro i hi
      have h := hab i
      rw [hi] at h
      cases hb : b i <;> simp_all
      exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
    have h := thinned_extremal_mono Γ false (by simpa using hHorn) V I hSat a b hmask
    simpa [out] using h
  have hbound (mask : Fin I.constraints.card → Bool) :
      (∑ v : V, if out mask v then (1 : ℝ) else 0) ≤ (U.card : ℝ) := by
    exact horn_thinning_nonisolated_height_bound Γ hHorn V I hSat mask
  let ν : Fin I.constraints.card → PMF (V → Bool) := fun i => A V (I.delete (occurrenceAt I i))
  have hν (i : Fin I.constraints.card) (x : V → Bool) :
      (ν i x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
        (if out (Function.update mask i false) = x then 1 else 0) := by
    exact deleted_output_law_at_original_index Γ false ε A hLaw V I hSat i x
  have hμ (x : V → Bool) : (A V I x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
        (if out mask = x then 1 else 0) := hLaw V I hSat x
  have hsum := shared_mask_aggregate_transport_bound I.constraints.card out hmono (U.card : ℝ)
    ε hbound hε hε1 (A V I) ν hμ hν
  unfold averageSensitivity
  by_cases hI : I.constraints = 0
  · simp [hI]
    positivity
  · rw [if_neg hI, sum_over_occurrences]
    have hcard : 0 < (I.constraints.card : ℝ) := by
      exact_mod_cast Multiset.card_pos.mpr hI
    apply (div_le_iff₀ hcard).2
    calc
      _ ≤ (U.card : ℝ) * ε⁻¹ := hsum
      _ ≤ ((maxArity Γ : ℝ) * I.constraints.card) * ε⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (le_of_lt hε))
        exact_mod_cast nonisolated_variables_bound I
      _ = _ := by ring
