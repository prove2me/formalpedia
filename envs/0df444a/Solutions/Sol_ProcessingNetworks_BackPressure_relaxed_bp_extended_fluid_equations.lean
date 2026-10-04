-- Prove2me | solution 1 for ProcessingNetworks.BackPressure.relaxed_bp_extended_fluid_equations
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:30:31.005454+00:00
-- url     : https://prove2.me/submissions/9b0fef5d-8be6-458f-b448-a37f074d77a5

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

open MeasureTheory Filter

namespace ProcessingNetworks.BackPressure.RelaxedCE

open ProcessingNetworks.BackPressure

def dat : SPNPlanningData 0 0 0 :=
  { B := 0, Γ := 0, m := fun j => j.elim0, hm := fun j => j.elim0, A := 0,
    b := fun k => k.elim0, hb := fun k => k.elim0 }

theorem h91 : SatisfiesAssumption91 dat := fun j => j.elim0

theorem hE : (({0} : Finset (Fin 0 → ℝ)) : Set (Fin 0 → ℝ)) = ExtremeAllocations dat := by
  ext x
  simp only [Finset.coe_singleton, Set.mem_singleton_iff, ExtremeAllocations, mem_extremePoints]
  constructor
  · rintro rfl
    exact ⟨⟨fun j => j.elim0, fun k => k.elim0⟩, fun x1 _ x2 _ _ =>
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  · intro _; exact Subsingleton.elim _ _

end ProcessingNetworks.BackPressure.RelaxedCE

open ProcessingNetworks.BackPressure in
theorem solution : ¬ (∀ {Xstate : Type} [Countable Xstate] {Ω : Type} [MeasureSpace Ω] {I J K : ℕ}
    (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = ExtremeAllocations dat)
    (Zraw Traw : Xstate → ℝ → Ω → Fin I → ℝ) (Yraw : (Fin J → ℝ) → Xstate → ℝ → Ω → ℝ)
    (Traw' : Xstate → ℝ → Ω → Fin J → ℝ)
    (size : Xstate → ℝ) (size_nonneg : ∀ x, 0 ≤ size x)
    (hTY : ∀ x ω t j, Traw' x t ω j = ∑ β ∈ E, β j * Yraw β x t ω)
    (hYmono : ∀ β ∈ E, ∀ x ω, Monotone (Yraw β x · ω))
    (hYsum : ∀ x ω t, 0 ≤ t → ∑ β ∈ E, Yraw β x t ω = t)
    (hYopt : ∀ β ∈ E, ∀ (x : Xstate) (ω : Ω) (u1 u2 : ℝ), 0 ≤ u1 → u1 ≤ u2 →
      (∀ u ∈ Set.Icc u1 u2, p dat β (Zraw x u ω) < ⨆ α ∈ E, p dat α (Zraw x u ω)) →
      Yraw β x u2 ω = Yraw β x u1 ω)
    (ω : Ω) (x : ℕ → Xstate) (hsize : Tendsto (fun n => size (x n)) atTop atTop)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) (Yh : (Fin J → ℝ) → ℝ → ℝ)
    (hZconv :
      UOCConverges (fun n t i => (size (x n))⁻¹ * Zraw (x n) (size (x n) * t) ω i) Zh)
    (hTconv :
      UOCConverges (fun n t j => (size (x n))⁻¹ * Traw' (x n) (size (x n) * t) ω j) Th)
    (hYconv : ∀ β ∈ E,
      UOCConvergesR (fun n t => (size (x n))⁻¹ * Yraw β (x n) (size (x n) * t) ω) (Yh β)),
    (∀ t : ℝ, 0 ≤ t → ∀ j, Th t j = ∑ β ∈ E, β j * Yh β t) ∧
    (∀ β ∈ E, Monotone (Yh β)) ∧
    (∀ t : ℝ, 0 ≤ t → ∑ β ∈ E, Yh β t = t) ∧
    (∀ β ∈ E, ∀ t : ℝ, 0 < t → p dat β (Zh t) < ⨆ α ∈ E, p dat α (Zh t) →
      ∀ d : ℝ, HasDerivAt (Yh β) d t → d = 0)) := by
  intro h
  have key := h (Xstate := ℕ) (Ω := ℝ) RelaxedCE.dat RelaxedCE.h91 {0} RelaxedCE.hE
    (fun _ _ _ i => i.elim0) (fun _ _ _ i => i.elim0) (fun _ _ u _ => u) (fun _ _ _ j => j.elim0)
    (fun n => (n : ℝ)) (fun n => Nat.cast_nonneg n) (fun _ _ _ j => j.elim0)
    (fun _ _ _ _ _ _ hab => hab) (fun _ _ t _ => by simp)
    (fun β _ x ω u1 u2 _ _ hlt => by
      exfalso
      have h1 := hlt u1 ⟨le_rfl, by assumption⟩
      have hp : ∀ α : Fin 0 → ℝ, p RelaxedCE.dat α ((fun _ _ _ i => i.elim0) x u1 ω) = 0 :=
        fun α => by simp [p]
      have hle : (⨆ α ∈ ({0} : Finset (Fin 0 → ℝ)),
          p RelaxedCE.dat α ((fun _ _ _ i => i.elim0) x u1 ω)) ≤ 0 :=
        Real.iSup_le (fun α => Real.iSup_le (fun _ => (hp α).le) le_rfl) le_rfl
      rw [hp] at h1
      linarith)
    0 (fun n => n) tendsto_natCast_atTop_atTop
    (fun _ i => i.elim0) (fun _ j => j.elim0) (fun _ j => j.elim0) (fun _ i => i.elim0)
    (fun _ t => |t|)
    (fun _ _ _ _ => ⟨0, fun _ _ _ _ (i : Fin 0) => i.elim0⟩)
    (fun _ _ _ _ => ⟨0, fun _ _ _ _ (j : Fin 0) => j.elim0⟩)
    (fun β _ Tb _ ε hε => ⟨1, fun n hn t ht => by
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      beta_reduce
      rw [← mul_assoc, inv_mul_cancel₀ hn', one_mul, abs_of_nonneg ht.1, sub_self, abs_zero]
      exact hε⟩)
  have := key.2.1 0 (Finset.mem_singleton_self _) (show (-1 : ℝ) ≤ 0 by norm_num)
  norm_num at this


