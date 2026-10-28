-- Prove2me | solution 1 for Submodule.exists_ne_zero_dotProduct_const_on
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:23.058511+00:00
-- url     : https://prove2.me/submissions/05821136-9160-49b0-affa-013a0b45ed90

import Mathlib

-- carved verbatim out of submission 3c55ced4-4944-4de2-ba43-8110d2682db1, lines 2489-2526

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def aux1_dotL {n : Type*} [Fintype n] (u : n → ℝ) : Module.Dual ℝ (n → ℝ) where
  toFun v := u ⬝ᵥ v
  map_add' v w := dotProduct_add u v w
  map_smul' t v := by simp [dotProduct_smul]

end

section
open Matrix

theorem aux_sum_smul_dot {n : ℕ} {ι : Type*} [Fintype ι] (y : ι → ℝ) (a : ι → Fin n → ℝ)
    (x : Fin n → ℝ) : (∑ j, y j • a j) ⬝ᵥ x = ∑ j, y j * (a j ⬝ᵥ x) := by
  simp [sum_dotProduct, smul_dotProduct]

def poly {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ j, a j ⬝ᵥ x ≤ b j}

theorem solution {N : ℕ} (V : Submodule ℝ (Fin N → ℝ))
    (S : Set (Fin N → ℝ))
    (h : Module.finrank ℝ (vectorSpan ℝ S) + 1 ≤ Module.finrank ℝ V) :
    ∃ v ∈ V, v ≠ 0 ∧ ∀ s ∈ S, ∀ s' ∈ S, s ⬝ᵥ v = s' ⬝ᵥ v := by
  classical
  let bW := Module.finBasis ℝ (vectorSpan ℝ S)
  let L : V →ₗ[ℝ] (Fin (Module.finrank ℝ (vectorSpan ℝ S)) → ℝ) :=
    LinearMap.pi (fun i => (aux1_dotL ((bW i : vectorSpan ℝ S) : Fin N → ℝ)).comp V.subtype)
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  have hr : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ (vectorSpan ℝ S) :=
    (Submodule.finrank_le _).trans (Module.finrank_fin_fun ℝ).le
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker L) := by omega
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := ↥(LinearMap.ker L))).1 hpos
  have hLx : L x = 0 := LinearMap.mem_ker.1 x.2
  have hi : ∀ i, ((bW i : vectorSpan ℝ S) : Fin N → ℝ) ⬝ᵥ ((x : V) : Fin N → ℝ) = 0 :=
    fun i => congrFun hLx i
  refine ⟨((x : V) : Fin N → ℝ), (x : V).2, fun h0 => hx ?_, fun s hs s' hs' => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    simpa using h0
  · have hmem : s - s' ∈ vectorSpan ℝ S := by
      rw [← vsub_eq_sub]
      exact vsub_mem_vectorSpan ℝ hs hs'
    have hrep := bW.sum_repr ⟨s - s', hmem⟩
    have e : s - s' =
        ∑ i, bW.repr ⟨s - s', hmem⟩ i • ((bW i : vectorSpan ℝ S) : Fin N → ℝ) := by
      have := congrArg Subtype.val hrep
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    have : (s - s') ⬝ᵥ ((x : V) : Fin N → ℝ) = 0 := by
      rw [e, aux_sum_smul_dot]
      simp [hi]
    rw [sub_dotProduct, sub_eq_zero] at this
    exact this

end
