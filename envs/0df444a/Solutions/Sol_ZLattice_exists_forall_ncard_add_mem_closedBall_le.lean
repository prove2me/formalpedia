-- Prove2me | solution 1 for ZLattice.exists_forall_ncard_add_mem_closedBall_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/867d133c-4c39-5eb2-b1e9-e44e3d236ab4

import Mathlib.Algebra.Module.ZLattice.Summable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZLattice_exists_forall_ncard_add_mem_closedBall_le

set_option autoImplicit false

noncomputable section

open Module

namespace ZLattice
p2m_export "ZLattice" "normBound normBound_pos abs_repr_le rank"
p2m_open "ZLattice"

theorem solution_aux
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : AddSubgroup E) (hL : DiscreteTopology L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E) (R : ℝ), 0 ≤ R →
      {x : E | x ∈ L ∧ ‖a + x‖ ≤ R}.Finite ∧
      (({x : E | x ∈ L ∧ ‖a + x‖ ≤ R}.ncard : ℕ) : ℝ) ≤ C * (1 + R) ^ Module.finrank ℝ E := by
  classical

  set L' : Submodule ℤ E := AddSubgroup.toIntSubmodule L with hL'
  have hmem : ∀ x : E, x ∈ L' ↔ x ∈ L := fun x => Iff.rfl
  haveI hdisc : DiscreteTopology L' := hL

  set d : ℕ := finrank ℤ L' with hd
  let b : Basis (Fin d) ℤ L' := Module.finBasis ℤ L'
  set ε : ℝ := normBound b with hε_def
  have hε : 0 < ε := normBound_pos b

  have hdle : d ≤ finrank ℝ E := by
    have h1 : Set.finrank ℝ (L' : Set E) = Set.finrank ℤ (L' : Set E) :=
      Real.finrank_eq_int_finrank_of_discrete (by rw [Submodule.span_eq]; exact hdisc)
    have h2 : Set.finrank ℤ (L' : Set E) = d := by
      rw [hd, Set.finrank, Submodule.span_eq]
    rw [← h2, ← h1, Set.finrank]
    exact Submodule.finrank_le _
  refine ⟨(4 / ε + 1) ^ d, by positivity, fun a R hR => ?_⟩
  set S : Set E := {x : E | x ∈ L ∧ ‖a + x‖ ≤ R} with hS
  by_cases hSe : S = ∅
  · rw [hSe]
    exact ⟨Set.finite_empty, by simp; positivity⟩
  obtain ⟨v₀, hv₀L, hv₀⟩ := Set.nonempty_iff_ne_empty.mpr hSe
  have hv₀L' : v₀ ∈ L' := (hmem v₀).mpr hv₀L

  set N : ℕ := ⌊2 * R / ε⌋₊ with hN
  let box : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

  let φ : E → (Fin d → ℤ) := fun v =>
    if h : v ∈ L' then fun i => b.repr (⟨v, h⟩ - ⟨v₀, hv₀L'⟩) i else 0
  have hφ_mem : ∀ v ∈ S, φ v ∈ box := by
    intro v hv
    obtain ⟨hvL, hvR⟩ := hv
    have hvL' : v ∈ L' := (hmem v).mpr hvL
    simp only [φ, dif_pos hvL', box, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    set z : ℤ := b.repr (⟨v, hvL'⟩ - ⟨v₀, hv₀L'⟩) i with hz
    have hnorm : ‖(⟨v, hvL'⟩ - ⟨v₀, hv₀L'⟩ : L')‖ ≤ 2 * R := by
      change ‖((⟨v, hvL'⟩ - ⟨v₀, hv₀L'⟩ : L') : E)‖ ≤ 2 * R
      have : ((⟨v, hvL'⟩ - ⟨v₀, hv₀L'⟩ : L') : E) = (a + v) - (a + v₀) := by
        simp only [Submodule.coe_sub]; abel
      rw [this]
      calc ‖(a + v) - (a + v₀)‖ ≤ ‖a + v‖ + ‖a + v₀‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add hvR hv₀
        _ = 2 * R := by ring
    have h1 : |(z : ℝ)| ≤ ε⁻¹ * (2 * R) := by
      have h := abs_repr_le b (⟨v, hvL'⟩ - ⟨v₀, hv₀L'⟩) i
      rw [Int.cast_abs] at h
      exact h.trans (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 hε.le))
    have h2 : ε⁻¹ * (2 * R) = 2 * R / ε := by ring
    have h3 : (2 * R / ε) < N + 1 := by rw [hN]; exact Nat.lt_floor_add_one _
    have h4 : |(z : ℝ)| < (N : ℝ) + 1 := by linarith
    have h5 : |z| ≤ (N : ℤ) := by
      have h4' : ((|z| : ℤ) : ℝ) < ((N : ℤ) : ℝ) + 1 := by
        rw [Int.cast_abs, Int.cast_natCast]; exact h4
      have h4'' : |z| < (N : ℤ) + 1 := by exact_mod_cast h4'
      omega
    exact abs_le.mp h5
  have hφ_inj : Set.InjOn φ S := by
    intro v hv w hw h
    have hvL' : v ∈ L' := (hmem v).mpr hv.1
    have hwL' : w ∈ L' := (hmem w).mpr hw.1
    simp only [φ, dif_pos hvL', dif_pos hwL'] at h
    have h' : b.repr (⟨v, hvL'⟩ - ⟨v₀, hv₀L'⟩) = b.repr (⟨w, hwL'⟩ - ⟨v₀, hv₀L'⟩) :=
      Finsupp.ext (congrFun h)
    have h'' := sub_left_inj.mp (b.repr.injective h')
    exact congrArg Subtype.val h''
  have hfin : S.Finite :=
    Set.Finite.of_finite_image ((box : Set (Fin d → ℤ)).toFinite.subset
      (by rintro p ⟨v, hv, rfl⟩; exact hφ_mem v hv)) hφ_inj
  refine ⟨hfin, ?_⟩

  have hcard : S.ncard ≤ box.card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard_of_injOn φ (fun v hv => by exact_mod_cast hφ_mem v hv) hφ_inj
  have hbox : (box.card : ℝ) = (2 * N + 1 : ℝ) ^ d := by
    simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
    rw [this]
    push_cast
    ring
  have hN_le : (N : ℝ) ≤ 2 * R / ε := by rw [hN]; exact Nat.floor_le (by positivity)
  have hε4 : 0 ≤ 4 / ε := by positivity
  calc ((S.ncard : ℕ) : ℝ) ≤ box.card := by exact_mod_cast hcard
    _ = (2 * N + 1 : ℝ) ^ d := hbox
    _ ≤ (4 * R / ε + 1) ^ d := by
        apply pow_le_pow_left₀ (by positivity)
        have : (2 : ℝ) * N ≤ 4 * R / ε := by
          rw [show (4 : ℝ) * R / ε = 2 * (2 * R / ε) by ring]
          linarith
        linarith
    _ ≤ ((4 / ε + 1) * (1 + R)) ^ d := by
        apply pow_le_pow_left₀ (by positivity)
        have : (4 / ε + 1) * (1 + R) = 4 * R / ε + 1 + (4 / ε + R) := by ring
        rw [this]
        linarith
    _ = (4 / ε + 1) ^ d * (1 + R) ^ d := mul_pow _ _ _
    _ ≤ (4 / ε + 1) ^ d * (1 + R) ^ finrank ℝ E := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ (by linarith) hdle

end ZLattice

theorem solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : AddSubgroup E) (hL : DiscreteTopology L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E) (R : ℝ), 0 ≤ R →
      {x : E | x ∈ L ∧ ‖a + x‖ ≤ R}.Finite ∧
      (({x : E | x ∈ L ∧ ‖a + x‖ ≤ R}.ncard : ℕ) : ℝ) ≤ C * (1 + R) ^ Module.finrank ℝ E :=
  ZLattice.solution_aux L hL

end
end S_ZLattice_exists_forall_ncard_add_mem_closedBall_le
end P2MW
export P2MW.S_ZLattice_exists_forall_ncard_add_mem_closedBall_le (solution)
