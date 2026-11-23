-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:35.029914+00:00
-- url     : https://prove2.me/submissions/5576af43-bcd9-4340-8633-068f0e747489

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Polynomial
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {ι : Type*} [Fintype ι] {n : ℕ} (V : Set (ι → Matrix (Fin n) (Fin n) ℂ))
    (hV : ∀ a ∈ V, ∀ b ∈ V, ∀ z : ℂ, (1 - z) • a + z • b ∈ V) :
    IsPreconnected {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} := by
  refine isPreconnected_of_forall_pair ?_
  rintro a ⟨haV, ha⟩ b ⟨hbV, hb⟩
  let L : ℂ → ι → Matrix (Fin n) (Fin n) ℂ := fun z => (1 - z) • a + z • b
  let p : ι → ℂ[X] := fun i =>
    (Matrix.of fun k l => C (a i k l) + X * C (b i k l - a i k l)).det
  have hev : ∀ i z, (p i).eval z = (L z i).det := by
    intro i z
    simp only [p, L]
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext k l
    simp [Matrix.of_apply]
    ring
  have hp : ∀ i, p i ≠ 0 := by
    intro i h0
    have := hev i 0
    rw [h0, eval_zero] at this
    exact ha i (by simpa [L] using this.symm)
  let Z : Set ℂ := ⋃ i, {z | (p i).IsRoot z}
  have hZ : Z.Countable := (Set.finite_iUnion fun i => Polynomial.finite_setOfPred_isRoot (hp i)).countable
  have hc : IsPreconnected Zᶜ :=
    (hZ.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
  have hLc : Continuous L := by
    simp only [L]
    fun_prop
  have hmem : ∀ z ∈ Zᶜ, L z ∈ {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} := by
    intro z hz
    refine ⟨hV a haV b hbV z, fun i h0 => hz ?_⟩
    exact Set.mem_iUnion.2 ⟨i, by show (p i).eval z = 0; rw [hev]; exact h0⟩
  have hnot : ∀ z, (∀ i, (L z i).det ≠ 0) → z ∈ Zᶜ := by
    intro z hz hZz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hZz
    exact hz i (by rw [← hev]; exact hi)
  have hL0 : L 0 = a := by simp [L]
  have hL1 : L 1 = b := by simp [L]
  refine ⟨L '' Zᶜ, ?_, ⟨0, hnot 0 (by rw [hL0]; exact ha), hL0⟩,
    ⟨1, hnot 1 (by rw [hL1]; exact hb), hL1⟩, hc.image L hLc.continuousOn⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hmem z hz
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
