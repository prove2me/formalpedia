-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P88.orbit_basis
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:17:07.598827+00:00
-- url     : https://prove2.me/submissions/a1eae3e2-b5b6-4a6d-8f9d-c123d4bf36b7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- zeta map -/
def AuxOB_Z (m : ℕ) : DiagramSpace m →ₗ[ℂ] DiagramSpace m :=
  Finsupp.linearCombination ℂ (fun d : LevelDiagram m =>
    ∑ e ∈ Finset.univ.filter (fun e : LevelDiagram m => d.val ≤ e.val), Finsupp.single e (1 : ℂ))

theorem AuxOB_Z_single (m : ℕ) (d : LevelDiagram m) :
    AuxOB_Z m (Finsupp.single d 1) =
      ∑ e ∈ Finset.univ.filter (fun e : LevelDiagram m => d.val ≤ e.val), Finsupp.single e (1 : ℂ) := by
  simp [AuxOB_Z]

theorem AuxOB_Z_apply (m : ℕ) (x : DiagramSpace m) (c : LevelDiagram m) :
    AuxOB_Z m x c = ∑ d ∈ x.support, x d * (if d.val ≤ c.val then 1 else 0) := by
  simp only [AuxOB_Z, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rw [Finset.sum_ite_eq']
  simp

theorem AuxOB_inj (m : ℕ) : Function.Injective (AuxOB_Z m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  have hs : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  obtain ⟨d, hd, hmin⟩ := Finset.exists_minimalFor (fun d : LevelDiagram m => d.val) x.support hs
  have h := AuxOB_Z_apply m x d
  rw [hx, Finsupp.zero_apply, Finset.sum_eq_single d] at h
  · simp at h; exact (Finsupp.mem_support_iff.mp hd) h.symm
  · intro d' hd' hne'
    by_cases hle : d'.val ≤ d.val
    · exact absurd (Subtype.ext (le_antisymm hle (hmin hd' hle))) hne'
    · simp [hle]
  · intro h'; exact absurd hd h'

theorem _root_.solution (m : ℕ) :
    ∃! b : Module.Basis (LevelDiagram m) ℂ (DiagramSpace m),
      ∀ d : LevelDiagram m,
        Finsupp.single d 1 = ∑ e ∈ Finset.univ.filter (fun e : LevelDiagram m => d.val ≤ e.val), b e := by
  let Ze := LinearEquiv.ofInjectiveEndo (AuxOB_Z m) (AuxOB_inj m)
  refine ⟨(Finsupp.basisSingleOne).map Ze.symm, fun d => ?_, fun b' hb' => ?_⟩
  · simp only [Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
    rw [← map_sum, ← AuxOB_Z_single]
    exact (Ze.symm_apply_apply _).symm
  · apply Module.Basis.eq_of_apply_eq
    set b := (Finsupp.basisSingleOne).map Ze.symm with hbdef
    have hb : ∀ d : LevelDiagram m, Finsupp.single d 1 =
        ∑ e ∈ Finset.univ.filter (fun e : LevelDiagram m => d.val ≤ e.val), b e := by
      intro d
      simp only [hbdef, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
      rw [← map_sum, ← AuxOB_Z_single]
      exact (Ze.symm_apply_apply _).symm
    by_contra hne
    push Not at hne
    have hS : (Finset.univ.filter (fun e => b' e - b e ≠ 0)).Nonempty := by
      obtain ⟨e, he⟩ := hne
      exact ⟨e, by simp [sub_ne_zero, he]⟩
    obtain ⟨e, he, hmax⟩ := Finset.exists_maximalFor (fun d : LevelDiagram m => d.val) _ hS
    have h0 : ∑ e' ∈ Finset.univ.filter (fun e' : LevelDiagram m => e.val ≤ e'.val), (b' e' - b e') = 0 := by
      rw [Finset.sum_sub_distrib, ← hb' e, ← hb e, sub_self]
    rw [Finset.sum_eq_single e] at h0
    · exact (Finset.mem_filter.mp he).2 h0
    · intro e' he' hne'
      have hle := (Finset.mem_filter.mp he').2
      by_contra hz
      have hmem : e' ∈ Finset.univ.filter (fun e => b' e - b e ≠ 0) := by simp [hz]
      exact hne' (Subtype.ext (le_antisymm (hmax hmem hle) hle))
    · intro h'; exact absurd (by simp) h'

end QAlgorithms.Papers.Independent.Intake100.P88

end
