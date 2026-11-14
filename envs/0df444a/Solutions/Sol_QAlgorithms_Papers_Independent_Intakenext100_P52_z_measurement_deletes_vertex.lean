-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.z_measurement_deletes_vertex
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:54:19.352556+00:00
-- url     : https://prove2.me/submissions/069d8889-c066-4cea-8946-bd2c70510a41

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_graphClusterState_isState
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 QAlgorithms.Papers.Independent.Information100.P21
open scoped Matrix ComplexConjugate
set_option autoImplicit false
private theorem edgePhase_delete {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (A : V) (s : Bool) (z : {v : V // v ≠ A} → Bool) :
    edgePhase E (insertSite A s z) = neighbourPhase E A s z * edgePhase (deletedEdges E A) z := by
  let S := E.filter (fun e => e.1 ≠ A ∧ e.2 ≠ A)
  have hrest : (∏ e ∈ S, czPhase (insertSite A s z e.1) (insertSite A s z e.2)) =
      ∏ e ∈ deletedEdges E A, czPhase (z e.1) (z e.2) := by
    apply Finset.prod_bij (fun e he =>
      (⟨e.1,(Finset.mem_filter.mp he).2.1⟩,⟨e.2,(Finset.mem_filter.mp he).2.2⟩))
    · intro e he
      simpa only [deletedEdges, Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.mem_filter.mp he).1
    · intro e he f hf h
      exact Prod.ext (congrArg (fun p => p.1.val) h) (congrArg (fun p => p.2.val) h)
    · intro e he
      have heE : (e.1.val,e.2.val) ∈ E := by simpa [deletedEdges] using he
      refine ⟨(e.1.val,e.2.val), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨heE,e.1.prop,e.2.prop⟩
      · exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    · intro e he
      simp [insertSite, (Finset.mem_filter.mp he).2.1, (Finset.mem_filter.mp he).2.2]
  unfold edgePhase neighbourPhase
  rw [← hrest]
  dsimp only [S]
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  by_cases h : e.1 = A ∨ e.2 = A
  · rcases h with h | h <;> simp [h]
  · have hn := not_or.mp h
    simp [h,hn.1,hn.2]

set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Z deletion, PDF pp.11–12: includes the missing intermediate 1/sqrt(2)
factor and explicitly removes the measured register. Singleton and isolated
vertices are allowed; their neighbour product is empty. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (hloop : ∀ e ∈ E, e.1 ≠ e.2)
    (horient : ∀ e ∈ E, (e.2,e.1) ∉ E) (A : V) (s : Bool) :
    let b : Vec ({v : V // v ≠ A} → Bool) :=
      WithLp.toLp 2 fun z => graphClusterState E (insertSite A s z)
    b = ((Real.sqrt 2)⁻¹ : ℂ) •
      (WithLp.toLp 2 fun z => neighbourPhase E A s z * graphClusterState (deletedEdges E A) z) ∧
    ‖b‖ ^ 2 = (1 / 2 : ℝ) := by
  dsimp only
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨A⟩
  have hcm : Fintype.card {v : V // v ≠ A} = Fintype.card V - 1 := by
    simpa using Fintype.card_subtype_compl (fun v : V => v = A)
  have hc : Fintype.card V = Fintype.card {v : V // v ≠ A} + 1 := by omega
  have hb : (WithLp.toLp 2 fun z => graphClusterState E (insertSite A s z)) =
      ((Real.sqrt 2)⁻¹ : ℂ) • (WithLp.toLp 2 fun z =>
        neighbourPhase E A s z * graphClusterState (deletedEdges E A) z) := by
    ext z
    simp only [graphClusterState, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
    rw [edgePhase_delete, hc, pow_succ]
    ring
  have hphase (z : {v : V // v ≠ A} → Bool) : ‖neighbourPhase E A s z‖ = 1 := by
    simp only [neighbourPhase, norm_prod]
    apply Finset.prod_eq_one
    intro e he
    split_ifs
    · cases insertSite A s z e.1 <;> cases insertSite A s z e.2 <;> simp [czPhase]
    · norm_num
  have hn : ‖(WithLp.toLp 2 fun z => neighbourPhase E A s z *
        graphClusterState (deletedEdges E A) z)‖ ^ 2 = (1 : ℝ) := by
    simp only [EuclideanSpace.norm_sq_eq, PiLp.toLp_apply, norm_mul, hphase, one_mul]
    rw [← EuclideanSpace.norm_sq_eq, show ‖graphClusterState (deletedEdges E A)‖ = 1 from
      graphClusterState_isState (deletedEdges E A)]
    norm_num
  refine ⟨hb, ?_⟩
  rw [hb, norm_smul, mul_pow, hn, mul_one]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num
