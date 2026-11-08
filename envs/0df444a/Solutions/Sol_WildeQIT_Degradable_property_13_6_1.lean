-- Prove2me | solution 1 for WildeQIT.Degradable.property_13_6_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:50:14.341178+00:00
-- url     : https://prove2.me/submissions/1b37df04-5c70-4369-8e28-8c261761b0cc

import Mathlib
import Definitions.Def_WildeQIT_Degradable_privateInfoChannel

namespace Aux_WildeQIT_13_6_1
open Matrix

lemma f_cont : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => x * Real.log x / Real.log 2 := by
    funext x; rw [Real.logb]; ring
  rw [this]
  exact Real.continuous_mul_log.div_const _

noncomputable def reindexStar {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom with
    map_star' := fun M => by
      change reindex e e (star M) = star (reindex e e M)
      rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_reindex] }

lemma reindexStar_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (M : Matrix ι ι ℂ) : reindexStar e M = reindex e e M := rfl

lemma trace_reindex' {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (M : Matrix ι ι ℂ) :
    (reindex e e M).trace = M.trace := by
  simp only [trace, reindex_apply, submatrix_apply, diag_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

lemma vn_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ) :
    QAlgorithms.vnEntropy (reindex e e M) = QAlgorithms.vnEntropy M := by
  unfold QAlgorithms.vnEntropy
  by_cases hM : IsSelfAdjoint M
  · have hM' : IsSelfAdjoint (reindexStar e M) := by
      rw [IsSelfAdjoint, ← map_star, hM.star_eq]
    have hcont : Continuous (reindexStar e) := by
      show Continuous (fun M : Matrix ι ι ℂ => M.submatrix e.symm e.symm)
      exact continuous_id.matrix_submatrix _ _
    have h := StarAlgHom.map_cfc (R := ℝ) (reindexStar e) (fun x : ℝ => x * Real.logb 2 x) M
      f_cont.continuousOn hcont hM hM'
    rw [reindexStar_apply, reindexStar_apply] at h
    rw [← h, trace_reindex']
  · have hM' : ¬ IsSelfAdjoint (reindex e e M) := by
      intro h
      apply hM
      have h2 : star (reindex e e M) = reindex e e M := h
      rw [star_eq_conjTranspose, conjTranspose_reindex] at h2
      have := (reindex e e).injective h2
      exact this
    rw [cfc_apply_of_not_predicate M hM, cfc_apply_of_not_predicate _ hM']
    simp

lemma cq_one {B : Type} [Fintype B] [DecidableEq B] (σ : Matrix B B ℂ) :
    WildeQIT.Degradable.cqState (fun _ : Fin 1 => (1 : ℝ)) (fun _ => σ)
      = reindex (Equiv.uniqueProd B (Fin 1)).symm (Equiv.uniqueProd B (Fin 1)).symm σ := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi; subst hj
  simp [WildeQIT.Degradable.cqState, kroneckerMap_apply, single_apply]

lemma mi_one {B : Type} [Fintype B] [DecidableEq B] (σ : Matrix B B ℂ) :
    DattaDiscord.mutualInfo (WildeQIT.Degradable.cqState (fun _ : Fin 1 => (1 : ℝ)) (fun _ => σ))
      = QAlgorithms.vnEntropy (Matrix.of fun _ _ : Fin 1 => σ.trace) := by
  unfold DattaDiscord.mutualInfo
  have h1 : QAlgorithms.traceRight (WildeQIT.Degradable.cqState (fun _ : Fin 1 => (1 : ℝ))
      (fun _ => σ)) = Matrix.of fun _ _ : Fin 1 => σ.trace := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi; subst hj
    simp [QAlgorithms.traceRight, WildeQIT.Degradable.cqState, kroneckerMap_apply, single_apply,
      trace]
  have h2 : QAlgorithms.traceLeft (WildeQIT.Degradable.cqState (fun _ : Fin 1 => (1 : ℝ))
      (fun _ => σ)) = σ := by
    ext b b'
    simp [QAlgorithms.traceLeft, WildeQIT.Degradable.cqState, kroneckerMap_apply, single_apply]
  rw [h1, h2, cq_one, vn_reindex]
  ring

end Aux_WildeQIT_13_6_1

open WildeQIT WildeQIT.Degradable Aux_WildeQIT_13_6_1 Matrix ComplexOrder in
theorem solution {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) :
    0 ≤ privateInfoChannel N := by
  classical
  -- traces
  have htrB : ∀ ρ : Matrix a a ℂ, (N.apply ρ).trace = ρ.trace := by
    intro ρ
    unfold QChannel.apply
    rw [trace_sum]
    have e : ∀ i, trace (N.K i * ρ * (N.K i)ᴴ) = trace ((N.K i)ᴴ * N.K i * ρ) := by
      intro i
      rw [trace_mul_comm, ← Matrix.mul_assoc]
    rw [Finset.sum_congr rfl (fun i _ => e i), ← trace_sum, ← Finset.sum_mul, N.complete,
      Matrix.one_mul]
  have htrE : ∀ ρ : Matrix a a ℂ, (complementaryApply N ρ).trace = ρ.trace := by
    intro ρ
    unfold complementaryApply
    have h1 : ∀ X : Matrix (b × N.ι) (b × N.ι) ℂ, (partialTraceLeft X).trace = X.trace := by
      intro X
      simp only [partialTraceLeft, trace, diag_apply, of_apply]
      rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    rw [h1, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
    have hV : (isometricExtension N)ᴴ * isometricExtension N = 1 := by
      rw [← N.complete]
      ext x x'
      simp only [mul_apply, conjTranspose_apply, isometricExtension, of_apply, Matrix.sum_apply]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [hV, Matrix.mul_one]
  -- a one-letter ensemble
  have hn : (0 : ℝ) < (Fintype.card a : ℝ) := by exact_mod_cast Fintype.card_pos
  let σ0 : Matrix a a ℂ := ((1 / (Fintype.card a : ℝ) : ℝ) : ℂ) • (1 : Matrix a a ℂ)
  have hσ0 : IsDensityOperator σ0 := by
    refine ⟨?_, ?_⟩
    · apply Matrix.PosSemidef.smul Matrix.PosSemidef.one
      exact Complex.zero_le_real.2 (le_of_lt (by positivity : (0 : ℝ) < 1 / (Fintype.card a : ℝ)))
    · simp only [σ0, trace_smul, trace_one, smul_eq_mul]
      have : (Fintype.card a : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := a)).ne'
      push_cast
      field_simp
  let ρ0 : CQInput a := ⟨1, ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩, fun _ => σ0,
    fun _ => hσ0⟩
  have hval : DattaDiscord.mutualInfo (cqState ρ0.p.prob fun x => N.apply (ρ0.ρ x)) -
      DattaDiscord.mutualInfo (cqState ρ0.p.prob fun x => complementaryApply N (ρ0.ρ x)) = 0 := by
    show DattaDiscord.mutualInfo (cqState (fun _ : Fin 1 => (1 : ℝ)) fun _ => N.apply σ0) -
      DattaDiscord.mutualInfo (cqState (fun _ : Fin 1 => (1 : ℝ)) fun _ => complementaryApply N σ0)
      = 0
    rw [mi_one, mi_one, htrB, htrE, sub_self]
  unfold privateInfoChannel
  by_cases hbdd : BddAbove (Set.range fun ρ : CQInput a =>
      DattaDiscord.mutualInfo (cqState ρ.p.prob fun x => N.apply (ρ.ρ x)) -
      DattaDiscord.mutualInfo (cqState ρ.p.prob fun x => complementaryApply N (ρ.ρ x)))
  · exact le_ciSup_of_le hbdd ρ0 (le_of_eq hval.symm)
  · rw [Real.iSup_of_not_bddAbove hbdd]
