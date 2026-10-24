-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P02.nuclear_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:15:06.037453+00:00
-- url     : https://prove2.me/submissions/1de67bf5-f28e-4485-a46a-3e0aa02835ee

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

lemma X7A14_adj_rep (T : H →L[F] H) (f : ℕ → (H →L[F] F)) (y : ℕ → H)
    (h : BanachNuclearRepresentation T f y) :
    BanachNuclearRepresentation (ContinuousLinearMap.adjoint T)
      (fun k => innerSL F (y k)) (fun k => (InnerProductSpace.toDual F H).symm (f k)) ∧
    (∑' k, ‖innerSL F (y k)‖ * ‖(InnerProductSpace.toDual F H).symm (f k)‖) =
      ∑' k, ‖f k‖ * ‖y k‖ := by
  obtain ⟨hs, hx⟩ := h
  set z : ℕ → H := fun k => (InnerProductSpace.toDual F H).symm (f k) with hz
  have hzn : ∀ k, ‖z k‖ = ‖f k‖ := fun k => by simp [hz]
  have hcost : (fun k => ‖innerSL F (y k)‖ * ‖z k‖) = fun k => ‖f k‖ * ‖y k‖ := by
    funext k; rw [innerSL_apply_norm, hzn, mul_comm]
  refine ⟨⟨?_, fun x => ?_⟩, ?_⟩
  · show Summable (fun k => ‖innerSL F (y k)‖ * ‖z k‖)
    rw [hcost]; exact hs
  · -- absolute summability
    have habs : Summable (fun k => ‖(innerSL F (y k) x) • z k‖) := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hs.mul_right ‖x‖)
      rw [norm_smul, hzn]
      have : ‖innerSL F (y k) x‖ ≤ ‖y k‖ * ‖x‖ := by
        rw [innerSL_apply_apply]; exact norm_inner_le_norm _ _
      calc ‖innerSL F (y k) x‖ * ‖f k‖ ≤ (‖y k‖ * ‖x‖) * ‖f k‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = ‖f k‖ * ‖y k‖ * ‖x‖ := by ring
    obtain ⟨s, hsum⟩ := habs.of_norm
    convert hsum using 1
    apply ext_inner_left F
    intro w
    have h1 : HasSum (fun k => inner F w ((innerSL F (y k) x) • z k)) (inner F w s) :=
      hsum.mapL (innerSL F w)
    have h2 : HasSum (fun k => inner F x ((f k w) • y k)) (inner F x (T w)) :=
      (hx w).mapL (innerSL F x)
    have h3 := h2.star
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm]
    refine (h3.unique ?_)
    convert h1 using 1
    funext k
    simp only [innerSL_apply_apply, inner_smul_right, hz]
    rw [← inner_conj_symm w, InnerProductSpace.toDual_symm_apply]
    simp [inner_conj_symm, mul_comm]
  · rw [show (fun k => ‖innerSL F (y k)‖ * ‖(InnerProductSpace.toDual F H).symm (f k)‖) =
        fun k => ‖f k‖ * ‖y k‖ from hcost]

lemma X7A14_costs_sub (T : H →L[F] H) :
    {r : ℝ | ∃ (f : ℕ → (H →L[F] F)) (y : ℕ → H),
      BanachNuclearRepresentation T f y ∧ r = ∑' k, ‖f k‖ * ‖y k‖} ⊆
    {r : ℝ | ∃ (f : ℕ → (H →L[F] F)) (y : ℕ → H),
      BanachNuclearRepresentation (ContinuousLinearMap.adjoint T) f y ∧
        r = ∑' k, ‖f k‖ * ‖y k‖} := by
  rintro _ ⟨f, y, h, rfl⟩
  obtain ⟨h1, h2⟩ := X7A14_adj_rep T f y h
  exact ⟨_, _, h1, h2.symm⟩

lemma X7A14_nuclear_adjoint (T : H →L[F] H) :
    (IsNuclear T ↔ IsNuclear (ContinuousLinearMap.adjoint T)) ∧
      (IsNuclear T → banachNuclearNorm (ContinuousLinearMap.adjoint T) = banachNuclearNorm T) := by
  have hset : {r : ℝ | ∃ (f : ℕ → (H →L[F] F)) (y : ℕ → H),
      BanachNuclearRepresentation T f y ∧ r = ∑' k, ‖f k‖ * ‖y k‖} =
    {r : ℝ | ∃ (f : ℕ → (H →L[F] F)) (y : ℕ → H),
      BanachNuclearRepresentation (ContinuousLinearMap.adjoint T) f y ∧
        r = ∑' k, ‖f k‖ * ‖y k‖} := by
    apply Set.Subset.antisymm (X7A14_costs_sub T)
    have := X7A14_costs_sub (ContinuousLinearMap.adjoint T)
    rwa [ContinuousLinearMap.adjoint_adjoint] at this
  refine ⟨⟨fun ⟨f, y, h⟩ => ⟨_, _, (X7A14_adj_rep T f y h).1⟩, fun ⟨f, y, h⟩ => ?_⟩, fun _ => ?_⟩
  · have := (X7A14_adj_rep _ f y h).1
    rw [ContinuousLinearMap.adjoint_adjoint] at this
    exact ⟨_, _, this⟩
  · unfold banachNuclearNorm
    rw [hset]

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end

noncomputable section

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

open QAlgorithms.Papers.Independent.Next46.P02 in
theorem solution (T : H →L[F] H) :
    (IsNuclear T ↔ IsNuclear (ContinuousLinearMap.adjoint T)) ∧
      (IsNuclear T → banachNuclearNorm (ContinuousLinearMap.adjoint T) = banachNuclearNorm T) :=
  X7A14_nuclear_adjoint T

end Hilbert

end
