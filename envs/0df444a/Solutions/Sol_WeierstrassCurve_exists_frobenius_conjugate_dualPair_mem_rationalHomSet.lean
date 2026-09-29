-- Prove2me | solution 1 for WeierstrassCurve.exists_frobenius_conjugate_dualPair_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b492d200-6d39-5640-ba0b-ad01e275dfa9

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map map_id toAffine evalEvalBC IsRationallyRepresented rationalHomSet isRationallyRepresented_map_of_pow ratPointMap_injective ratPointHom ratPointHom_apply ratPointMap"
p2m_open "WeierstrassCurve"

namespace FrobConjDualPair

open Polynomial
open scoped Polynomial.Bivariate

variable {κ : Type} [Field κ] [DecidableEq κ] (p : ℕ) [ExpChar κ p]

omit [DecidableEq κ] in
theorem evalEvalBC_self (q : κ[X][Y]) (x y : κ) : evalEvalBC κ q x y = q.evalEval x y := by
  rw [evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]

omit [DecidableEq κ] in

theorem evalEvalBC_map_frobenius (q : κ[X][Y]) (x y : κ) :
    evalEvalBC κ (q.map (mapRingHom (frobenius κ p))) (frobenius κ p x) (frobenius κ p y) =
      frobenius κ p (evalEvalBC κ q x y) := by
  rw [evalEvalBC_self, evalEvalBC_self, Polynomial.map_mapRingHom_evalEval]

theorem isRationallyRepresented_ratPointHom_frobenius (W : WeierstrassCurve κ) :
    IsRationallyRepresented κ W (W.map (frobenius κ p)) (ratPointHom (frobenius κ p) (W₀ := W)) := by
  refine ⟨C (X ^ p), 1, X ^ p, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC κ (1 : κ[X][Y]) x y = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC κ (C (X ^ p) : κ[X][Y]) x y / evalEvalBC κ (1 : κ[X][Y]) x y = x ^ p := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC κ (X ^ p : κ[X][Y]) x y / evalEvalBC κ (1 : κ[X][Y]) x y = y ^ p := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : κ, a = x ^ p → b = y ^ p →
      ∃ h', ratPointHom (frobenius κ p) (W₀ := W) (.some x y h) = .some a b h' from H _ _ e1 e2
  rintro a b rfl rfl
  exact ⟨_, rfl⟩

theorem ratPointHom_frobenius_mem_rationalHomSet (W : WeierstrassCurve κ) :
    ratPointHom (frobenius κ p) (W₀ := W) ∈ rationalHomSet κ W (W.map (frobenius κ p)) :=
  Or.inr (isRationallyRepresented_ratPointHom_frobenius p W)

section Perfect

variable [PerfectRing κ p]

theorem ratPointHom_frobenius_bijective (W : WeierstrassCurve κ) :
    Function.Bijective (ratPointHom (frobenius κ p) (W₀ := W)) := by
  refine ⟨ratPointMap_injective _, ?_⟩
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨x', rfl⟩ := (bijective_frobenius κ p).2 x
    obtain ⟨y', rfl⟩ := (bijective_frobenius κ p).2 y
    exact ⟨.some x' y' ((W.toAffine.map_nonsingular (frobenius κ p).injective x' y').mp h), rfl⟩

def frobPointEquiv (W : WeierstrassCurve κ) :
    W.toAffine.Point ≃+ (W.map (frobenius κ p)).toAffine.Point :=
  AddEquiv.ofBijective (ratPointHom (frobenius κ p) (W₀ := W)) (ratPointHom_frobenius_bijective p W)

@[scoped simp] theorem frobPointEquiv_apply (W : WeierstrassCurve κ) (P : W.toAffine.Point) :
    frobPointEquiv p W P = ratPointHom (frobenius κ p) P := rfl

theorem ratPointHom_frobPointEquiv_symm (W : WeierstrassCurve κ)
    (P : (W.map (frobenius κ p)).toAffine.Point) :
    ratPointHom (frobenius κ p) ((frobPointEquiv p W).symm P) = P :=
  (frobPointEquiv p W).apply_symm_apply P

theorem frobPointEquiv_symm_ratPointHom (W : WeierstrassCurve κ) (P : W.toAffine.Point) :
    (frobPointEquiv p W).symm (ratPointHom (frobenius κ p) P) = P :=
  (frobPointEquiv p W).symm_apply_apply P

@[scoped simp] theorem ratPointMap_frobPointEquiv_symm (W : WeierstrassCurve κ)
    (P : (W.map (frobenius κ p)).toAffine.Point) :
    ratPointMap (frobenius κ p) ((frobPointEquiv p W).symm P) = P :=
  ratPointHom_frobPointEquiv_symm p W P

@[scoped simp] theorem frobPointEquiv_symm_ratPointMap (W : WeierstrassCurve κ) (P : W.toAffine.Point) :
    (frobPointEquiv p W).symm (ratPointMap (frobenius κ p) P) = P :=
  frobPointEquiv_symm_ratPointHom p W P

def frobConj (W₁ W₂ : WeierstrassCurve κ) (ψ : W₁.toAffine.Point →+ W₂.toAffine.Point) :
    (W₁.map (frobenius κ p)).toAffine.Point →+ (W₂.map (frobenius κ p)).toAffine.Point :=
  (ratPointHom (frobenius κ p) (W₀ := W₂)).comp
    (ψ.comp (frobPointEquiv p W₁).symm.toAddMonoidHom)

theorem frobConj_apply (W₁ W₂ : WeierstrassCurve κ) (ψ : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (P : (W₁.map (frobenius κ p)).toAffine.Point) :
    frobConj p W₁ W₂ ψ P = ratPointHom (frobenius κ p) (ψ ((frobPointEquiv p W₁).symm P)) := rfl

theorem frobConj_comp (W₁ W₂ : WeierstrassCurve κ) (ψ : W₁.toAffine.Point →+ W₂.toAffine.Point) :
    (frobConj p W₁ W₂ ψ).comp (ratPointHom (frobenius κ p) (W₀ := W₁)) =
      (ratPointHom (frobenius κ p) (W₀ := W₂)).comp ψ := by
  ext P
  simp [frobConj_apply]

theorem frobConj_comp_frobConj (W₁ W₂ W₃ : WeierstrassCurve κ)
    (ψ : W₁.toAffine.Point →+ W₂.toAffine.Point) (ψ' : W₂.toAffine.Point →+ W₃.toAffine.Point) :
    (frobConj p W₂ W₃ ψ').comp (frobConj p W₁ W₂ ψ) = frobConj p W₁ W₃ (ψ'.comp ψ) := by
  ext P
  simp [frobConj_apply]

theorem frobConj_nsmul_id (W : WeierstrassCurve κ) (N : ℕ) :
    frobConj p W W ((N : ℕ) • AddMonoidHom.id _) = (N : ℕ) • AddMonoidHom.id _ := by
  ext P
  simp [frobConj_apply, map_nsmul]

theorem ker_frobConj (W₁ W₂ : WeierstrassCurve κ) (ψ : W₁.toAffine.Point →+ W₂.toAffine.Point) :
    (frobConj p W₁ W₂ ψ).ker = ψ.ker.map (ratPointHom (frobenius κ p) (W₀ := W₁)) := by
  ext P
  simp only [AddMonoidHom.mem_ker, frobConj_apply, AddSubgroup.mem_map]
  constructor
  · intro hP
    refine ⟨(frobPointEquiv p W₁).symm P, ?_, ratPointHom_frobPointEquiv_symm p W₁ P⟩
    have h0 : ratPointHom (frobenius κ p) (ψ ((frobPointEquiv p W₁).symm P)) =
        ratPointHom (frobenius κ p) (W₀ := W₂) 0 := by rw [hP, map_zero]
    exact ratPointMap_injective _ h0
  · rintro ⟨Q, hQ, rfl⟩
    rw [frobPointEquiv_symm_ratPointHom, hQ, map_zero]

theorem isRationallyRepresented_of_comp_eq (W₁ W₂ : WeierstrassCurve κ)
    (α : W₁.toAffine.Point →+ W₂.toAffine.Point) (hα : IsRationallyRepresented κ W₁ W₂ α)
    (β : (W₁.map (frobenius κ p)).toAffine.Point →+ (W₂.map (frobenius κ p)).toAffine.Point)
    (hβ : β.comp (ratPointHom (frobenius κ p) (W₀ := W₁)) =
      (ratPointHom (frobenius κ p) (W₀ := W₂)).comp α) :
    IsRationallyRepresented κ (W₁.map (frobenius κ p)) (W₂.map (frobenius κ p)) β := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine ⟨nX.map (mapRingHom (frobenius κ p)), dX.map (mapRingHom (frobenius κ p)),
    nY.map (mapRingHom (frobenius κ p)), dY.map (mapRingHom (frobenius κ p)),
    frobenius κ p '' B, hB.image _, fun x y h hx => ?_⟩
  obtain ⟨x₀, rfl⟩ := (bijective_frobenius κ p).2 x
  obtain ⟨y₀, rfl⟩ := (bijective_frobenius κ p).2 y
  have h₀ : W₁.toAffine.Nonsingular x₀ y₀ :=
    (W₁.toAffine.map_nonsingular (frobenius κ p).injective x₀ y₀).mp h
  have hx₀ : x₀ ∉ B := fun hx₀ => hx ⟨x₀, hx₀, rfl⟩
  obtain ⟨hdX, hdY, h', hαP⟩ := hrep x₀ y₀ h₀ hx₀
  rw [evalEvalBC_map_frobenius, evalEvalBC_map_frobenius, evalEvalBC_map_frobenius,
    evalEvalBC_map_frobenius]
  refine ⟨(map_ne_zero (frobenius κ p)).mpr hdX, (map_ne_zero (frobenius κ p)).mpr hdY, ?_⟩
  rw [← map_div₀ (frobenius κ p), ← map_div₀ (frobenius κ p)]
  refine ⟨(W₂.toAffine.map_nonsingular (frobenius κ p).injective _ _).mpr h', ?_⟩
  have hβP := DFunLike.congr_fun hβ (.some x₀ y₀ h₀)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at hβP
  calc β (.some (frobenius κ p x₀) (frobenius κ p y₀) h)
      = β (ratPointHom (frobenius κ p) (W₀ := W₁) (.some x₀ y₀ h₀)) := rfl
    _ = ratPointHom (frobenius κ p) (W₀ := W₂) (α (.some x₀ y₀ h₀)) := hβP
    _ = ratPointHom (frobenius κ p) (W₀ := W₂) (.some _ _ h') :=
        congrArg (ratPointHom (frobenius κ p) (W₀ := W₂)) hαP
    _ = _ := rfl

theorem mem_rationalHomSet_of_comp_eq (W₁ W₂ : WeierstrassCurve κ)
    (α : W₁.toAffine.Point →+ W₂.toAffine.Point) (hα : α ∈ rationalHomSet κ W₁ W₂)
    (β : (W₁.map (frobenius κ p)).toAffine.Point →+ (W₂.map (frobenius κ p)).toAffine.Point)
    (hβ : β.comp (ratPointHom (frobenius κ p) (W₀ := W₁)) =
      (ratPointHom (frobenius κ p) (W₀ := W₂)).comp α) :
    β ∈ rationalHomSet κ (W₁.map (frobenius κ p)) (W₂.map (frobenius κ p)) := by
  rcases hα with hα | hα
  ·
    left
    ext P
    obtain ⟨Q, rfl⟩ := (ratPointHom_frobenius_bijective p W₁).2 P
    have hβQ := DFunLike.congr_fun hβ Q
    have hα0 : α Q = 0 := by rw [hα]; rfl
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, hα0, map_zero] at hβQ
    rw [hβQ]
    rfl
  · exact Or.inr (isRationallyRepresented_of_comp_eq p W₁ W₂ α hα β hβ)

theorem frobConj_mem_rationalHomSet (W₁ W₂ : WeierstrassCurve κ)
    (ψ : W₁.toAffine.Point →+ W₂.toAffine.Point) (hψ : ψ ∈ rationalHomSet κ W₁ W₂) :
    frobConj p W₁ W₂ ψ ∈ rationalHomSet κ (W₁.map (frobenius κ p)) (W₂.map (frobenius κ p)) :=
  mem_rationalHomSet_of_comp_eq p W₁ W₂ ψ hψ _ (frobConj_comp p W₁ W₂ ψ)

end Perfect

end FrobConjDualPair
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet.WeierstrassCurve.FrobConjDualPair"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet.WeierstrassCurve.FrobConjDualPair P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet.WeierstrassCurve.FrobConjDualPair P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet.WeierstrassCurve"

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet.WeierstrassCurve WeierstrassCurve.FrobConjDualPair in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W W' : WeierstrassCurve κ) [W.IsElliptic] [W'.IsElliptic]
    (ψ : W.toAffine.Point →+ W'.toAffine.Point) (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
    (ψ' : W'.toAffine.Point →+ W.toAffine.Point) (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
    (N : ℕ) (h₁ : ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _) (h₂ : ψ.comp ψ' = (N : ℕ) • AddMonoidHom.id _) :
    WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W) ∈
        WeierstrassCurve.rationalHomSet κ W (W.map (frobenius κ p)) ∧
    WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W') ∈
        WeierstrassCurve.rationalHomSet κ W' (W'.map (frobenius κ p)) ∧
    ∃ (ψF : (W.map (frobenius κ p)).toAffine.Point →+ (W'.map (frobenius κ p)).toAffine.Point)
      (ψF' : (W'.map (frobenius κ p)).toAffine.Point →+ (W.map (frobenius κ p)).toAffine.Point),
      ψF ∈ WeierstrassCurve.rationalHomSet κ (W.map (frobenius κ p)) (W'.map (frobenius κ p)) ∧
      ψF' ∈ WeierstrassCurve.rationalHomSet κ (W'.map (frobenius κ p)) (W.map (frobenius κ p)) ∧
      ψF.comp (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)) =
        (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W')).comp ψ ∧
      ψF'.comp (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W')) =
        (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)).comp ψ' ∧
      ψF'.comp ψF = (N : ℕ) • AddMonoidHom.id _ ∧ ψF.comp ψF' = (N : ℕ) • AddMonoidHom.id _ ∧
      ψF.ker = ψ.ker.map (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)) := by
  refine ⟨ratPointHom_frobenius_mem_rationalHomSet p W, ratPointHom_frobenius_mem_rationalHomSet p W',
    frobConj p W W' ψ, frobConj p W' W ψ',
    frobConj_mem_rationalHomSet p W W' ψ hψ, frobConj_mem_rationalHomSet p W' W ψ' hψ',
    frobConj_comp p W W' ψ, frobConj_comp p W' W ψ', ?_, ?_, ker_frobConj p W W' ψ⟩
  · rw [frobConj_comp_frobConj, h₁, frobConj_nsmul_id]
  · rw [frobConj_comp_frobConj, h₂, frobConj_nsmul_id]

end S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet (solution)
