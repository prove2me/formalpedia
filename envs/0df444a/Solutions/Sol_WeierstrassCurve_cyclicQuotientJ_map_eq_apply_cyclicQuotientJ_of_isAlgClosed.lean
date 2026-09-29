-- Prove2me | solution 1 for WeierstrassCurve.cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/cf28dd09-4285-5d77-be5a-738dffbda299

import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_MapPoint
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"

set_option autoImplicit false

universe u v

open WeierstrassCurve

namespace CycQJMapAux

variable {L : Type u} {L' : Type v} [Field L] [Field L'] [DecidableEq L] [DecidableEq L'] (σ : L →+* L')

theorem cyclicQuotientJ_map_congr {V : WeierstrassCurve L} {W₁ W₂ : WeierstrassCurve L'} (hW : W₁ = W₂)
    (φ₁ : V.toAffine.Point →+ W₁.toAffine.Point) (φ₂ : V.toAffine.Point →+ W₂.toAffine.Point)
    (hφ₁ : ∀ (x y : L) (h : V.toAffine.Nonsingular x y), ∃ h', φ₁ (.some x y h) = .some (σ x) (σ y) h')
    (hφ₂ : ∀ (x y : L) (h : V.toAffine.Nonsingular x y), ∃ h', φ₂ (.some x y h) = .some (σ x) (σ y) h')
    (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    W₁.cyclicQuotientJ (H.map φ₁) N = W₂.cyclicQuotientJ (H.map φ₂) N := by
  subst hW
  have hφ : φ₁ = φ₂ := by
    ext P
    rcases P with _ | ⟨x, y, h⟩
    · exact (map_zero φ₁).trans (map_zero φ₂).symm
    · obtain ⟨h₁, e₁⟩ := hφ₁ x y h
      obtain ⟨h₂, e₂⟩ := hφ₂ x y h
      rw [e₁, e₂]
  rw [hφ]

theorem main_aux [IsAlgClosed L] (V₀ : WeierstrassCurve L) (V : WeierstrassCurve L) (hV : V₀.baseChange L = V)
    (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    (V.map σ).cyclicQuotientJ (H.map (WeierstrassCurve.mapPointHom σ)) N = σ (V.cyclicQuotientJ H N) := by
  subst hV
  letI : Algebra L L' := σ.toAlgebra
  let f : L →ₐ[L] L' := Algebra.ofId L L'
  have hf : ∀ a : L, f a = σ a := fun _ => rfl
  have key := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed V₀ f H N
  have hW : (V₀.baseChange L).map σ = V₀.baseChange L' := by
    ext <;> rfl
  have e := cyclicQuotientJ_map_congr σ hW (WeierstrassCurve.mapPointHom σ)
    (WeierstrassCurve.Affine.Point.map f) (fun x y h => ⟨_, rfl⟩)
    (fun x y h => ⟨_, by rw [WeierstrassCurve.Affine.Point.map_some]; rfl⟩) H N
  exact e.trans (key.trans (hf _))

end CycQJMapAux

theorem solution
    {L : Type u} {L' : Type v} [Field L] [Field L'] [DecidableEq L] [DecidableEq L'] [IsAlgClosed L] (σ : L →+* L')
    (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    (V.map σ).cyclicQuotientJ (H.map (WeierstrassCurve.mapPointHom σ)) N = σ (V.cyclicQuotientJ H N) := by
  exact CycQJMapAux.main_aux σ V V (by ext <;> rfl) H N

end S_WeierstrassCurve_cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed (solution)
