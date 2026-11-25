-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_diag_le_of_prop_35f1667a3ed2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:28.365697+00:00
-- url     : https://prove2.me/submissions/0d62ac57-ce83-4a7f-b053-74b956169668

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffMinor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_map_comp_subst_dde6ca6167d5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
omit [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) (W : Ideal (MRing (T.wwIdx ι ν κ))) [W.IsPrime] (hW : T.wwIdeal x δ e φ a₀ a₁ ≤ W) (m : κ)
    (hm : (X ⟨.line0, m⟩ : MRing (T.wwIdx ι ν κ)) ∉ W)
    (hprop : ∀ q : κ, (X ⟨.line0, m⟩ * X ⟨.line1, q⟩ - X ⟨.line1, m⟩ * X ⟨.line0, q⟩ :
      MRing (T.wwIdx ι ν κ)) ∈ W) :
    T.wwIdeal x δ e φ a₀ a₀ ≤ W := by
  classical
  let K := FractionRing (MRing (T.wwIdx ι ν κ) ⧸ W)
  let π : MRing (T.wwIdx ι ν κ) →+* K := (algebraMap _ K).comp (Ideal.Quotient.mk W)
  have hπ : ∀ g, π g = 0 ↔ g ∈ W := fun g => by
    simp only [π, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let σ := eval₂Hom (Int.castRingHom (Polynomial (MRing (T.wwIdx ι ν κ)))) (lineSubst ι ν κ)
  have hm' : π (X ⟨.line0, m⟩) ≠ 0 := fun h => hm ((hπ _).1 h)
  have hσ : (Polynomial.eval₂RingHom π (π (X ⟨.line1, m⟩) / π (X ⟨.line0, m⟩))).comp σ = π := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [σ]
    · rintro ⟨b, q⟩
      cases b
      · simp [σ, lineSubst]
      · simp [σ, lineSubst]
      · simp [σ, lineSubst]
      · have h := (hπ _).2 (hprop q)
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
        simp only [σ, RingHom.comp_apply, eval₂Hom_X', lineSubst, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rw [mul_div_assoc', div_eq_iff hm']
        linear_combination -h
  intro g hg
  rw [T.wwIdeal, RingHom.mem_ker] at hg
  have h1 : Polynomial.mapRingHom (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁)) (σ g) = 0 := by
    rw [← RingHom.comp_apply, map_comp_subst, RingHom.comp_apply, hg, map_zero]
  have h2 : (σ g).map π = 0 := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, hπ]
    refine hW ?_
    rw [T.wwIdeal, RingHom.mem_ker]
    have := congrArg (fun f => Polynomial.coeff f n) h1
    simpa [Polynomial.coeff_map] using this
  rw [← hπ, ← hσ, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map, h2,
    Polynomial.eval_zero]
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
