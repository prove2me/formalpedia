-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.isRat_of_isProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:36.215803+00:00
-- url     : https://prove2.me/submissions/a8a5777c-ad63-4226-adfd-f2a377578014

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    IsRatProjFrame x e := by
  refine ⟨h.inj, h.free, fun i => ?_⟩
  have hmem : ∀ v ∈ coneRing ℤ (x ∘ e), v ∈ coneRing ℚ (x ∘ e) := by
    rintro v ⟨q, rfl⟩
    refine ⟨MvPolynomial.map (algebraMap ℤ ℚ) q, ?_⟩
    unfold coneMap
    exact MvPolynomial.aeval_map_algebraMap ℚ _ _
  let φ : coneRing ℤ (x ∘ e) →+* coneRing ℚ (x ∘ e) :=
    { toFun := fun s => ⟨s.1, hmem s.1 s.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨p, hm, hp⟩ := h.integral i
  refine ⟨p.map φ, hm.map _, ?_⟩
  have hc : (algebraMap (coneRing ℚ (x ∘ e)) (Polynomial Ω)).comp φ =
      algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω) := RingHom.ext fun _ => rfl
  rw [Polynomial.eval₂_map, hc]
  exact hp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
