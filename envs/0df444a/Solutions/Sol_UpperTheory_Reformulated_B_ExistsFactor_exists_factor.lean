-- Prove2me | solution 1 for UpperTheory.Reformulated.B.ExistsFactor.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:32:29.499869+00:00
-- url     : https://prove2.me/submissions/ed1ea4d3-1d78-4d61-8c69-444a5bac070f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ExistsFactor
theorem _root_.solution :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (e : Matrix (Fin n) (Fin n) K),
    e * e = e →
      ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) K) (N : Matrix (Fin r) (Fin n) K),
        N * M = (1 : Matrix (Fin r) (Fin r) K) ∧ M * N = e := by
  intro K _ n e he
  let f : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' e
  have hf : ∀ v, f (f v) = f v := by
    intro v
    have h : f.comp f = f := by
      show (Matrix.toLin' e).comp (Matrix.toLin' e) = Matrix.toLin' e
      rw [← Matrix.toLin'_mul, he]
    exact LinearMap.congr_fun h v
  let b := Module.finBasis K (LinearMap.range f)
  let c := Pi.basisFun K (Fin n)
  refine ⟨Module.finrank K (LinearMap.range f),
    LinearMap.toMatrix b c (LinearMap.range f).subtype,
    LinearMap.toMatrix c b f.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]
    have h : f.rangeRestrict.comp (LinearMap.range f).subtype = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨x, v, rfl⟩
      apply Subtype.ext
      exact hf v
    rw [h, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp]
    have h : (LinearMap.range f).subtype.comp f.rangeRestrict = f := by
      apply LinearMap.ext
      intro v
      rfl
    rw [h]
    show LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) (Matrix.toLin' e) = e
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
end UpperTheory.Reformulated.B.ExistsFactor
