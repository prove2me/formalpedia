-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:14.381412+00:00
-- url     : https://prove2.me/submissions/764fcf82-1c0a-47ad-9b9d-38172e24eed6

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_finMat_emb
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_map_mulVec_vinc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (L : Set (Fin M → E)) (g : UJ (σ : E →+* E) J) (h : HA (AF F) σ J) :
    abelian₂ σ J L (emb σ J g * h) =
      (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' abelian₂ σ J L h := by
  ext x
  have hinv : (emb σ J g * h)⁻¹ = h⁻¹ * emb σ J g⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
  have h1 : ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *
      (((g⁻¹ : UJ (σ : E →+* E) J) : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have h2 : (((g⁻¹ : UJ (σ : E →+* E) J) : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *
      ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  simp only [abelian₂, Set.mem_ofPred_eq, Set.mem_image, hinv, finMat_mul, ← Matrix.mulVec_mulVec, finMat_emb,
    map_mulVec_vinc]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
end PI.UnitaryGroupMassFormula.UJClassFin
