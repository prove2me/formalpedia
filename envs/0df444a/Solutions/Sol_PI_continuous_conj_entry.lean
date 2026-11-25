-- Prove2me | solution 1 for PI.continuous_conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:18:20.849581+00:00
-- url     : https://prove2.me/submissions/3cd80469-b392-4029-8a93-c83d3a48905a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicFiniteOrder_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI
open NumberField IsDedekindDomain TensorProduct Matrix
namespace PI
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (k : ℕ)
    (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (i j : Fin k) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) := by
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  let : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  have : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have : ContinuousAdd (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  have hmul : ∀ c d : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Continuous (fun z => c * z * d) := by
    intro c d
    have := IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F)
      ((LinearMap.mulRight (FiniteAdeleRing (𝓞 F) F) d).comp
        (LinearMap.mulLeft (FiniteAdeleRing (𝓞 F) F) c))
    exact this
  have he : ∀ a b : Fin k, Continuous (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      (u : Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hfun : (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) =
      fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => ∑ b, ∑ a, (y : Matrix (Fin k) (Fin k) _) i a *
        (u : Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b *
        ((y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin k) (Fin k) _) b j := by
    funext u
    simp only [Units.val_mul, Matrix.mul_apply, Finset.sum_mul]
  rw [hfun]
  exact continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun a _ => (hmul _ _).comp (he a b)
end PI
