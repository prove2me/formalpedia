-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LocF_emb_finite_635c9e87fdb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:05.713138+00:00
-- url     : https://prove2.me/submissions/05ca8eb9-1d92-462a-b4c6-3a49eea51763

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_emb_cont_73c680fc7d35
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LocF
open NumberField IsDedekindDomain HeightOneSpectrum WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable (l : ℕ) [hl : Fact l.Prime] (hv : (l : 𝓞 F) ∈ v.asIdeal)
open scoped TensorProduct
namespace Formalism.BasicNotions.Examples₂.LocF
theorem _root_.solution : letI := (emb v l hv).toAlgebra
    FiniteDimensional ℚ_[l] (v.adicCompletion F) := by
  let _ := (emb v l hv).toAlgebra
  have : ContinuousSMul ℚ_[l] (v.adicCompletion F) :=
    continuousSMul_of_algebraMap _ _ (emb_cont v l hv)
  have : IsScalarTower ℚ ℚ_[l] (v.adicCompletion F) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let Φ : ℚ_[l] ⊗[ℚ] F →ₗ[ℚ_[l]] v.adicCompletion F :=
    (Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (v.adicCompletion F))
      (algebraMap F (v.adicCompletion F)).toRatAlgHom (fun _ _ => Commute.all _ _)).toLinearMap
  have hd : DenseRange Φ := by
    apply (v.denseRange_algebraMap F).mono
    rintro _ ⟨x, rfl⟩
    refine ⟨1 ⊗ₜ x, ?_⟩
    exact (Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) 1 x).trans (by rw [map_one, one_mul]; rfl)
  exact Module.Finite.of_surjective Φ (by
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact hd.closure_range)
end Formalism.BasicNotions.Examples₂.LocF
