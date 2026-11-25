-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.oh_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:35.374726+00:00
-- url     : https://prove2.me/submissions/6a8246c5-6863-4d68-a88d-3d5db22ff78b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_PIW_AdelClassFin_dual_intersection


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
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution {e : E} (he : inclR (Af F) e ∈ Oh F E) : IsIntegral ℤ e := by
  let ψ : Af F ⊗[F] E →+* E ⊗[F] Af F := (Algebra.TensorProduct.comm F (Af F) E).toRingHom
  have hψ : ∀ z ∈ Oh F E, ψ z ∈ Formalism.MainNotions.S.IntAf F E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, e', he', rfl⟩ := hz
      have e1 : ψ (a ⊗ₜ[F] e') = (e' ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [e1]
      refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨e', ⟨⟨e', he'⟩, rfl⟩⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact Subring.zero_mem _
    | add x y _ _ h1 h2 => rw [map_add]; exact Subring.add_mem _ h1 h2
    | neg x _ h1 => rw [map_neg]; exact Subring.neg_mem _ h1
  have e2 : ψ (inclR (Af F) e) = Formalism.UG.inclE (F := F) (Af F) e := rfl
  have := PIW.AdelClassFin.dual_intersection F E e (e2 ▸ hψ _ he)
  obtain ⟨b, hb⟩ := this
  rw [← hb]
  exact b.isIntegral_coe
end PI.UnitaryGroupMassFormula.UJClassFin
