-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.topStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:02:57.349908+00:00
-- url     : https://prove2.me/submissions/1d22c27b-5dee-4db1-b937-8f40c857920f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_TopStep
import Theorems.Thm_PI_UnitaryApproxFinWork_dv_mul
import Theorems.Thm_PI_UnitaryApproxFinWork_exists_int_mul
import Theorems.Thm_PI_UnitaryApproxFinWork_inclE_mem_Sv
import Theorems.Thm_PI_UnitaryApproxFinWork_scU_mem_UJ
import Theorems.Thm_PI_UnitaryApproxFinWork_scU_val
import Theorems.Thm_PI_UnitaryApproxFinWork_sigR_inclE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution : TopStep := by
  unfold TopStep CayleyFin EigAvoid PI.UnitaryApproxFin.UnitaryApproxFin
  intro hC hE F E iF iNF iE iNE iA n iFt iDe σ J hσ hθ hJ hdet T g hg D hD
  obtain ⟨μ, hμ, hinv⟩ := hE F E n σ hσ hθ T (fun v => ((g v : GL n _) : Matrix n n _))
  have hμ' : μ * σ μ = 1 := by rw [mul_comm]; exact hμ
  have hab : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) = 1 := fun v => by
    rw [← map_mul, hμ', map_one]
  have hρ : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := fun v => by
    rw [sigR_inclE, ← map_mul, hμ, map_one]
  obtain ⟨c, hc0, hc⟩ := exists_int_mul (F := F) (σ μ)
  obtain ⟨γ', hγ', hcong⟩ := hC F E n σ J hσ hJ hdet T
    (fun v => scU (n := n) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ)
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ)) (hab v) * g v)
    (fun v hv => Subgroup.mul_mem _
      (scU_mem_UJ (n := n) (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
        (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) _ _ _ (hρ v)) (hg v hv))
    (fun v hv => by
      simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul]
      exact hinv v hv)
    (D * c) (mul_ne_zero hD hc0)
  refine ⟨scU (n := n) (σ μ) μ hμ * γ',
    Subgroup.mul_mem _ (scU_mem_UJ (n := n) (σ : E →+* E) J (σ μ) μ hμ ?_) hγ', ?_⟩
  · show σ (σ μ) * σ μ = 1
    rw [hσ, hμ']
  · intro v hv i j
    obtain ⟨s, hs, hseq⟩ := hcong v hv i j
    refine ⟨PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F) * σ μ) * s,
      Subring.mul_mem _ (inclE_mem_Sv v hc) hs, ?_⟩
    have hdv : dv E v (D * c) =
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) *
          PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) :=
      dv_mul v D c
    have hba : PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := by
      rw [← map_mul, hμ, map_one]
    simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul] at hseq ⊢
    rw [hdv] at hseq
    simp only [map_mul]
    linear_combination PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) * hseq -
      ((g v : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j * hba
end PI.UnitaryApproxFinWork
