-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.TR.transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:05.054049+00:00
-- url     : https://prove2.me/submissions/9e2bbf1c-62d6-44f5-9a60-05716cb603c0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Transf
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_TR_continuous_lmulQ
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_TR_continuous_rmulQ
import Theorems.Thm_Formalism_REAL_isClosedEmbeddingMatrix
import Theorems.Thm_Formalism_REAL_range_coeMatrix
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_continuous_lmulQ
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_continuous_rmulQ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.TR
open PI Formalism.REAL
variable {m : ℕ}
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.TR
theorem _root_.solution : Transfer := by
  intro m ε T S P Q hQP hPQ hS hR μ hσ h0 hcar hl s hs
  set Φ : UJ ε → MtM m := fun g => fun i j => (Q * uMat g * P) i j with hΦdef
  have hΦc : Φ = conjH P Q hQP hPQ ∘ coeMatrixAlt ε := rfl
  have hemb : MeasurableEmbedding Φ := by
    rw [hΦc]
    exact ((conjH P Q hQP hPQ).isClosedEmbedding.comp (isClosedEmbeddingMatrix m ε).1).measurableEmbedding
  have hΦm : Measurable Φ := hemb.measurable

  have hH : IsHaarOnM S (μ.map Φ) := by
    refine ⟨hemb.sigmaFinite_map, (Measure.map_ne_zero_iff hΦm.aemeasurable).2 h0, ?_, ?_⟩
    · rw [hemb.map_apply]
      refine measure_mono_null (fun g hg => ?_) hcar
      intro hT
      exact hg ((hS _).1 ⟨g.2, hT⟩)
    · intro s' hs'
      have ht : inUJ ε (P * s' * Q) ∧ P * s' * Q ∈ T := by
        refine (hS _).2 ?_
        rw [show Q * (P * s' * Q) * P = (Q * P) * s' * (Q * P) by simp only [Matrix.mul_assoc], hQP,
          Matrix.one_mul, Matrix.mul_one]
        exact hs'
      have hr : P * s' * Q ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact ht.1
      obtain ⟨t, htt⟩ := hr
      have hcomm : lmulQ s' ∘ Φ = Φ ∘ (fun x => t * x) := by
        funext g
        show s' * Matrix.of (fun i j => (Q * uMat g * P) i j) = fun i j => (Q * uMat (t * g) * P) i j
        have hu : uMat (t * g) = coeMatrixAlt ε t * uMat g := rfl
        rw [hu, htt]
        funext i j
        show (s' * (Q * uMat g * P)) i j = (Q * (P * s' * Q * uMat g) * P) i j
        rw [show Q * (P * s' * Q * uMat g) * P = (Q * P) * s' * (Q * uMat g * P) by
          simp only [Matrix.mul_assoc], hQP, Matrix.one_mul]
      have htT : t ∈ {g : UJ ε | uMat g ∈ T} := by
        show coeMatrixAlt ε t ∈ T
        rw [htt]; exact ht.2
      rw [Measure.map_map (continuous_lmulQ s').measurable hΦm, hcomm,
        ← Measure.map_map hΦm (continuous_const_mul t).measurable, hl t htT]
  have hRI := hR _ hH
  have hs' : Q * uMat s * P ∈ S := (hS _).1 ⟨s.2, hs⟩
  have hcomm : Φ ∘ (fun x => x * s) = rmulQ (Q * uMat s * P) ∘ Φ := by
    funext g
    show (fun i j => (Q * uMat (g * s) * P) i j) = Matrix.of (fun i j => (Q * uMat g * P) i j) * (Q * uMat s * P)
    have hu : uMat (g * s) = uMat g * uMat s := rfl
    rw [hu]
    funext i j
    show (Q * (uMat g * uMat s) * P) i j = ((Q * uMat g * P) * (Q * uMat s * P)) i j
    rw [show (Q * uMat g * P) * (Q * uMat s * P) = Q * uMat g * (P * Q) * uMat s * P by
      simp only [Matrix.mul_assoc], hPQ, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hmap : (μ.map (fun x => x * s)).map Φ = μ.map Φ := by
    rw [Measure.map_map hΦm (continuous_mul_const s).measurable, hcomm,
      ← Measure.map_map (continuous_rmulQ _).measurable hΦm, hRI _ hs']
  rw [← hemb.comap_map (μ.map (fun x => x * s)), hmap, hemb.comap_map]
end PI.NUnimodLoc.UnitaryGroupMassFormula.TR
