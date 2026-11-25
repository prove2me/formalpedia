-- Prove2me | solution 1 for PI.VolStabW.tensR_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:33.665862+00:00
-- url     : https://prove2.me/submissions/831e2cff-de5d-437d-a462-8753f1eb16b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfTR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Theorems.Thm_PI_VolStabW_exists_coord_pi
import Theorems.Thm_PI_VolStabW_exists_coord_sub
import Theorems.Thm_PI_VolStabW_exists_coord_tens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation
namespace PI.VolStabW
theorem _root_.solution : TensR := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet
  have : IsTotallyReal F := hCM.1
  obtain ⟨k, eK, hK⟩ := exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := exists_coord_pi eK hK (Fin M)
  obtain ⟨n, eV, hV⟩ := exists_coord_pi e1 h1 (Fin a)
  obtain ⟨k2, e2, h2⟩ := exists_coord_pi eK hK (Fin a)
  obtain ⟨N, eM, hM⟩ := exists_coord_pi e2 h2 (Fin a)
  have hdiv : ∀ n : ℕ, 0 < n → ∀ S ∈ HermR (Ainf F) σ a, ∃ T ∈ HermR (Ainf F) σ a, n • T = S := by
    intro n hn S hS
    let c : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1 / n)
    have hsc : sigR (Ainf F) σ c = c :=
      (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
    refine ⟨c • S, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hsc]
      rw [hS i j]
    · have hc1 : (n : Ainf F ⊗[F] E) * c = 1 := by
        simp only [c]
        rw [← map_natCast (algebraMap F (Ainf F ⊗[F] E)) n, ← map_mul]
        have : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
        rw [mul_one_div_cancel this, map_one]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, hc1, one_mul]
  obtain ⟨m, eH, hH⟩ := exists_coord_sub (X := Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) eM hM
    (HermR (Ainf F) σ a) (isClosed_HermR (Ainf F) σ a) hdiv
  exact ⟨n, m, eV, eH, hV, hH⟩
end PI.VolStabW
