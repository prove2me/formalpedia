-- Prove2me | solution 1 for PI.VolStabW.smul_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:25.623094+00:00
-- url     : https://prove2.me/submissions/08d6ed5d-0b2f-4ec3-bb23-5b4f45e54725

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Theorems.Thm_PI_VolStabW_lt_one_iff_unif
import Theorems.Thm_PI_VolStabW_unifV_spec
import Theorems.Thm_PI_VolStabW_unifV_val


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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
variable {σ : E →ₐ[F] E} (A : AntiB F E σ)
variable (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))
namespace PI.VolStabW
theorem _root_.solution (z : Fv F v ⊗[F] E) :
    (∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = z) ↔
      (z ∈ lamC v A hD ∧ Valued.v (Xc v A z) < 1 ∧ Valued.v (Yc v A z) < 1) := by
  have hπ := unifV_spec v
  have hπv : Valued.v (unifV v) < 1 := by rw [unifV_val]; decide
  constructor
  · rintro ⟨z', hz', rfl⟩
    rw [mem_lamC] at hz'
    have ex : Xc v A (unifV v • z') = unifV v * Xc v A z' := by
      rw [Xc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have ey : Yc v A (unifV v • z') = unifV v * Yc v A z' := by
      rw [Yc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have h1 : ∀ x ∈ v.adicCompletionIntegers F, Valued.v (unifV v * x) < 1 := by
      intro x hx
      rw [map_mul]
      calc Valued.v (unifV v) * Valued.v x ≤ Valued.v (unifV v) * 1 :=
            mul_le_mul' le_rfl ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx)
        _ < 1 := by rw [mul_one]; exact hπv
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_lamC, ex, ey]; exact ⟨mul_mem hπ.2.2 hz'.1, mul_mem hπ.2.2 hz'.2⟩
    · rw [ex]; exact h1 _ hz'.1
    · rw [ey]; exact h1 _ hz'.2
  · rintro ⟨_, h1, h2⟩
    refine ⟨(unifV v)⁻¹ • z, ?_, ?_⟩
    · rw [mem_lamC, Xc, Yc, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
        smul_eq_mul]
      exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).2
          ((lt_one_iff_unif v _).1 h1),
        (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).2
          ((lt_one_iff_unif v _).1 h2)⟩
    · rw [smul_smul, mul_inv_cancel₀ hπ.1, one_smul]
end PI.VolStabW
