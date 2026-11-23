-- Prove2me | solution 1 for PI.WAU.B.cls_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:40.150375+00:00
-- url     : https://prove2.me/submissions/1172501e-df79-403a-ae2f-ccf0c448cc9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU.B
theorem _root_.solution {M : ℕ} (hM : 0 < M) {a a' : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (ha' : ∀ v, a' v ∈ v.adicCompletionIntegers F)
    (h : cls M a = cls M a') :
    ∃ b : FiniteAdeleRing (𝓞 F) F, (∀ v, b v ∈ v.adicCompletionIntegers F) ∧
      a - a' = (M : FiniteAdeleRing (𝓞 F) F) * b := by
  classical
  have hM0 : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) ((M : F)⁻¹) * (a - a'), fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) ((M : F)⁻¹) * (a v - a' v) ∈ v.adicCompletionIntegers F
    by_cases hv : v ∈ Bad F M
    · have hk := congrFun h ⟨v, hv⟩
      have h1 := (exists_close v ((M : F)⁻¹) (a v)).choose_spec
      have h2 := (exists_close v ((M : F)⁻¹) (a' v)).choose_spec
      simp only [cls] at hk
      rw [hk] at h1
      have hsplit : algebraMap F (v.adicCompletion F) ((M : F)⁻¹) * (a v - a' v) =
          algebraMap F (v.adicCompletion F) ((M : F)⁻¹) *
            (a v - algebraMap F (v.adicCompletion F) (exists_close v ((M : F)⁻¹) (a' v)).choose) -
          algebraMap F (v.adicCompletion F) ((M : F)⁻¹) *
            (a' v - algebraMap F (v.adicCompletion F) (exists_close v ((M : F)⁻¹) (a' v)).choose) := by
        ring
      rw [hsplit]
      exact sub_mem h1 h2
    · have hint : algebraMap F (v.adicCompletion F) ((M : F)⁻¹) ∈ v.adicCompletionIntegers F := by
        rw [mem_adicCompletionIntegers]
        erw [valuedAdicCompletion_eq_valuation']
        simpa [Bad, HeightOneSpectrum.Support] using hv
      exact mul_mem hint (sub_mem (ha v) (ha' v))
  · rw [← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul,
      mul_inv_cancel₀ hM0, map_one, one_mul]
end PI.WAU.B
