-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:17.244374+00:00
-- url     : https://prove2.me/submissions/422d1a64-ebaa-4da2-8457-c10c835690ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {v : HeightOneSpectrum (𝓞 F)}
private lemma dv_mem_Sv' (d : 𝓞 F) : dv E v d ∈ Sv E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨algebraMap F E (d : F),
    ⟨⟨algebraMap F E (d : F), (RingOfIntegers.isIntegral_coe d).algebraMap⟩, rfl⟩⟩, rfl⟩
end PI.UnitaryApproxFinWork
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {v : HeightOneSpectrum (𝓞 F)}
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (π : 𝓞 F) {A : Matrix n n (E ⊗[F] v.adicCompletion F)} (hA : MS E v A) :
    ∃ s ∈ Sv E v, (1 + dv E v π • A).det = 1 + dv E v π * s := by
  let p : Sv E v := ⟨dv E v π, dv_mem_Sv' π⟩
  let B := toS hA
  let I : Ideal (Sv E v) := Ideal.span {p}
  have hp0 : Ideal.Quotient.mk I p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have h0 : (Ideal.Quotient.mk I).mapMatrix (p • B) = 0 := by
    ext i j
    simp [hp0]
  have hmap : (Ideal.Quotient.mk I).mapMatrix (1 + p • B) = 1 := by
    rw [map_add, map_one, h0, add_zero]
  have hdet : Ideal.Quotient.mk I ((1 + p • B).det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hmap, Matrix.det_one, map_one, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨(t : E ⊗[F] v.adicCompletion F), t.2, ?_⟩
  have h2 : (Sv E v).subtype.mapMatrix (1 + p • B) = 1 + dv E v π • A := by
    rw [map_add, map_one]
    congr 1
  have h4 : (1 + p • B).det = 1 + p * t := by
    rw [mul_comm, ht]
    ring
  rw [← h2, ← RingHom.map_det, h4]
  simp [p]
end PI.UnitaryApproxFinWork
