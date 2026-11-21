-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P88.maschke_regular_trace
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T09:00:16.999321+00:00
-- url     : https://prove2.me/submissions/56068ccd-227a-4f06-854c-48a09c9c8b33

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

theorem _root_.solution (F A M : Type*) [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [AddCommGroup M] [Module F M] [Module A M]
    [IsScalarTower F A M] [FiniteDimensional F M]
    (_hnd : TraceNondegenerate (regularTrace (F := F) (A := A))) :
    IsSemisimpleModule A M := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  have hJ : Ring.jacobson A = ⊥ := by
    obtain ⟨n, hn⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson A))
    rw [eq_bot_iff]
    intro b hb
    rw [Submodule.mem_bot]
    by_contra hb0
    obtain ⟨a, ha⟩ := _hnd b hb0
    apply ha
    have hba : b * a ∈ Ring.jacobson A := Ideal.mul_mem_right a _ hb
    have hpow : (b * a) ^ n ∈ Ring.jacobson A ^ n := Submodule.pow_mem_pow _ hba n
    rw [hn, Submodule.zero_eq_bot, Submodule.mem_bot] at hpow
    have hnil : IsNilpotent (Algebra.lmul F A (b * a)) :=
      ⟨n, by rw [← map_pow, hpow, map_zero]⟩
    exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  haveI : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hJ
  infer_instance

end QAlgorithms.Papers.Independent.Intake100.P88
