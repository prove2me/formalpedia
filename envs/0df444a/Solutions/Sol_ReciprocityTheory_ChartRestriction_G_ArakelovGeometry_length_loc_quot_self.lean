-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.length_loc_quot_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:26.635798+00:00
-- url     : https://prove2.me/submissions/00cfacd8-ed2d-4e93-ae57-b9fc733859ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ P)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  have hne : ∀ (r : R) (t : P.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk P r) t = 0 → r ∈ P := by
    intro r t h0
    rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    rw [smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, smul_zero, Ideal.Quotient.eq_zero_iff_mem] at hu
    rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hu with h1 | h1
    · exact absurd h1 u.2
    · rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› h1 with h2 | h2
      · exact absurd h2 t.2
      · exact h2
  constructor
  · refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk P 1) 1, 0, fun h0 => ?_⟩⟩
    exact ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr (hne 1 1 h0))
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
      have hr : r ∈ P.primeCompl := fun hrP => hx (by
        rw [(Ideal.Quotient.eq_zero_iff_mem.mpr hrP), LocalizedModule.zero_mk])
      induction y using LocalizedModule.induction_on with
      | h m' t' =>
        obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
        refine ⟨Localization.mk (r' * t) (t' * ⟨r, hr⟩), ?_⟩
        rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq, ← map_mul]
        congr 1
        ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
