-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__detIdeal_fg_86bcb276e1a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:36.352778+00:00
-- url     : https://prove2.me/submissions/291ffaa6-4896-4153-9eb2-d2d6b967c76e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (L : Submodule (𝓞 E) (Fin N → E)) (hfg : L.FG) : (detIdeal L).FG := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    (S.biUnion fun s => Finset.univ.image s)
  have hL : ∀ x ∈ L, ∀ j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (a : 𝓞 E) • x j := by
    have hle : L ≤ ⨅ j : Fin N, (1 : Submodule (𝓞 E) E).comap
        ((a : 𝓞 E) • (LinearMap.proj j : (Fin N → E) →ₗ[𝓞 E] E)) := by
      rw [← hS, Submodule.span_le]
      intro s hs
      simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.proj_apply, Submodule.mem_one]
      intro j
      exact RingHom.mem_rangeS.mp (ha _ (Finset.mem_biUnion.mpr
        ⟨s, hs, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩))
    intro x hx j
    have h := hle hx
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.smul_apply,
      LinearMap.proj_apply, Submodule.mem_one] at h
    exact h j
  have hgen : ∀ v : Fin N → Fin N → E, (∀ j, v j ∈ L) →
      ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = ((a : 𝓞 E) ^ N) • (Matrix.of v).det := by
    intro v hv
    choose y hy using fun i j => hL (v i) (hv i) j
    have h1 : (algebraMap (𝓞 E) E (a : 𝓞 E)) • Matrix.of v
        = (algebraMap (𝓞 E) E).mapMatrix (Matrix.of y) := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Matrix.of_apply, hy, Algebra.smul_def]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det] at h2
    exact ⟨(Matrix.of y).det, by rw [← h2, Algebra.smul_def, map_pow]⟩
  have hle : detIdeal L ≤ (1 : Submodule (𝓞 E) E).comap
      (((a : 𝓞 E) ^ N) • (LinearMap.id : E →ₗ[𝓞 E] E)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_one]
    exact hgen v hv
  have hfrac : IsFractional (nonZeroDivisors (𝓞 E)) (detIdeal L) := by
    refine ⟨(a : 𝓞 E) ^ N, pow_mem a.2 N, fun b hb => ?_⟩
    have h := hle hb
    rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mem_one] at h
    exact RingHom.mem_rangeS.mpr h
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨detIdeal L, hfrac⟩
end Formalism.BasicNotions.Examples₂
