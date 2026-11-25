-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__GatR_isAdicComplete_e5d83f2ed8a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:06.562002+00:00
-- url     : https://prove2.me/submissions/bc75dac9-94b4-4232-b986-c6204f65d684

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__GatR_mem_span_om_pow_bf8597fdd0ae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.GatR
open QuadraticAlgebra IsLocalRing
variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {ϖ : W}
namespace Formalism.BasicNotions.Examples₂.GatR
theorem _root_.solution (hϖ : Irreducible ϖ) (hC : IsAdicComplete (Ideal.span {ϖ}) W) :
    haveI := isDomain hϖ; haveI := isDVR hϖ
    IsAdicComplete (maximalIdeal (QuadraticAlgebra W ϖ 0)) (QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  have := isDVR hϖ
  have keyO : ∀ (n : ℕ) (x y : QuadraticAlgebra W ϖ 0),
      x ≡ y [SMOD (maximalIdeal (QuadraticAlgebra W ϖ 0) ^ n • ⊤ : Submodule _ (QuadraticAlgebra W ϖ 0))] ↔
        x - y ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} := fun n x y => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, (om_irreducible hϖ).maximalIdeal_eq,
      Ideal.span_singleton_pow]
  have keyW : ∀ (n : ℕ) (x y : W),
      x ≡ y [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule W W)] ↔ ϖ ^ n ∣ x - y := fun n x y => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hle : ∀ {m n : ℕ}, m ≤ n → Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} ≤ Ideal.span {ω ^ m} :=
    fun h => (Ideal.span_singleton_le_span_singleton).mpr (pow_dvd_pow _ h)
  refine { toIsHausdorff := inferInstance, prec' := fun f hf => ?_ }
  have hf' : ∀ {m n : ℕ}, m ≤ n → f (2 * m) - f (2 * n) ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} :=
    fun h => (keyO _ _ _).mp (hf (Nat.mul_le_mul_left 2 h))
  obtain ⟨a, ha⟩ := hC.toIsPrecomplete.prec' (fun m => (f (2 * m)).re)
    (fun {m n} h => (keyW _ _ _).mpr (by simpa using ((mem_span_om_pow m _).mp (hf' h)).1))
  obtain ⟨b, hb⟩ := hC.toIsPrecomplete.prec' (fun m => (f (2 * m)).im)
    (fun {m n} h => (keyW _ _ _).mpr (by simpa using ((mem_span_om_pow m _).mp (hf' h)).2))
  refine ⟨⟨a, b⟩, fun n => (keyO _ _ _).mpr ?_⟩
  have h1 : f n - f (2 * n) ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} :=
    (keyO _ _ _).mp (hf (by omega))
  have h2 : f (2 * n) - ⟨a, b⟩ ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} :=
    hle (by omega : n ≤ 2 * n) ((mem_span_om_pow n _).mpr
      ⟨by simpa using (keyW _ _ _).mp (ha n), by simpa using (keyW _ _ _).mp (hb n)⟩)
  have e : f n - ⟨a, b⟩ = (f n - f (2 * n)) + (f (2 * n) - ⟨a, b⟩) := by ring
  rw [e]
  exact add_mem h1 h2
end Formalism.BasicNotions.Examples₂.GatR
