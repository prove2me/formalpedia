-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_mid_6a0fa6ff4b63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:37.635812+00:00
-- url     : https://prove2.me/submissions/2c42a15f-655a-495a-8273-bdfe643859d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_eq_of_mul_006227a8d564
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_mem_idealMod_of_mul_6e0f843cd020
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_idealMod_sup_le_53cef066e13b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
theorem _root_.solution (pp : Ideal (Poly k N)) (hp : pp.IsPrime)
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hle : primeOf (S := k) x ≤ pp)
    (i : Fin (N + 1)) (hi : (X i : Poly k N) ∉ pp) (M : SubSystem k x Ω)
    (hM : ∀ I, ∃ M' : Submodule (chartRing k x I) Ω, M.sub I * M' = 1) :
    eulerCharQuot k ((M.twist (twistSys k x 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)})))
        ((M.twist (twistSys k x 1)).twist (idealSys x pp)) =
      eulerCharQuot k M (M.twist (idealSys x pp)) := by
  have hO : ∀ (I : Chart x) (j : Fin (N + 1)), j ∈ I.1 →
      (twistSys k x 1).sub I = Submodule.span (chartRing k x I) {x j} := fun I j hj => by
    rw [show (twistSys k x 1).sub I = twistMod k x 1 I from rfl, twistMod_eq_span 1 I hj, zpow_one]
  have hsub : ∀ (K : Ideal (Poly k N)) (I : Chart x),
      ((M.twist (twistSys k x 1)).twist (idealSys x K)).sub I =
        idealMod K I * ((twistSys k x 1).sub I * M.sub I) :=
    fun K I => by rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line]; rfl
  have hsub' : ∀ I : Chart x, (M.twist (idealSys x pp)).sub I = idealMod pp I * M.sub I :=
    fun I => by rw [SubSystem.twist_sub_eq_mul_of_line]; rfl
  refine eulerCharQuot_eq_of_mul _ _ _ _ (x i) ?_ ?_ ?_
  · intro I y hy
    obtain ⟨j, hj⟩ := I.2.1
    have hxj : x j ≠ 0 := (mem_support x).mp (I.2.2 hj)
    rw [hsub, hO I j hj]
    have hu : x i / x j ∈ idealMod (pp ⊔ Ideal.span {(X i : Poly k N)}) I :=
      Submodule.subset_span ⟨X i, X j, 1, Ideal.mem_sup_right (Ideal.mem_span_singleton_self _),
        X_mem_monos hj, isHomogeneous_X _ _, isHomogeneous_X _ _, by rw [aeval_X, aeval_X]⟩
    have := Submodule.mul_mem_mul hu (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self (x j)) hy)
    rwa [← mul_assoc (x i / x j), div_mul_cancel₀ _ hxj] at this
  · intro I z hz
    obtain ⟨j, hj⟩ := I.2.1
    have hxj : x j ≠ 0 := (mem_support x).mp (I.2.2 hj)
    rw [hsub, hO I j hj] at hz
    rw [hsub, hO I j hj]
    have hz' := mul_le_mul' (idealMod_sup_le hh (i := i) hj) le_rfl hz
    rw [Submodule.sup_mul] at hz'
    obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.mem_sup.mp hz'
    rw [← mul_assoc, Submodule.span_mul_span, Set.singleton_mul_singleton, div_mul_cancel₀ _ hxj] at hv
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_span_singleton_mul.mp hv
    exact ⟨m, hm, by rwa [add_sub_cancel_right]⟩
  · intro I y hy
    obtain ⟨j, hj⟩ := I.2.1
    rw [hsub, hsub', hO I j hj]
    constructor
    · intro h2
      obtain ⟨M', hM'⟩ := hM I
      have key : ∀ m' ∈ M', y * m' ∈ idealMod pp I := by
        intro m' hm'
        have h3 := Submodule.mul_mem_mul h2 hm'
        rw [mul_assoc, mul_assoc, hM', mul_one, mul_comm, Submodule.mem_span_singleton_mul] at h3
        obtain ⟨q, hq, hqe⟩ := h3
        have hr : y * m' ∈ (1 : Submodule (chartRing k x I) Ω) := hM' ▸ Submodule.mul_mem_mul hy hm'
        obtain ⟨r, hr⟩ := Submodule.mem_one.mp hr
        have hr' : y * m' ∈ chartRing k x I := hr ▸ r.2
        exact mem_idealMod_of_mul hp hle hi hr' hq (by rw [← mul_assoc, hqe])
      have hy1 : y ∈ Submodule.span (chartRing k x I) {y} * (M' * M.sub I) := by
        rw [mul_comm M', hM', mul_one]
        exact Submodule.mem_span_singleton_self y
      rw [← mul_assoc] at hy1
      refine mul_le_mul' (Submodule.mul_le.mpr fun a ha b hb => ?_) le_rfl hy1
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
      exact Submodule.smul_mem _ c (key b hb)
    · intro h2
      have hxi : x i ∈ Submodule.span (chartRing k x I) {x j} := hO I j hj ▸ mem_twistMod_one I i
      have := Submodule.mul_mem_mul hxi h2
      rwa [mul_left_comm] at this
end GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
