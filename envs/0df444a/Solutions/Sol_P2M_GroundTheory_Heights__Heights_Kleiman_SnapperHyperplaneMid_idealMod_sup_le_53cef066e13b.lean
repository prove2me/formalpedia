-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_idealMod_sup_le_53cef066e13b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:22.311168+00:00
-- url     : https://prove2.me/submissions/1f734bd0-2c8d-4220-afa4-ed919206ffd3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_homogeneousComponent_mul_form_2336838196fb


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
theorem _root_.solution {pp : Ideal (Poly k N)} (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp)
    {i j : Fin (N + 1)} {I : Chart x} (hj : j ∈ I.1) :
    idealMod (pp ⊔ Ideal.span {(X i : Poly k N)}) I ≤
      idealMod pp I ⊔ Submodule.span (chartRing k x I) {x i / x j} := by
  have hxj : x j ≠ 0 := (mem_support x).mp (I.2.2 hj)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [SetLike.mem_coe, ← homogeneousComponent_eq_self hfe, map_add, map_add, add_div]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span
    ⟨homogeneousComponent e g, s, e, hh g hg e, hs, homogeneousComponent_isHomogeneous e g, hse, rfl⟩))
    (Submodule.mem_sup_right ?_)
  have hspan := IdealTwistFamily.homogeneousComponent_mul_form h (X i) (isHomogeneous_X k i) e
  generalize homogeneousComponent e (h * X i) = v at hspan ⊢
  induction hspan using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h', d', hh', hd', rfl⟩ := hv
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨aeval x (h' * X j) / aeval x s, h' * X j, s, e, hs, hd' ▸ hh'.mul (isHomogeneous_X k j), hse,
      rfl⟩, ?_⟩
    rw [chartRing_smul_def]
    simp only [map_mul, aeval_X]
    field_simp
  | zero => simp
  | add v w _ _ hv hw => rw [map_add, add_div]; exact Submodule.add_mem _ hv hw
  | smul c v _ hv =>
    rw [map_smul, smul_div_assoc]
    exact Submodule.smul_of_tower_mem _ c hv
end GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
