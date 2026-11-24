-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:04.542731+00:00
-- url     : https://prove2.me/submissions/7741b949-e076-456a-8c4f-cf8bb8c8772e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRetr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FiniteTypeOfFiniteProjectiveExtension
private lemma exists_retr {C D : Type*} [CommRing C] [CommRing D] [Algebra C D] [Module.Finite C D]
    [Module.Projective C D] (h : Function.Injective (algebraMap C D)) :
    ∃ π : D →ₗ[C] C, π 1 = 1 := by
  let J : Ideal C := LinearMap.range (LinearMap.applyₗ (R := C) (M := D) (M₂ := C) (1 : D))
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective C D
  have key : ∀ d : D, d ∈ J • (⊤ : Submodule C D) := by
    intro d
    have hd : d = ∑ i, g d i • f (Pi.single i 1) := by
      have e1 : d = f (g d) := by
        have := LinearMap.congr_fun hfg d
        simpa using this.symm
      conv_lhs => rw [e1, ← Finset.univ_sum_single (g d)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_smul]
      congr 1
      ext j
      simp [Pi.single_apply]
    rw [hd]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    refine LinearMap.mem_range.2 ⟨(LinearMap.proj i).comp (g.comp (LinearMap.mulLeft C d)), ?_⟩
    simp
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤
    (Module.Finite.fg_top) (fun d _ => key d)
  have hr : r = 0 := h (by simpa [Algebra.smul_def] using hr0 1 trivial)
  have h1 : (1 : C) ∈ J := by
    have := J.neg_mem hr1
    simpa [hr] using this
  obtain ⟨π, hπ⟩ := LinearMap.mem_range.1 h1
  exact ⟨π, by simpa using hπ⟩
end FiniteTypeOfFiniteProjectiveExtension
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.FiniteTypeDescent.main
theorem _root_.solution.{u_1, u_2, u_3} :
    ∀ (R : Type u_1) (C : Type u_2) (D : Type u_3) [inst : CommRing R] [inst_1 : CommRing C] [inst_2 : CommRing D]
      [inst_3 : Algebra R C] [inst_4 : Algebra C D] [inst_5 : Algebra R D] [IsScalarTower R C D] [Module.Finite C D]
      [Module.Projective C D],
      Function.Injective (⇑(Algebra.algebraMap C D) : C → D) → ∀ [Algebra.FiniteType R D], Algebra.FiniteType R C := by
  intro R C D _ _ _ _ _ _ _ _ _ hinj hft
  obtain ⟨π, hπ⟩ := FiniteTypeOfFiniteProjectiveExtension.exists_retr (C := C) (D := D) hinj
  obtain ⟨B₀, hB₀, hB₀D⟩ := exists_subalgebra_of_fg R C D hft.out (Module.Finite.fg_top)
  haveI : Module.Finite B₀ D := ⟨hB₀D⟩
  let π' : D →ₗ[B₀] C := π.restrictScalars B₀
  have hsurj : Function.Surjective π' := fun c =>
    ⟨algebraMap C D c, by
      show π (algebraMap C D c) = c
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]⟩
  haveI : Module.Finite B₀ C := Module.Finite.of_surjective π' hsurj
  haveI : Algebra.FiniteType R B₀ := ⟨B₀.fg_top.2 hB₀⟩
  exact Algebra.FiniteType.trans (S := B₀) inferInstance inferInstance
end UpperTheory.Reformulated.B.FiniteTypeDescent.main
