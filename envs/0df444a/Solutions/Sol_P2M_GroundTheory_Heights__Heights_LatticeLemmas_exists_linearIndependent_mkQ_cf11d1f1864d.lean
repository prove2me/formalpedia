-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_linearIndependent_mkQ_cf11d1f1864d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:12.410834+00:00
-- url     : https://prove2.me/submissions/ac3bc96d-12cd-472c-b9f7-1747df9c27d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMeanQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights Submodule Cardinal TensorProduct
universe u v w
noncomputable section
variable {K : Type u} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    {ι : Type w} (x : ι → M.carrier)
    (hx : Module.finrank (𝓞 K) (span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier) :
    ∃ s : Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F)) → ι,
      LinearIndependent (𝓞 K) (fun j ↦ F.mkQ (x (s j))) := by
  classical
  let v : ι → M.carrier ⧸ F := fun i ↦ F.mkQ (x i)
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn (𝓞 K) v
  set N := span (𝓞 K) (v '' s)
  have hS : Module.IsTorsion (𝓞 K) (M.carrier ⧸ span (𝓞 K) (Set.range x)) := by
    rw [← Module.finrank_eq_zero_iff_isTorsion]
    have := Submodule.finrank_quotient_add_finrank (span (𝓞 K) (Set.range x))
    omega
  have hv : span (𝓞 K) (Set.range x) ≤
      (torsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N)).comap (N.mkQ ∘ₗ F.mkQ) := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ s
    · have : N.mkQ (v i) = 0 := by
        rw [mkQ_apply, Quotient.mk_eq_zero]
        exact subset_span ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]
      exact this ▸ zero_mem _
    · obtain ⟨a, ha, hav⟩ := hmax i hi
      simp only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]
      rw [mem_torsion_iff]
      refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
      rw [Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero]
      exact hav
  have hT : Module.IsTorsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N) := by
    intro q
    obtain ⟨q, rfl⟩ := N.mkQ_surjective q
    obtain ⟨m, rfl⟩ := F.mkQ_surjective q
    obtain ⟨a, ha⟩ := hS (x := (span (𝓞 K) (Set.range x)).mkQ m)
    rw [Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero] at ha
    obtain ⟨b, hb⟩ := (mem_torsion_iff _).mp (hv ha)
    refine ⟨b * a, ?_⟩
    rw [Submonoid.smul_def] at hb ⊢
    simpa [mul_smul, map_smul] using hb
  have hrank : Module.rank (𝓞 K) (M.carrier ⧸ F) ≤ #(v '' s) := by
    have h := rank_quotient_add_rank_of_isDomain N
    rw [Module.rank_eq_zero_iff_isTorsion.mpr hT, zero_add] at h
    exact h ▸ rank_span_le _
  have hle : lift.{w} #(Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F))) ≤ lift.{0} #s := by
    have h1 := (lift_le.{w}).mpr hrank
    have h2 := mk_image_le_lift (f := v) (s := s)
    rw [← Module.finrank_eq_rank, lift_natCast] at h1
    rw [mk_fin, lift_natCast, lift_uzero]
    exact (lift_le.{v}).mp (by simpa using h1.trans h2)
  obtain ⟨e⟩ := lift_mk_le'.mp hle
  exact ⟨fun j ↦ (e j : ι), hs.comp e e.injective⟩
end GroundTheory.Heights₂.Heights.LatticeLemmas
