-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tilde_gmul_le_fcc9035f3d08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:03:14.183171+00:00
-- url     : https://prove2.me/submissions/61f58328-69cc-4b6a-8aca-cc67a877e5cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
theorem _root_.solution (M : FinGradedSub (S := S) (x := x) E) {s : ℕ} (h : Fin s → Poly S N) (d : Fin s → ℕ)
    (hh : ∀ l, (h l).IsHomogeneous (d l)) {J : Ideal (Poly S N)} (hJ : ∀ l, h l ∈ J) (F : SubSystem S x E)
    (hF : ∀ I, M.tilde 0 I ≤ F.sub I) (I : Chart x) :
    (gmul M h d).tilde 0 I ≤ (F.twist (idealSys x J)).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, t, a, e, ht, hte, hm, hae, rfl⟩
  have ht0 := eval_ne_zero_of_mem_monos I ht
  change m ∈ Submodule.span S _ at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, b, m, hm, hb, rfl⟩ := hz
    have hX0 : aeval x (X i ^ d l : Poly S N) ≠ 0 := by
      rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
    have hq : aeval x (h l) / aeval x (X i ^ d l : Poly S N) ∈ (idealSys x J).sub I :=
      Submodule.subset_span ⟨h l, X i ^ d l, d l, hJ l, pow_mem (X_mem_monos hi) _, hh l,
        isHomogeneous_X_pow i _, rfl⟩
    have hy : (aeval x t)⁻¹ • (aeval x (X i ^ d l : Poly S N) • m) ∈ F.sub I := by
      refine hF I (Submodule.subset_span ⟨_, t, a, e, ht, hte, ?_, hae, rfl⟩)
      have := M.smul_mem (d l) b (X i ^ d l) m (isHomogeneous_X_pow i _) hm
      rwa [hb] at this
    refine Submodule.subset_span ⟨_, hq, _, hy, ?_⟩
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r hz
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
