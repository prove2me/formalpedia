-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_smul_mem_f84cdc00b338
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:11.565896+00:00
-- url     : https://prove2.me/submissions/9eba644b-bcad-4f4f-bb92-c49448b7da4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange

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
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (M : FullLattice K V) (x : V) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ b • x ∈ M.carrier := by
  have hx : x ∈ Submodule.span K (M.carrier : Set V) := M.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.carrier.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨c, hc, hcz⟩ := hz
    refine ⟨b * c, mul_ne_zero hb hc, ?_⟩
    have e1 : (b * c) • y = c • (b • y) := by rw [mul_comm, mul_smul]
    have e2 : (b * c) • z = b • (c • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact M.carrier.add_mem (M.carrier.smul_mem c hby) (M.carrier.smul_mem b hcz)
  | smul t y _ hy =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) t
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd0
    refine ⟨d * b, mul_ne_zero hd0 hb, ?_⟩
    have key : (d * b) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) • y) = n • (b • y) := by
      rw [← algebraMap_smul K (d * b), ← algebraMap_smul K b y, ← algebraMap_smul K n, smul_smul,
        smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact M.carrier.smul_mem n hby
end GroundTheory.Heights₂.Heights.LatticeLemmas
