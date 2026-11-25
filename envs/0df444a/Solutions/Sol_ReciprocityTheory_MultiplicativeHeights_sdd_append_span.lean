-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_append_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:47:28.497012+00:00
-- url     : https://prove2.me/submissions/8164a4d5-68f6-4159-9172-4f59aae04e69

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_cutProjK_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_proj_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (c b₁ : Fin k₁ → Fin r → K) (hb₀ : IsKBasisIn (B ⊓ cutSub K r e) b₀) (hcB : ∀ j, c j ∈ B)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁ : IsKBasisIn (B.map (projGe K r e)) b₁) :
    ∀ x ∈ B, x ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := by
  intro x hx
  have hfx : projGe K r e x ∈ Submodule.span K (Set.range b₁) :=
    hb₁.2.2 _ (Submodule.mem_map_of_mem hx)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hfx
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) β
  simp only [IsLocalization.IsInteger, RingHom.mem_rangeS] at hd
  choose β' hβ' using hd
  set dK : K := algebraMap (𝓞 K) K d with hdK
  have hd0 : dK ≠ 0 := by
    rw [hdK]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)
  set y : Fin r → K := dK • x - ∑ j, (algebraMap (𝓞 K) K (β' j)) • c j with hy
  have hyB : y ∈ B := by
    refine B.sub_mem ?_ (B.sum_mem fun j _ => ?_)
    · rw [hdK, algebraMap_smul]
      exact B.smul_mem _ hx
    · rw [algebraMap_smul]
      exact B.smul_mem _ (hcB j)
  have hycut : y ∈ cutSub K r e := by
    rw [← sdd_proj_eq_zero_iff, ← sdd_cutProjK_eq, hy, map_sub, map_smul, map_sum]
    simp only [map_smul, sdd_cutProjK_eq, hcb, ← hβ, Finset.smul_sum, smul_smul, hβ']
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def (d : 𝓞 K) (β j)]
  have hys : y ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := by
    refine Submodule.span_mono ?_ (hb₀.2.2 y ⟨hyB, hycut⟩)
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd k₁ i, Fin.append_left b₀ c i⟩
  have hcs : ∀ j, c j ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := fun j =>
    Submodule.subset_span ⟨Fin.natAdd k₀ j, Fin.append_right b₀ c j⟩
  have hx' : x = dK⁻¹ • (y + ∑ j, (algebraMap (𝓞 K) K (β' j)) • c j) := by
    rw [hy, sub_add_cancel, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hys
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs j)))
end ReciprocityTheory.MultiplicativeHeights
