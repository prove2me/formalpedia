-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.hormanderLemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:45.45254+00:00
-- url     : https://prove2.me/submissions/825f3dbb-f1d7-45e0-912c-a3374c4bce89

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HormanderLemma
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_split
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_rieszOnRange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open scoped InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    HormanderLemmaStatement E H₁ H₂ := by
  intro ι t K hK hrange v A hA hv hbound
  let G : Submodule ℂ (H₂ × H₁) := weakAdjGraph ι t ⊓ K.comap (LinearMap.fst ℂ H₂ H₁)
  have hG : ∀ p : G, WeakAdj ι t (p : H₂ × H₁).1 (p : H₂ × H₁).2 ∧ (p : H₂ × H₁).1 ∈ K :=
    fun p => ⟨(Submodule.mem_inf.mp p.2).1, (Submodule.mem_inf.mp p.2).2⟩
  obtain ⟨u, -, hu, huv⟩ := rieszOnRange G H₁ ((LinearMap.snd ℂ H₂ H₁).comp G.subtype)
    ((innerₛₗ ℂ v).comp ((LinearMap.fst ℂ H₂ H₁).comp G.subtype)) A hA (by
      intro p
      obtain ⟨h1, h2⟩ := hG p
      simpa using hbound _ h2 _ h1)
  refine ⟨u, hu, fun f w hfw => ?_⟩
  obtain ⟨f₁, f₂, rfl, hf₁, hf₂, hw1, -⟩ := split E H₁ H₂ ι t K hK hrange f w hfw
  have hmem : ((f₁, w) : H₂ × H₁) ∈ G := Submodule.mem_inf.mpr ⟨hw1, hf₁⟩
  have h3 := huv ⟨(f₁, w), hmem⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.snd_apply, LinearMap.fst_apply] at h3
  rw [inner_add_right, Submodule.inner_right_of_mem_orthogonal hv hf₂, add_zero]
  exact h3
end ReciprocityTheory.L2DbarEstimates
