-- Prove2me | solution 1 for SumProduct.count_le_boxAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:06:50.573804+00:00
-- url     : https://prove2.me/submissions/fd1f6003-3f18-4291-9dfb-36af0e256d05

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_latticeEmbed_apply
import Theorems.Thm_SumProduct_normAtPlace_latticeEmbed
import Theorems.Thm_SumProduct_mem_convexBodyLT_iff
import Theorems.Thm_SumProduct_latticeEquiv_coe
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult


attribute [local simp] SumProduct.latticeEmbed_apply
attribute [local simp] SumProduct.latticeEquiv_coe

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.ncard
      ≤ (boxAdd K (2 * (r : ℝ))).card := by
  set T := {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} with hT
  rcases T.eq_empty_or_nonempty with he | ⟨α₀, hα₀⟩
  · simp [he]
  · have hinj : Set.InjOn (· - α₀) T := fun a _ b _ h => by linear_combination h
    have hsub : (· - α₀) '' T ⊆ ↑(boxAdd K (2 * (r : ℝ))) := by
      rintro _ ⟨α, hα, rfl⟩
      have hαmem : latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r) := hα
      have hα₀mem : latticeEmbed K α₀ + x ∈ convexBodyLT K (fun _ => r) := hα₀
      rw [Finset.mem_coe, mem_boxAdd]
      intro w
      rw [← normAtPlace_latticeEmbed]
      have e : latticeEmbed K (α - α₀)
          = (latticeEmbed K α + x) - (latticeEmbed K α₀ + x) := by rw [map_sub]; abel
      rw [e]
      have key : normAtPlace w ((latticeEmbed K α + x) - (latticeEmbed K α₀ + x))
          ≤ normAtPlace w (latticeEmbed K α + x) + normAtPlace w (latticeEmbed K α₀ + x) := by
        calc normAtPlace w ((latticeEmbed K α + x) - (latticeEmbed K α₀ + x))
            = normAtPlace w ((latticeEmbed K α + x) + -(latticeEmbed K α₀ + x)) := by
              rw [sub_eq_add_neg]
          _ ≤ normAtPlace w (latticeEmbed K α + x)
              + normAtPlace w (-(latticeEmbed K α₀ + x)) := normAtPlace_add_le w _ _
          _ = normAtPlace w (latticeEmbed K α + x)
              + normAtPlace w (latticeEmbed K α₀ + x) := by rw [normAtPlace_neg]
      have h1 := (mem_convexBodyLT_iff _ _).mp hαmem w
      have h2 := (mem_convexBodyLT_iff _ _).mp hα₀mem w
      have : (2 : ℝ) * (r : ℝ) = (r : ℝ) + (r : ℝ) := by ring
      linarith
    calc T.ncard = ((· - α₀) '' T).ncard := (Set.InjOn.ncard_image hinj).symm
      _ ≤ (↑(boxAdd K (2 * (r : ℝ))) : Set (𝓞 K)).ncard :=
            Set.ncard_le_ncard hsub (boxAdd K (2 * (r : ℝ))).finite_toSet
      _ = (boxAdd K (2 * (r : ℝ))).card := Set.ncard_coe_finset _
end SumProduct
