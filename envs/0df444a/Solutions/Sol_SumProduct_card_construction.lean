-- Prove2me | solution 1 for SumProduct.card_construction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:06:54.58325+00:00
-- url     : https://prove2.me/submissions/213e1531-5815-49fd-b742-cdfc6b978574

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
import Theorems.Thm_SumProduct_directness
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
import Theorems.Thm_SumProduct_latticeEmbed_apply
import Theorems.Thm_SumProduct_latticeEquiv_coe
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply
attribute [local simp] SumProduct.idealCountArith_apply_ne
attribute [local simp] SumProduct.latticeEmbed_apply
attribute [local simp] SumProduct.latticeEquiv_coe
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open Real
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {n : ℕ} {r : ℝ} (hrn : r < (n : ℝ))
    (hφ : ((n : ℝ) + r) / ((n : ℝ) - r) < goldenRatio)
    (G : Finset (𝓞 K)ˣ) (B : Finset (𝓞 K)) (hB : ∀ b ∈ B, b ∈ boxAdd K r) :
    ((G ×ˢ B).image
        (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((n : 𝓞 K) + gb.2))).card
      = G.card * B.card := by
  have hinj : Set.InjOn
      (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((n : 𝓞 K) + gb.2)) ↑(G ×ˢ B) := by
    rintro ⟨g₁, b₁⟩ hmem₁ ⟨g₂, b₂⟩ hmem₂ heq
    simp only [Finset.mem_coe, Finset.mem_product] at hmem₁ hmem₂
    obtain ⟨hg, hb⟩ := directness hrn hφ (hB b₁ hmem₁.2) (hB b₂ hmem₂.2) heq
    exact Prod.ext hg hb
  rw [Finset.card_image_of_injOn hinj, Finset.card_product]
end SumProduct
