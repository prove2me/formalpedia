-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.quotGram_det_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:03:24.902824+00:00
-- url     : https://prove2.me/submissions/ea9ff0c5-406c-4d78-a3f2-f9953fafdda9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotGram_eq_conjTranspose_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_embeddingColumns_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_linearIndependent_map_embedding
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotientGram_det_re_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) {m : ℕ} {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) (hli : LinearIndependent K (Fin.append b c)) :
    0 < (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by
  have hinj : Function.Injective (hPm σ b * hBm σ c).mulVec := by
    intro z z' hzz
    have h0 : hPm σ b *ᵥ (hBm σ c *ᵥ (z - z')) = 0 := by
      rw [mulVec_mulVec, mulVec_sub, hzz, sub_self]
    set y := ((hBm σ b)ᴴ * hBm σ b)⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ (hBm σ c *ᵥ (z - z'))) with hy
    have h1 : hBm σ c *ᵥ (z - z') - hBm σ b *ᵥ y = 0 := by
      have h2 := h0
      simp only [hPm, sub_mulVec, one_mulVec, ← mulVec_mulVec] at h2
      exact h2
    have hl := linearIndependent_map_embedding σ hli
    have h3 : ∑ i, Fin.append (-y) (z - z') i • (fun l => σ (Fin.append b c i l)) = 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← h1, embeddingColumns_mulVec, embeddingColumns_mulVec]
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
      abel
    have h4 := Fintype.linearIndependent_iff.mp hl _ h3
    funext j
    have := h4 (Fin.natAdd k j)
    rw [Fin.append_right] at this
    exact sub_eq_zero.mp this
  have hpd := PosDef.conjTranspose_mul_self (hPm σ b * hBm σ c) hinj
  rw [← quotGram_eq_conjTranspose_mul σ hb c] at hpd
  have hpos := hpd.det_pos
  rw [← quotientGram_det_re_eq σ hb c] at hpos
  exact_mod_cast hpos
end ReciprocityTheory.ChartRestriction.G.T0
