-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.no_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:52:28.612714+00:00
-- url     : https://prove2.me/submissions/d3d33ca9-7f64-4400-82c7-e2ebd5795453

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_half_not_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) (x : Fin r → K) (hx : x ≠ 0) (hline : ∀ t : K, t • x ∈ L) : False := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (S.biUnion fun v => Finset.univ.image v)
  have hb0 : (b : K) ≠ 0 := by
    intro h0
    have : b = 0 := by exact_mod_cast h0
    exact nonZeroDivisors.ne_zero hb this
  have hgen : ∀ v ∈ S, ∀ j, IsIntegralElt ((b : K) * v j) := by
    intro v hv j
    obtain ⟨z, hz⟩ := hbint (v j) (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
    refine ⟨z, ?_⟩
    show algebraMap (𝓞 K) K z = _
    rw [hz, Algebra.smul_def]
  have hall : ∀ w ∈ L, ∀ j, IsIntegralElt ((b : K) * w j) := by
    intro w hw
    rw [← hS] at hw
    induction hw using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => intro j; exact ⟨0, by simp⟩
    | add v w _ _ hv hw =>
      intro j
      obtain ⟨z1, hz1⟩ := hv j
      obtain ⟨z2, hz2⟩ := hw j
      refine ⟨z1 + z2, ?_⟩
      push_cast
      rw [Pi.add_apply, mul_add]
      exact congrArg₂ (· + ·) hz1 hz2
    | smul a v _ hv =>
      intro j
      obtain ⟨z, hz⟩ := hv j
      refine ⟨a * z, ?_⟩
      push_cast
      rw [Pi.smul_apply, Algebra.smul_def]
      calc (a : K) * (z : K) = (a : K) * ((b : K) * v j) := congrArg (fun q => (a : K) * q) hz
        _ = (b : K) * (algebraMap (𝓞 K) K a * v j) := by
          show (a : K) * ((b : K) * v j) = (b : K) * ((a : K) * v j)
          ring
  have h1 := hall _ (hline ((2 * (b : K) * x i)⁻¹)) i
  apply half_not_integral (K := K)
  convert h1 using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
end ReciprocityTheory.MultiplicativeHeights.SemiPt
