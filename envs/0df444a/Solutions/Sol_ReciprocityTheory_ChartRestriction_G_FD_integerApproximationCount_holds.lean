-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.integerApproximationCount_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:24.748813+00:00
-- url     : https://prove2.me/submissions/69f9061c-ae44-4a61-a0e1-ad158ae67bed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RingOfIntegersCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PackingSeparation_count
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RingOfIntegersCovering_cover_OE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_iota_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField InfinitePlace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : IntegerApproximationCount (E := E) := by
  intro r X
  refine ⟨fun w' => ?_, fun R hR => PackingSeparation.count R hR⟩
  classical
  have hconjmem : ∀ φ : E →+* ℂ, φ ∉ X.Ψ → ComplexEmbedding.conjugate φ ∈ X.Ψ := by
    intro φ h
    have := X.cmType (ComplexEmbedding.conjugate φ)
    rw [TraceIntegralBasis.conj_conj] at this
    exact this.mpr h
  let Z : TraceIntegralBasis.VS E := WithLp.toLp 2 (fun w : TraceIntegralBasis.CP E =>
    if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
    else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩))
  obtain ⟨α, hα⟩ := RingOfIntegersCovering.cover_OE Z
  refine ⟨α, fun τ => ?_⟩
  set w : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩ with hw
  have hcoord : ‖Z w - w.1.embedding (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have h := PiLp.norm_apply_le (Z - TraceIntegralBasis.iota E (α : E)) w
    rw [PiLp.sub_apply, TraceIntegralBasis.iota_apply] at h
    exact h.trans hα
  have hZw : Z w = if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
      else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩) := rfl
  have hmk : InfinitePlace.mk w.1.embedding = InfinitePlace.mk τ.1 := mk_embedding _
  rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
  · have hmem : w.1.embedding ∈ X.Ψ := h ▸ τ.2
    have hZ : Z w = w' τ := by
      rw [hZw, dif_pos hmem]
      congr 1
      exact Subtype.ext h
    rw [hZ, h] at hcoord
    rwa [norm_sub_rev] at hcoord
  · have hnot : w.1.embedding ∉ X.Ψ := by
      intro hm
      exact ((X.cmType _).mp hm) (h ▸ τ.2)
    have hZ : Z w = conj (w' τ) := by
      rw [hZw, dif_neg hnot]
      congr 2
      exact Subtype.ext h
    have hemb : w.1.embedding (α : E) = conj (τ.1 (α : E)) := by
      rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    rw [hZ, hemb, ← map_sub, Complex.norm_conj] at hcoord
    rwa [norm_sub_rev] at hcoord
end ReciprocityTheory.ChartRestriction.G.FD
