-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:50.063816+00:00
-- url     : https://prove2.me/submissions/667d85d3-9c48-4275-ae4c-fb70bf85021c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
private lemma finsupp_apply_le_degree (α : ι →₀ ℕ) (i : ι) : α i ≤ α.degree := by
  unfold Finsupp.degree
  by_cases h : i ∈ α.support
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) h
  · have h0 : α i = 0 := by simpa [Finsupp.mem_support_iff] using h
    rw [h0]
    exact Nat.zero_le _
private lemma mem_paS' {c : ℕ} {α : ι →₀ ℕ} : α ∈ paS (ι := ι) c ↔ α.degree ≤ c := by
  simp only [paS, Finset.mem_filter, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨⟨α, fun i => ?_, ?_⟩, h⟩
    · have := finsupp_apply_le_degree α i
      omega
    · simp
end
end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution {c d : ℕ} (h : c ≤ d) : paPoly (ι := ι) c ≤ paPoly d := by
  unfold paPoly
  apply Submodule.span_mono
  apply Set.image_mono
  intro γ hγ
  exact mem_paS'.mpr (le_trans (mem_paS'.mp hγ) (by exact_mod_cast h))
end ReciprocityTheory.ChartRestriction.G.I2.FPw
