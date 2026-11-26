-- Prove2me | solution 1 for Stanley.alternating_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:52.185793+00:00
-- url     : https://prove2.me/submissions/7c22563a-9c35-4a1d-aaa2-9287782b0734

module
public import Definitions.Def_Stanley_Orientation
public import Definitions.Def_Stanley_SourceSum
public import Theorems.Thm_Stanley_count_allSources
public import Theorems.Thm_Stanley_alternating_sources

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution [Nonempty V] :
    ∑ s : Finset V, (if Independent G (s : Set V) then
      (-1 : ℤ) ^ s.card * orientationCount (G.induce (s : Set V)ᶜ) else 0) = 0 := by
  have h := alternating_sources G
  simp_rw [count_allSources, mul_ite, mul_zero] at h
  exact h
end Stanley
