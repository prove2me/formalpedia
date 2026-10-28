-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P35.roof_graph_fiber
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:10:42.511008+00:00
-- url     : https://prove2.me/submissions/cc273e30-547e-43f2-b465-be8bea9542a1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

-- ===== P35R =====

noncomputable section

namespace X4PR
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P35

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- the hull fiber over `r` is exactly the set of roof values. -/
lemma fiber_eq (V : Set E) (f : E → ℝ) (r : E) :
    {a : ℝ | (r, a) ∈ convexHull ℝ (graphOn V f)} = roofValues V f r := by
  ext a
  constructor
  · intro h
    obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 h
    have hx : ∀ i, ∃ x ∈ V, (x, f x) = z i := fun i => hz i
    choose x hxV hxz using hx
    set e := Fintype.equivFin ι
    have hpos : 0 < Fintype.card ι := by
      rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
      · exfalso
        have : IsEmpty ι := Fintype.card_eq_zero_iff.1 h0
        rw [Finset.univ_eq_empty, Finset.sum_empty] at hw1
        exact zero_ne_one hw1
      · exact h0
    have hs1 : ∑ j : Fin (Fintype.card ι), w (e.symm j) = 1 := by
      rw [← hw1]; exact Equiv.sum_comp e.symm w
    have hsum' : ∑ i, w i • z i = (r, a) := hsum
    have hfst : ∑ i, w i • x i = r := by
      have := congrArg Prod.fst hsum'
      rw [Prod.fst_sum] at this
      simpa [← hxz] using this
    have hsnd : ∑ i, w i * f (x i) = a := by
      have := congrArg Prod.snd hsum'
      rw [Prod.snd_sum] at this
      simpa [← hxz] using this
    refine ⟨⟨Fintype.card ι, hpos, fun j => x (e.symm j), fun j => hxV _, fun j => w (e.symm j),
      fun j => hw0 _, hs1, ?_⟩, ?_⟩
    · rw [← hfst]; exact Equiv.sum_comp e.symm (fun i => w i • x i)
    · rw [← hsnd]; exact (Equiv.sum_comp e.symm (fun i => w i * f (x i))).symm
  · rintro ⟨d, rfl⟩
    have : (r, ∑ j, d.weight j * f (d.point j)) = ∑ j, d.weight j • (d.point j, f (d.point j)) := by
      ext
      · simp [Prod.fst_sum, d.barycenter]
      · simp [Prod.snd_sum]
    show (r, ∑ j, d.weight j * f (d.point j)) ∈ convexHull ℝ (graphOn V f)
    rw [this]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => d.nonnegative j) d.total
      (fun j _ => subset_convexHull ℝ _ ⟨d.point j, d.member j, rfl⟩)

end X4PR

-- ===== P35RSol =====

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

theorem _root_.solution {n : ℕ} (V : Set (Fin n → ℝ))
    (hV : IsNonsingularVariety V) (hcompact : IsCompact V) (hne : V.Nonempty)
    (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f V)
    (r : Fin n → ℝ) (hr : r ∈ convexHull ℝ V) :
    lowerRoof V f r = sInf {a : ℝ | (r, a) ∈ convexHull ℝ (graphOn V f)} ∧
    upperRoof V f r = sSup {a : ℝ | (r, a) ∈ convexHull ℝ (graphOn V f)} := by
  rw [X4PR.fiber_eq]
  exact ⟨rfl, rfl⟩

end QAlgorithms.Papers.Independent.Support50.P35

end

#print axioms solution
