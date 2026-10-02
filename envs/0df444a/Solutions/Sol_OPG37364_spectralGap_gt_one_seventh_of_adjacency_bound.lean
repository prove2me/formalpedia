-- Prove2me | solution 1 for OPG37364.spectralGap_gt_one_seventh_of_adjacency_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T10:52:45.530018+00:00
-- url     : https://prove2.me/submissions/fb966d35-3180-4a11-ac59-73bf7e37a185

import Definitions.Def_opg37364_matching_cuts
import Definitions.Def_mm_spectral
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Order.ConditionallyCompleteLattice.Finset

set_option autoImplicit false

open scoped Classical

namespace OPG37364.Stage3Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma degree_fourteen (G : SimpleGraph V) (hreg : OPG37364.IsRegularOfDegree G 14)
    (v : V) : G.degree v = 14 := by
  have h := hreg v
  rw [Set.encard_eq_coe_toFinset_card] at h
  exact_mod_cast h

omit [DecidableEq V] in
lemma graphWalk_eq_smul_adjMatrix (G : SimpleGraph V)
    (hreg : OPG37364.IsRegularOfDegree G 14) :
    MarkovMixing.graphWalk G = ((1 : ℝ) / 14) • G.adjMatrix ℝ := by
  ext x y
  simp [MarkovMixing.graphWalk, SimpleGraph.adjMatrix,
    degree_fourteen G hreg, Matrix.smul_apply, smul_eq_mul]

omit [DecidableEq V] in
lemma adjMatrix_eq_smul_graphWalk (G : SimpleGraph V)
    (hreg : OPG37364.IsRegularOfDegree G 14) :
    G.adjMatrix ℝ = (14 : ℝ) • MarkovMixing.graphWalk G := by
  rw [graphWalk_eq_smul_adjMatrix G hreg, smul_smul]
  norm_num

lemma isEigenvalue_iff_mem_spectrum (P : Matrix V V ℝ) (r : ℝ) :
    MarkovMixing.IsEigenvalue P r ↔ r ∈ spectrum ℝ P := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · rintro ⟨f, hf, heq⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := f)
    exact ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using heq), hf⟩
  · intro h
    obtain ⟨f, hf, hne⟩ := h.exists_hasEigenvector
    exact ⟨f, hne, by simpa using Module.End.mem_eigenspace_iff.mp hf⟩

omit [DecidableEq V] in
lemma graphWalk_isHermitian (G : SimpleGraph V)
    (hreg : OPG37364.IsRegularOfDegree G 14) :
    (MarkovMixing.graphWalk G).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  rw [graphWalk_eq_smul_adjMatrix G hreg]
  exact (G.isSymm_adjMatrix).smul _

lemma nontrivial_eigenvalues_nonempty [Nonempty V] (G : SimpleGraph V)
    (hreg : OPG37364.IsRegularOfDegree G 14) :
    {r : ℝ | MarkovMixing.IsEigenvalue (MarkovMixing.graphWalk G) r ∧ r ≠ 1}.Nonempty := by
  let P := MarkovMixing.graphWalk G
  have hP : P.IsHermitian := graphWalk_isHermitian G hreg
  have hne : P - 1 ≠ 0 := by
    intro h
    have heq : P = 1 := sub_eq_zero.mp h
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv := congrArg (fun M : Matrix V V ℝ => M v v) heq
    simp [P, MarkovMixing.graphWalk] at hv
  obtain ⟨f, t, ht, hf, heq⟩ :=
    (hP.sub Matrix.isHermitian_one).exists_eigenvector_of_ne_zero hne
  refine ⟨t + 1, ⟨f, hf, ?_⟩, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec] at heq
    rw [add_smul, one_smul]
    exact sub_eq_iff_eq_add.mp heq
  · exact fun h => ht (by linarith)

lemma nontrivial_eigenvalues_finite (P : Matrix V V ℝ) :
    {r : ℝ | MarkovMixing.IsEigenvalue P r ∧ r ≠ 1}.Finite := by
  apply (Matrix.finite_real_spectrum (A := P)).subset
  intro r hr
  exact (isEigenvalue_iff_mem_spectrum P r).mp hr.1

lemma scaled_eigenvalue_mem_adjacency_spectrum (G : SimpleGraph V)
    (hreg : OPG37364.IsRegularOfDegree G 14) {r : ℝ}
    (hr : MarkovMixing.IsEigenvalue (MarkovMixing.graphWalk G) r) :
    14 * r ∈ spectrum ℝ (G.adjMatrix ℝ) := by
  apply (isEigenvalue_iff_mem_spectrum _ _).mp
  obtain ⟨f, hf, heq⟩ := hr
  refine ⟨f, hf, ?_⟩
  rw [adjMatrix_eq_smul_graphWalk G hreg, Matrix.smul_mulVec, heq, smul_smul]

end OPG37364.Stage3Internal

open OPG37364

/-- A one-sided adjacency-spectrum bound suffices for the ordinary walk gap.
The excluded eigenvalue is the value 14, with no ordered-eigenvalue convention. -/
theorem solution
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hconn : IsConnected G) (hreg : IsRegularOfDegree G 14)
    (hAdj : ∀ μ : ℝ, μ ∈ spectrum ℝ (G.adjMatrix ℝ) → μ ≠ 14 → μ < 12) :
    (1 : ℝ) / 7 < MarkovMixing.spectralGap (MarkovMixing.graphWalk G) := by
  have : Nonempty (Fin n) := hconn.1
  have hfinite := Stage3Internal.nontrivial_eigenvalues_finite (MarkovMixing.graphWalk G)
  have hnonempty := Stage3Internal.nontrivial_eigenvalues_nonempty G hreg
  have hbounded : BddAbove
      {r : ℝ | MarkovMixing.IsEigenvalue (MarkovMixing.graphWalk G) r ∧ r ≠ 1} :=
    hfinite.bddAbove
  have hsup : MarkovMixing.lambdaTwo (MarkovMixing.graphWalk G) < (6 : ℝ) / 7 := by
    apply (hfinite.csSup_lt_iff hnonempty).mpr
    intro r hr
    have hμ := Stage3Internal.scaled_eigenvalue_mem_adjacency_spectrum G hreg hr.1
    have hne : 14 * r ≠ 14 := fun h => hr.2 (by linarith)
    have hlt := hAdj (14 * r) hμ hne
    linarith
  unfold MarkovMixing.spectralGap
  linarith

