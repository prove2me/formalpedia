-- Prove2me | solution 1 for SocialEquilibrium.Existence.exists_equilibrium_point
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T05:24:52.156951+00:00
-- url     : https://prove2.me/submissions/78120ad6-aaf6-4a06-98ec-6c5345bcbe27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
import Definitions.Def_SocialEquilibrium_Existence_IsContractible
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game
import Theorems.Thm_SocialEquilibrium_Existence_fixed_point_of_contractible_polyhedron
import Theorems.Thm_SocialEquilibrium_Existence_mem_bestResponse_iff
import Theorems.Thm_SocialEquilibrium_Existence_isClosed_graph_prod
import Theorems.Thm_SocialEquilibrium_Existence_isClosed_bestGraph
import Theorems.Thm_SocialEquilibrium_Existence_bestResponse_isContractible
import Theorems.Thm_SocialEquilibrium_Existence_pi_isPolyhedron_isContractible

set_option autoImplicit false

open unitInterval

/-- The profile space `∀ j, X j` is homeomorphic to the subset `Set.univ.pi X` of `∀ j, E j`. -/
def seq_profileHomeomorph {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    (X : ∀ i, Set (E i)) : (∀ j, X j) ≃ₜ (Set.univ.pi X : Set (∀ j, E j)) where
  toEquiv := (Equiv.Set.univPi X).symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val

/-- Contractibility (in Debreu's sense) transfers along a homeomorphism of the underlying
subspaces. -/
lemma seq_isContractible_of_homeomorph {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
    {S : Set Y} {T : Set Y'} (h : S ≃ₜ T)
    (hS : SocialEquilibrium.Existence.IsContractible S) :
    SocialEquilibrium.Existence.IsContractible T := by
  obtain ⟨z₀, H, h0, h1⟩ := hS
  refine ⟨h z₀, ?_⟩
  refine ⟨⟨fun p => h (H (p.1, h.symm p.2)), ?_⟩, ?_, ?_⟩
  · exact h.continuous.comp
      (H.continuous.comp (continuous_fst.prodMk (h.symm.continuous.comp continuous_snd)))
  · intro z
    simp [h0]
  · intro z
    simp [h1]

open SocialEquilibrium.Existence in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (hX : ∀ i, IsPolyhedron (X i) ∧ IsContractible (X i))
    (A : ∀ i : ι, Others X i → Set (X i))
    (hA : ∀ i (ā : Others X i), (A i ā).Nonempty)
    (hG : ∀ i, IsClosed (graph (A i)))
    (f : ι → (∀ j, X j) → EReal)
    (hf : ∀ i, ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hφ : ∀ i, Continuous (bestValue X A f i))
    (hM : ∀ i (ā : Others X i), IsContractible (bestSet X A f i ā)) :
    ∃ a : ∀ j, X j, IsEquilibrium X A f a := by
  -- the polyhedron `Z = ∏ X i` inside the finite-dimensional normed space `∀ j, E j`
  set Z : Set (∀ j, E j) := Set.univ.pi X with hZdef
  let e : (∀ j, X j) ≃ₜ Z := seq_profileHomeomorph X
  obtain ⟨hZp, hZc⟩ := pi_isPolyhedron_isContractible X hX
  -- the best-response correspondence transported to `Z`
  let φ : Z → Set Z := fun z => {w | e.symm w ∈ bestResponse X A f (e.symm z)}
  -- closed graph: the graph of `bestResponse` is closed, and `e × e` is a homeomorphism
  have hBR : IsClosed (graph (bestResponse X A f)) := by
    have h := isClosed_graph_prod X (fun i => graph (bestSet X A f i))
      (fun i => isClosed_bestGraph X A f i (hG i) (hf i) (hφ i))
    exact h
  have hφG : IsSemicontinuous φ := by
    have hpre : graph φ = (fun p : Z × Z => (e.symm p.1, e.symm p.2)) ⁻¹' graph (bestResponse X A f) := by
      ext p
      rfl
    unfold IsSemicontinuous
    rw [hpre]
    exact hBR.preimage ((e.symm.continuous.comp continuous_fst).prodMk
      (e.symm.continuous.comp continuous_snd))
  -- contractible values
  have hφc : ∀ z, IsContractible (φ z) := by
    intro z
    have hc := bestResponse_isContractible X A f hM (e.symm z)
    refine seq_isContractible_of_homeomorph ?_ hc
    exact (e.image (bestResponse X A f (e.symm z))).trans
      (Homeomorph.setCongr (by
        ext w
        simp only [Set.mem_image, Set.mem_setOf_eq, φ]
        constructor
        · rintro ⟨a, ha, rfl⟩
          simpa using ha
        · intro hw
          exact ⟨e.symm w, hw, by simp⟩))
  -- the fixed point of Debreu's lemma is an equilibrium point
  obtain ⟨z, hz⟩ := fixed_point_of_contractible_polyhedron Z hZp hZc φ hφG hφc
  exact ⟨e.symm z, (mem_bestResponse_iff X A f (e.symm z)).1 hz⟩
