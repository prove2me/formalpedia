-- Prove2me | solution 1 for WeldedPath.completion_gram_conditioning
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-18T02:34:51.756912+00:00
-- url     : https://prove2.me/submissions/c2da2c61-e985-49ee-8ebd-70ac43d86333

import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtModules
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Powerset
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.PiLex
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauVectors
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_WeldedPath_exactCpO
import Definitions.Def_WeldedPath_cpO
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_WeldedPath_InjDb
import Definitions.Def_WeldedPath_Supplement_exactCpWT
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Trace
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

set_option autoImplicit false

-- Solutions.SpechtRowRestriction
section

namespace WeldedPath.SpechtPieri

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open scoped BigOperators

def cellInclusion {ν μ : YoungDiagram} (h : ν ≤ μ) : ν.cells ↪ μ.cells where
  toFun x := ⟨x.1, h x.2⟩
  inj' _ _ he := Subtype.ext (congrArg (fun y : μ.cells => y.1) he)

def rowMatch {ν μ : YoungDiagram} (h : ν ≤ μ) (r : Tabloid ν) (s : Tabloid μ) : Prop :=
  ∀ x : ν.cells, s.1 (cellInclusion h x) = r.1 x

def rowRestriction {ν μ : YoungDiagram} (h : ν ≤ μ) :
    EuclideanSpace ℂ (Tabloid μ) →ₗ[ℂ] EuclideanSpace ℂ (Tabloid ν) where
  toFun f := WithLp.toLp 2 (fun r => ∑ s : Tabloid μ, if rowMatch h r s then f s else 0)
  map_add' f g := by
    ext r
    simp only [PiLp.toLp_apply, PiLp.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  map_smul' a f := by
    ext r
    simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp

@[simp] lemma rowRestriction_apply {ν μ : YoungDiagram} (h : ν ≤ μ)
    (f : EuclideanSpace ℂ (Tabloid μ)) (r : Tabloid ν) :
    rowRestriction h f r = ∑ s : Tabloid μ, if rowMatch h r s then f s else 0 := rfl

lemma rowMatch_relabel {ν μ : YoungDiagram} (h : ν ≤ μ)
    (g : Equiv.Perm μ.cells) (k : Equiv.Perm ν.cells)
    (hg : ∀ x, g (cellInclusion h x) = cellInclusion h (k x))
    (r : Tabloid ν) (s : Tabloid μ) :
    rowMatch h r (relabel μ g s) ↔ rowMatch h (relabel ν k⁻¹ r) s := by
  have hinv (x : ν.cells) : g⁻¹ (cellInclusion h (k x)) = cellInclusion h x := by
    rw [← hg]
    exact g.symm_apply_apply _
  have hinv' (x : ν.cells) : g⁻¹ (cellInclusion h x) = cellInclusion h (k⁻¹ x) := by
    simpa using hinv (k⁻¹ x)
  constructor
  · intro H x
    have hx := H (k x)
    change s.1 (g⁻¹ (cellInclusion h (k x))) = r.1 (k x) at hx
    rw [hinv] at hx
    simpa only [relabel_apply, inv_inv] using hx
  · intro H x
    have hx := H (k⁻¹ x)
    change s.1 (cellInclusion h (k⁻¹ x)) = r.1 ((k⁻¹)⁻¹ (k⁻¹ x)) at hx
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at hx
    change s.1 (g⁻¹ (cellInclusion h x)) = r.1 x
    rw [hinv']
    exact hx

theorem rowRestriction_equivariant {ν μ : YoungDiagram} (h : ν ≤ μ)
    (g : Equiv.Perm μ.cells) (k : Equiv.Perm ν.cells)
    (hg : ∀ x, g (cellInclusion h x) = cellInclusion h (k x))
    (f : EuclideanSpace ℂ (Tabloid μ)) :
    rowRestriction h (tabloidRep μ g f) = tabloidRep ν k (rowRestriction h f) := by
  ext r
  simp only [rowRestriction_apply, tabloidRep_apply]
  apply Fintype.sum_equiv (relabelEquiv μ g⁻¹)
  intro s
  have hm := rowMatch_relabel h g k hg r (relabel μ g⁻¹ s)
  rw [← relabel_mul, mul_inv_cancel, relabel_one] at hm
  change (if rowMatch h r s then f (relabel μ g⁻¹ s) else 0) =
    if rowMatch h (relabel ν k⁻¹ r) (relabel μ g⁻¹ s) then f (relabel μ g⁻¹ s) else 0
  rw [hm]

lemma rowRestriction_delta {ν μ : YoungDiagram} (h : ν ≤ μ)
    (s : Tabloid μ) (r : Tabloid ν) :
    rowRestriction h (delta μ s) r = if rowMatch h r s then 1 else 0 := by
  rw [rowRestriction_apply]
  change (∑ q : Tabloid μ, if rowMatch h r q then (if q = s then 1 else 0) else 0) = _
  rw [Finset.sum_eq_single s]
  · simp
  · intro q _ hq
    rw [if_neg hq]
    split_ifs <;> rfl
  · simp

abbrev HorizontalStrip (ν μ : YoungDiagram) : Prop :=
  ν ≤ μ ∧ ∀ x ∈ μ, x ∉ ν → ∀ y ∈ μ, y ∉ ν → x.2 = y.2 → x = y

lemma column_fixed_of_rowMatch {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    (c : columnGroup μ) (hm : rowMatch hs.1 (canonical ν) (relabel μ c.1 (canonical μ))) :
    c = 1 := by
  have hfix (x : ν.cells) : c.1⁻¹ (cellInclusion hs.1 x) = cellInclusion hs.1 x := by
    apply Subtype.ext
    apply Prod.ext
    · exact hm x
    · have hc := c.2 (c.1⁻¹ (cellInclusion hs.1 x))
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply, OAI.PartialPermutation.YoungTabloid.col] using hc.symm
  have hall (y : μ.cells) : c.1⁻¹ y = y := by
    by_cases hy : y.1 ∈ ν
    · exact hfix ⟨y.1,hy⟩
    · have hy' : (c.1⁻¹ y).1 ∉ ν := by
        intro hh
        have he := hfix ⟨(c.1⁻¹ y).1,hh⟩
        have he' : c.1⁻¹ (c.1⁻¹ y) = c.1⁻¹ y := he
        exact hy (by
          have he'' : c.1⁻¹ y = y := c.1.symm.injective he'
          simpa only [he''] using hh)
      apply Subtype.ext
      apply hs.2 (c.1⁻¹ y).1 (c.1⁻¹ y).2 hy' y.1 y.2 hy
      have hc := c.2 (c.1⁻¹ y)
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply, OAI.PartialPermutation.YoungTabloid.col] using hc.symm
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  exact hall

lemma rowMatch_column_iff {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    (c : columnGroup μ) :
    rowMatch hs.1 (canonical ν) (relabel μ c.1 (canonical μ)) ↔ c = 1 := by
  constructor
  · exact column_fixed_of_rowMatch hs c
  · rintro rfl
    intro x
    rfl

theorem strip_coefficient {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    rowRestriction hs.1 (polytabloid μ) (canonical ν) = 1 := by
  unfold polytabloid antisym
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  have hdelta (c : columnGroup μ) :
      tabloidRep μ c.1 (delta μ (canonical μ)) = delta μ (relabel μ c.1 (canonical μ)) := by
    ext r
    simp only [tabloidRep_apply, delta, PiLp.toLp_apply]
    have he : relabel μ c.1⁻¹ r = canonical μ ↔ r = relabel μ c.1 (canonical μ) := by
      constructor
      · intro h
        have := congrArg (relabel μ c.1) h
        simpa only [← relabel_mul, mul_inv_cancel, relabel_one] using this
      · rintro rfl
        rw [← relabel_mul, inv_mul_cancel, relabel_one]
    rw [he]
  simp_rw [hdelta, rowRestriction_delta, rowMatch_column_iff hs]
  simp

end
end WeldedPath.SpechtPieri

end

-- Solutions.YoungTableauBranching
section
-- Reuses the accepted Prove2Me tableau-branching proof, submission 98ed0bff-c8c5-4666-a3bb-c19bb25f88ed.
-- Its six elementary definitions below have exactly the published P31/P26 bodies.

namespace WeldedPath.YoungCounts

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Cell := ℕ × ℕ
abbrev Filling (n : ℕ) := Fin n → ℕ × ℕ

def IsTableau {n : ℕ} (nu : YoungDiagram) (t : Filling n) : Prop :=
  Function.Injective t ∧ Finset.univ.image t = nu.cells ∧
    (∀ i j, (t i).1 = (t j).1 → (t i).2 < (t j).2 → i < j) ∧
    (∀ i j, (t i).2 = (t j).2 → (t i).1 < (t j).1 → i < j)

def corners (lam : YoungDiagram) : Finset Cell :=
  lam.cells.filter fun z => (z.1 + 1, z.2) ∉ lam ∧ (z.1, z.2 + 1) ∉ lam

def oneBoxPredecessors (lam : YoungDiagram) : Finset YoungDiagram :=
  ((lam.cells.powerset.filter fun a : Finset Cell => a.card + 1 = lam.card ∧
    IsLowerSet (a : Set Cell)).attach).image fun a =>
      (⟨a.val, (Finset.mem_filter.mp a.property).2.2⟩ : YoungDiagram)

def tableauCount (lam : YoungDiagram) : ℕ :=
  Fintype.card {t : Fin lam.card → {z : Cell // z ∈ lam.cells} //
    IsTableau lam (fun i => (t i).val)}

theorem g61a_corner_mem {lam : YoungDiagram} {c : ℕ × ℕ} (hc : c ∈ corners lam) : c ∈ lam.cells :=
  (Finset.mem_filter.mp hc).1

theorem g61a_corner_row {lam : YoungDiagram} {c z : ℕ × ℕ} (hc : c ∈ corners lam)
    (hz : z ∈ lam.cells) (h1 : c.1 ≤ z.1) (h2 : c.2 < z.2) : False := by
  have h := (Finset.mem_filter.mp hc).2.2
  apply h
  rw [YoungDiagram.mem_cells] at hz
  refine lam.up_left_mem (i2 := z.1) (j2 := z.2) h1 ?_ (by simpa using hz)
  omega

theorem g61a_corner_col {lam : YoungDiagram} {c z : ℕ × ℕ} (hc : c ∈ corners lam)
    (hz : z ∈ lam.cells) (h1 : c.1 < z.1) (h2 : c.2 ≤ z.2) : False := by
  have h := (Finset.mem_filter.mp hc).2.1
  apply h
  rw [YoungDiagram.mem_cells] at hz
  refine lam.up_left_mem (i2 := z.1) (j2 := z.2) ?_ h2 (by simpa using hz)
  omega

/-- Removing a corner. -/
def g61a_er (lam : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ corners lam) : YoungDiagram :=
  ⟨lam.cells.erase c, by
    intro b a hab hb
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hb ⊢
    refine ⟨lam.isLowerSet hab hb.1, fun hac => ?_⟩
    subst hac
    have hne := hb.2
    obtain ⟨h1, h2⟩ := hab
    by_cases h : a.1 < b.1
    · exact g61a_corner_col hc hb.1 h h2
    · have e1 : a.1 = b.1 := by omega
      have : a.2 < b.2 := by
        rcases Nat.lt_or_eq_of_le h2 with h' | h'
        · exact h'
        · exact absurd (Prod.ext e1 h').symm hne
      exact g61a_corner_row hc hb.1 (by omega) this⟩

theorem g61a_er_cells (lam : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ corners lam) :
    (g61a_er lam c hc).cells = lam.cells.erase c := rfl

theorem g61a_fwd (lam : YoungDiagram) (n : ℕ) (c : ℕ × ℕ) (hc : c ∈ corners lam)
    (t : Fin (n + 1) → ℕ × ℕ) (ht : IsTableau lam t) (hl : t (Fin.last n) = c) :
    IsTableau (g61a_er lam c hc) (Fin.init t) := by
  obtain ⟨hinj, him, hr, hcl⟩ := ht
  refine ⟨fun a b h => Fin.castSucc_injective _ (hinj h), ?_, ?_, ?_⟩
  · ext z
    rw [g61a_er_cells, Finset.mem_erase, ← him]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.init]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨fun h => ?_, a.castSucc, rfl⟩
      rw [← hl] at h
      exact (Fin.castSucc_lt_last a).ne (hinj h)
    · rintro ⟨hne, i, rfl⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact ⟨j, rfl⟩
      · exact absurd hl hne
  · intro i j h1 h2; exact Fin.castSucc_lt_castSucc_iff.mp (hr _ _ h1 h2)
  · intro i j h1 h2; exact Fin.castSucc_lt_castSucc_iff.mp (hcl _ _ h1 h2)

theorem g61a_bwd (lam : YoungDiagram) (n : ℕ) (c : ℕ × ℕ) (hc : c ∈ corners lam)
    (s : Fin n → ℕ × ℕ) (hs : IsTableau (g61a_er lam c hc) s) :
    IsTableau lam (Fin.snoc (α := fun _ => ℕ × ℕ) s c) := by
  obtain ⟨hinj, him, hr, hcl⟩ := hs
  have hsmem : ∀ a, s a ∈ lam.cells.erase c := fun a => by
    rw [← g61a_er_cells lam c hc, ← him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hsne : ∀ a, s a ≠ c := fun a => (Finset.mem_erase.mp (hsmem a)).1
  have hsin : ∀ a, s a ∈ lam.cells := fun a => (Finset.mem_erase.mp (hsmem a)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl <;>
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
    · rw [hinj h]
    · exact absurd h (hsne a)
    · exact absurd h.symm (hsne b)
    · rfl
  · ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.exists_fin_succ',
      Fin.snoc_castSucc, Fin.snoc_last]
    constructor
    · rintro (⟨a, rfl⟩ | rfl)
      · exact hsin a
      · exact g61a_corner_mem hc
    · intro hz
      by_cases hzc : z = c
      · exact Or.inr hzc.symm
      · left
        have : z ∈ (g61a_er lam c hc).cells := by
          rw [g61a_er_cells]; exact Finset.mem_erase.mpr ⟨hzc, hz⟩
        rw [← him] at this
        simpa using this
  · intro i j h1 h2
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at h1 h2
    · exact Fin.castSucc_lt_castSucc_iff.mpr (hr i j h1 h2)
    · exact Fin.castSucc_lt_last i
    · exact (g61a_corner_row hc (hsin j) h1.le h2).elim
    · exact absurd h2 (lt_irrefl _)
  · intro i j h1 h2
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at h1 h2
    · exact Fin.castSucc_lt_castSucc_iff.mpr (hcl i j h1 h2)
    · exact Fin.castSucc_lt_last i
    · exact (g61a_corner_col hc (hsin j) h2 h1.le).elim
    · exact absurd h2 (lt_irrefl _)

def g61a_T (mu : YoungDiagram) (n : ℕ) : ℕ :=
  Fintype.card {t : Fin n → {z : ℕ × ℕ // z ∈ mu.cells} // IsTableau mu (fun i => (t i).val)}

theorem g61a_count (mu : YoungDiagram) (n : ℕ) (h : mu.card = n) :
    tableauCount mu = g61a_T mu n := by
  subst h; rfl

theorem g61a_fiber (lam : YoungDiagram) (n : ℕ) (c : ℕ × ℕ) (hc : c ∈ corners lam) :
    ((Finset.univ : Finset (Fin (n + 1) → {z : ℕ × ℕ // z ∈ lam.cells})).filter
      (fun t => IsTableau lam (fun i => (t i).val) ∧ (t (Fin.last n)).val = c)).card =
    g61a_T (g61a_er lam c hc) n := by
  unfold g61a_T
  rw [Fintype.card_subtype]
  refine Finset.card_bij' (fun t ht => fun j => ⟨(t j.castSucc).val, ?_⟩)
    (fun s hs => fun k => ⟨Fin.snoc (α := fun _ => ℕ × ℕ) (fun i => (s i).val) c k, ?_⟩)
    ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hf := g61a_fwd lam n c hc _ ht.1 ht.2
    rw [← hf.2.1]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hb := g61a_bwd lam n c hc _ hs
    rw [← hb.2.1]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact g61a_fwd lam n c hc _ ht.1 ht.2
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨g61a_bwd lam n c hc _ hs, by simp⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    funext k
    apply Subtype.ext
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
    · simp
    · simp [ht.2]
  · intro s hs
    funext k
    apply Subtype.ext
    simp

theorem g61a_last_corner (lam : YoungDiagram) (n : ℕ) (t : Fin (n + 1) → ℕ × ℕ)
    (ht : IsTableau lam t) : t (Fin.last n) ∈ corners lam := by
  obtain ⟨hinj, him, hr, hcl⟩ := ht
  have hmem : ∀ z, z ∈ lam.cells → ∃ i, t i = z := fun z hz => by
    rw [← him] at hz; simpa using hz
  unfold corners
  rw [Finset.mem_filter]
  refine ⟨by rw [← him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_, ?_⟩
  · intro h
    obtain ⟨i, hi⟩ := hmem _ (by simpa using h)
    have := hcl (Fin.last n) i (by rw [hi]) (by rw [hi]; simp)
    exact absurd (Fin.le_last i) (not_le.mpr this)
  · intro h
    obtain ⟨i, hi⟩ := hmem _ (by simpa using h)
    have := hr (Fin.last n) i (by rw [hi]) (by rw [hi]; simp)
    exact absurd (Fin.le_last i) (not_le.mpr this)

theorem g61a_split (lam : YoungDiagram) (n : ℕ) :
    g61a_T lam (n + 1) = ∑ x ∈ (corners lam).attach, g61a_T (g61a_er lam x.1 x.2) n := by
  unfold g61a_T
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t => (t (Fin.last n)).val) (t := corners lam)
    (fun t ht => g61a_last_corner lam n _ (Finset.mem_filter.mp ht).2)]
  rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.filter_filter]
  exact g61a_fiber lam n x.1 x.2

theorem g61a_obp (lam : YoungDiagram) :
    ∑ x ∈ (corners lam).attach, tableauCount (g61a_er lam x.1 x.2) =
      ∑ mu ∈ oneBoxPredecessors lam, tableauCount mu := by
  refine Finset.sum_bij (fun x _ => g61a_er lam x.1 x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x _
    unfold oneBoxPredecessors
    rw [Finset.mem_image]
    refine ⟨⟨lam.cells.erase x.1, ?_⟩, Finset.mem_attach _ _, rfl⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.erase_subset _ _, ?_, (g61a_er lam x.1 x.2).isLowerSet⟩
    exact Finset.card_erase_add_one (g61a_corner_mem x.2)
  · intro x _ y _ hxy
    have h := congrArg YoungDiagram.cells hxy
    rw [g61a_er_cells, g61a_er_cells] at h
    apply Subtype.ext
    by_contra hne
    have : y.1 ∈ lam.cells.erase x.1 := Finset.mem_erase.mpr ⟨Ne.symm hne, g61a_corner_mem y.2⟩
    rw [h] at this
    simp at this
  · intro mu hmu
    unfold oneBoxPredecessors at hmu
    rw [Finset.mem_image] at hmu
    obtain ⟨⟨a, ha⟩, _, rfl⟩ := hmu
    rw [Finset.mem_filter, Finset.mem_powerset] at ha
    obtain ⟨hsub, hcard, hlow⟩ := ha
    have hsd : (lam.cells \ a).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub]; simp only [YoungDiagram.card] at hcard; omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hsd
    have hcmem : c ∈ lam.cells \ a := by rw [hc]; simp
    rw [Finset.mem_sdiff] at hcmem
    have key : ∀ z ∈ lam.cells, z ∉ a → z = c := fun z hz hza => by
      have : z ∈ lam.cells \ a := Finset.mem_sdiff.mpr ⟨hz, hza⟩
      rw [hc] at this; simpa using this
    have hcor : c ∈ corners lam := by
      unfold corners
      rw [Finset.mem_filter]
      refine ⟨hcmem.1, fun h => ?_, fun h => ?_⟩
      · rw [← YoungDiagram.mem_cells] at h
        by_cases hza : (c.1 + 1, c.2) ∈ a
        · exact hcmem.2 (hlow (show c ≤ (c.1 + 1, c.2) from ⟨by simp, le_refl _⟩) hza)
        · have := key _ h hza
          have := congrArg Prod.fst this; simp at this
      · rw [← YoungDiagram.mem_cells] at h
        by_cases hza : (c.1, c.2 + 1) ∈ a
        · exact hcmem.2 (hlow (show c ≤ (c.1, c.2 + 1) from ⟨le_refl _, by simp⟩) hza)
        · have := key _ h hza
          have := congrArg Prod.snd this; simp at this
    refine ⟨⟨c, hcor⟩, Finset.mem_attach _ _, ?_⟩
    apply YoungDiagram.ext
    rw [g61a_er_cells]
    ext z
    rw [Finset.mem_erase]
    constructor
    · rintro ⟨hzc, hz⟩
      by_contra hza
      exact hzc (key z hz hza)
    · intro hza
      refine ⟨fun h => hcmem.2 ?_, hsub hza⟩
      rw [h] at hza; exact hza

theorem tableauBranching (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    tableauCount lam = ∑ mu ∈ oneBoxPredecessors lam, tableauCount mu := by
  obtain ⟨n, hn⟩ : ∃ n, lam.card = n + 1 := ⟨lam.card - 1, by
    have := hne.card_pos; simp only [YoungDiagram.card]; omega⟩
  rw [g61a_count lam (n + 1) hn, g61a_split, ← g61a_obp]
  refine Finset.sum_congr rfl fun x _ => (g61a_count _ n ?_).symm
  simp only [YoungDiagram.card, g61a_er_cells]
  rw [Finset.card_erase_of_mem (g61a_corner_mem x.2)]
  simp only [YoungDiagram.card] at hn; omega

end

end WeldedPath.YoungCounts

end

-- Solutions.YoungLattice
section

namespace WeldedPath.YoungCounts

noncomputable section
open Classical
open scoped BigOperators

def Covers (lam μ : YoungDiagram) : Prop := lam ≤ μ ∧ lam.card + 1 = μ.card

lemma mem_predecessors {lam μ : YoungDiagram} :
    lam ∈ oneBoxPredecessors μ ↔ Covers lam μ := by
  constructor
  · rintro h
    obtain ⟨⟨a, ha⟩, _, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hs, hc, _⟩ := Finset.mem_filter.mp ha
    exact ⟨Finset.mem_powerset.mp hs, hc⟩
  · rintro ⟨hs, hc⟩
    exact Finset.mem_image.mpr ⟨⟨lam.cells,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs, hc, lam.isLowerSet⟩⟩,
      Finset.mem_attach _ _, by cases lam; rfl⟩

lemma corner_iff {lam : YoungDiagram} {c : Cell} :
    c ∈ corners lam ↔ c.2 + 1 = lam.rowLen c.1 ∧ lam.rowLen (c.1 + 1) ≤ c.2 := by
  rcases c with ⟨i, j⟩
  simp only [corners, Finset.mem_filter, YoungDiagram.mem_cells,
    YoungDiagram.mem_iff_lt_rowLen, not_lt]
  omega

lemma corner_eq_of_row_eq {lam : YoungDiagram} {c d : Cell}
    (hc : c ∈ corners lam) (hd : d ∈ corners lam) (h : c.1 = d.1) : c = d := by
  apply Prod.ext h
  have hc' := (corner_iff.mp hc).1
  have hd' := (corner_iff.mp hd).1
  rw [h] at hc'
  omega

def addRow (lam : YoungDiagram) (i : ℕ)
    (hi : i = 0 ∨ lam.rowLen i < lam.rowLen (i - 1)) : YoungDiagram :=
  ⟨insert (i, lam.rowLen i) lam.cells, by
    intro b a hab hb
    change a ∈ insert (i, lam.rowLen i) lam.cells
    rcases Finset.mem_insert.mp hb with rfl | hb
    · by_cases hr : a.1 = i
      · by_cases hc : a.2 = lam.rowLen i
        · exact Finset.mem_insert.mpr (Or.inl (Prod.ext hr hc))
        · apply Finset.mem_insert_of_mem
          rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, hr]
          have := hab.2
          omega
      · apply Finset.mem_insert_of_mem
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
        have hri : a.1 ≤ i - 1 := by have := hab.1; omega
        have hpos : 0 < i := by have := hab.1; omega
        have hdrop : lam.rowLen i < lam.rowLen (i - 1) := hi.resolve_left (by omega)
        have hanti := lam.rowLen_anti a.1 (i - 1) hri
        have := hab.2
        omega
    · exact Finset.mem_insert_of_mem (lam.isLowerSet hab hb)⟩

lemma covers_addRow (lam : YoungDiagram) (i : ℕ)
    (hi : i = 0 ∨ lam.rowLen i < lam.rowLen (i - 1)) : Covers lam (addRow lam i hi) := by
  refine ⟨Finset.subset_insert _ _, ?_⟩
  change lam.card + 1 = (insert (i, lam.rowLen i) lam.cells).card
  rw [Finset.card_insert_of_notMem]
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, lt_self_iff_false,
    not_false_eq_true]

def extension (lam : YoungDiagram) : Option {c // c ∈ corners lam} → YoungDiagram
  | none => addRow lam 0 (Or.inl rfl)
  | some c => addRow lam (c.1.1 + 1) (Or.inr (by
      have hc := corner_iff.mp c.2
      simp only [Nat.add_sub_cancel]
      omega))

lemma extension_covers (lam : YoungDiagram) (a : Option {c // c ∈ corners lam}) :
    Covers lam (extension lam a) := by
  cases a with
  | none => exact covers_addRow lam 0 (Or.inl rfl)
  | some c =>
      exact covers_addRow lam (c.1.1 + 1) (Or.inr (by
        have hc := corner_iff.mp c.2
        simp only [Nat.add_sub_cancel]
        omega))

lemma addRow_injective (lam : YoungDiagram) (i j : ℕ)
    (hi : i = 0 ∨ lam.rowLen i < lam.rowLen (i - 1))
    (hj : j = 0 ∨ lam.rowLen j < lam.rowLen (j - 1))
    (h : addRow lam i hi = addRow lam j hj) : i = j := by
  have hc := congrArg YoungDiagram.cells h
  change insert (i, lam.rowLen i) lam.cells = insert (j, lam.rowLen j) lam.cells at hc
  have hm : (i, lam.rowLen i) ∈ insert (j, lam.rowLen j) lam.cells := by
    rw [← hc]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hm with he | he
  · exact congrArg Prod.fst he
  · exact (lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp he)).elim

lemma extension_injective (lam : YoungDiagram) : Function.Injective (extension lam) := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b =>
          simp only [extension] at h
          have := addRow_injective lam _ _ _ _ h
          omega
  | some a =>
      cases b with
      | none =>
          simp only [extension] at h
          have := addRow_injective lam _ _ _ _ h
          omega
      | some b =>
          simp only [extension] at h
          congr 1
          apply Subtype.ext
          apply corner_eq_of_row_eq a.2 b.2
          have := addRow_injective lam _ _ _ _ h
          omega

lemma covers_insert {lam μ : YoungDiagram} (h : Covers lam μ) :
    ∃ c, c ∉ lam.cells ∧ μ.cells = insert c lam.cells := by
  have hd : (μ.cells \ lam.cells).card = 1 := by
    rw [Finset.card_sdiff_of_subset h.1]
    have hcard : lam.cells.card + 1 = μ.cells.card := h.2
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hd
  have hm : c ∈ μ.cells \ lam.cells := by rw [hc]; simp
  refine ⟨c, (Finset.mem_sdiff.mp hm).2, ?_⟩
  rw [← Finset.sdiff_union_of_subset h.1, hc]
  simp

lemma covers_addRow_eq {lam μ : YoungDiagram} (h : Covers lam μ) :
    ∃ i hi, μ = addRow lam i hi := by
  obtain ⟨c, hc, he⟩ := covers_insert h
  have hrow : c.2 = lam.rowLen c.1 := by
    have hlo : lam.rowLen c.1 ≤ c.2 := by
      exact not_lt.mp (fun hlt => hc (YoungDiagram.mem_iff_lt_rowLen.mpr hlt))
    by_contra hn
    have hm : (c.1, lam.rowLen c.1) ∈ μ :=
      μ.up_left_mem le_rfl hlo (by change c ∈ μ.cells; rw [he]; simp)
    change (c.1, lam.rowLen c.1) ∈ μ.cells at hm
    rw [he, Finset.mem_insert] at hm
    rcases hm with hm | hm
    · have := congrArg Prod.snd hm; omega
    · exact (lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)).elim
  have hi : c.1 = 0 ∨ lam.rowLen c.1 < lam.rowLen (c.1 - 1) := by
    by_cases hz : c.1 = 0
    · exact Or.inl hz
    right
    have hm : (c.1 - 1, c.2) ∈ μ :=
      μ.up_left_mem (Nat.sub_le _ _) le_rfl (by change c ∈ μ.cells; rw [he]; simp)
    change (c.1 - 1, c.2) ∈ μ.cells at hm
    rw [he, Finset.mem_insert] at hm
    rcases hm with hm | hm
    · have := congrArg Prod.fst hm; omega
    · simpa only [hrow] using YoungDiagram.mem_iff_lt_rowLen.mp hm
  refine ⟨c.1, hi, ?_⟩
  apply YoungDiagram.ext
  change μ.cells = insert (c.1, lam.rowLen c.1) lam.cells
  rw [he, ← hrow]

lemma extension_surjective (lam : YoungDiagram) (μ : YoungDiagram) (h : Covers lam μ) :
    ∃ a, extension lam a = μ := by
  obtain ⟨i, hi, rfl⟩ := covers_addRow_eq h
  rcases i with _ | i
  · exact ⟨none, rfl⟩
  · have hd : lam.rowLen (i + 1) < lam.rowLen i := by
      simpa using hi.resolve_left (by omega)
    have hc : (i, lam.rowLen i - 1) ∈ corners lam := by
      rw [corner_iff]
      simp only [Prod.fst, Prod.snd]
      omega
    exact ⟨some ⟨(i, lam.rowLen i - 1), hc⟩, rfl⟩

def extensionEquiv (lam : YoungDiagram) :
    Option {c // c ∈ corners lam} ≃ {μ // Covers lam μ} :=
  Equiv.ofBijective (fun a => ⟨extension lam a, extension_covers lam a⟩)
    ⟨fun a b h => extension_injective lam (congrArg Subtype.val h), by
      rintro ⟨μ, hμ⟩
      obtain ⟨a, ha⟩ := extension_surjective lam μ hμ
      exact ⟨a, Subtype.ext ha⟩⟩

theorem predecessor_sum (lam : YoungDiagram) (f : YoungDiagram → ℕ) :
    ∑ x ∈ (corners lam).attach, f (g61a_er lam x.1 x.2) =
      ∑ mu ∈ oneBoxPredecessors lam, f mu := by
  refine Finset.sum_bij (fun x _ => g61a_er lam x.1 x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x _
    unfold oneBoxPredecessors
    rw [Finset.mem_image]
    refine ⟨⟨lam.cells.erase x.1, ?_⟩, Finset.mem_attach _ _, rfl⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.erase_subset _ _, ?_, (g61a_er lam x.1 x.2).isLowerSet⟩
    exact Finset.card_erase_add_one (g61a_corner_mem x.2)
  · intro x _ y _ hxy
    have h := congrArg YoungDiagram.cells hxy
    rw [g61a_er_cells, g61a_er_cells] at h
    apply Subtype.ext
    by_contra hne
    have : y.1 ∈ lam.cells.erase x.1 := Finset.mem_erase.mpr ⟨Ne.symm hne, g61a_corner_mem y.2⟩
    rw [h] at this
    simp at this
  · intro mu hmu
    unfold oneBoxPredecessors at hmu
    rw [Finset.mem_image] at hmu
    obtain ⟨⟨a, ha⟩, _, rfl⟩ := hmu
    rw [Finset.mem_filter, Finset.mem_powerset] at ha
    obtain ⟨hsub, hcard, hlow⟩ := ha
    have hsd : (lam.cells \ a).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub]; simp only [YoungDiagram.card] at hcard; omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hsd
    have hcmem : c ∈ lam.cells \ a := by rw [hc]; simp
    rw [Finset.mem_sdiff] at hcmem
    have key : ∀ z ∈ lam.cells, z ∉ a → z = c := fun z hz hza => by
      have : z ∈ lam.cells \ a := Finset.mem_sdiff.mpr ⟨hz, hza⟩
      rw [hc] at this; simpa using this
    have hcor : c ∈ corners lam := by
      unfold corners
      rw [Finset.mem_filter]
      refine ⟨hcmem.1, fun h => ?_, fun h => ?_⟩
      · rw [← YoungDiagram.mem_cells] at h
        by_cases hza : (c.1 + 1, c.2) ∈ a
        · exact hcmem.2 (hlow (show c ≤ (c.1 + 1, c.2) from ⟨by simp, le_refl _⟩) hza)
        · have := key _ h hza
          have := congrArg Prod.fst this; simp at this
      · rw [← YoungDiagram.mem_cells] at h
        by_cases hza : (c.1, c.2 + 1) ∈ a
        · exact hcmem.2 (hlow (show c ≤ (c.1, c.2 + 1) from ⟨le_refl _, by simp⟩) hza)
        · have := key _ h hza
          have := congrArg Prod.snd this; simp at this
    refine ⟨⟨c, hcor⟩, Finset.mem_attach _ _, ?_⟩
    apply YoungDiagram.ext
    rw [g61a_er_cells]
    ext z
    rw [Finset.mem_erase]
    constructor
    · rintro ⟨hzc, hz⟩
      by_contra hza
      exact hzc (key z hz hza)
    · intro hza
      refine ⟨fun h => hcmem.2 ?_, hsub hza⟩
      rw [h] at hza; exact hza

def oneBoxSuccessors (lam : YoungDiagram) : Finset YoungDiagram :=
  Finset.univ.image (extension lam)

lemma mem_successors {lam μ : YoungDiagram} :
    μ ∈ oneBoxSuccessors lam ↔ Covers lam μ := by
  constructor
  · rintro h
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
    exact extension_covers lam a
  · intro h
    obtain ⟨a, rfl⟩ := extension_surjective lam μ h
    exact Finset.mem_image_of_mem _ (Finset.mem_univ a)

lemma predecessors_card (lam : YoungDiagram) :
    (oneBoxPredecessors lam).card = (corners lam).card := by
  simpa using (predecessor_sum lam (fun _ => 1)).symm

lemma successors_card (lam : YoungDiagram) :
    (oneBoxSuccessors lam).card = (corners lam).card + 1 := by
  rw [oneBoxSuccessors, Finset.card_image_of_injective _ (extension_injective lam)]
  simp

lemma successors_card_eq_predecessors_card_add_one (lam : YoungDiagram) :
    (oneBoxSuccessors lam).card = (oneBoxPredecessors lam).card + 1 := by
  rw [successors_card, predecessors_card]

end
end WeldedPath.YoungCounts

end

-- Solutions.SpechtPieri
section

namespace WeldedPath.SpechtPieri

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open scoped BigOperators

lemma column_extend {ν μ : YoungDiagram} (h : ν ≤ μ) (c : columnGroup ν) :
    c.1.viaEmbedding (cellInclusion h) ∈ columnGroup μ := by
  intro x
  by_cases hx : x ∈ Set.range (cellInclusion h)
  · obtain ⟨y,rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply]
    exact c.2 y
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]

lemma signC_extend {ν μ : YoungDiagram} (h : ν ≤ μ) (c : Equiv.Perm ν.cells) :
    signC (c.viaEmbedding (cellInclusion h)) = signC c := by
  simp [signC, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]

lemma column_polytabloid (μ : YoungDiagram) (c : columnGroup μ) :
    tabloidRep μ c.1 (polytabloid μ) = signC c.1 • polytabloid μ := by
  ext r
  change polytabloid μ (relabel μ c.1⁻¹ r) = signC c.1 * polytabloid μ r
  have h := polytabloid_alternating μ c⁻¹ r
  simpa only [Subgroup.coe_inv, signC_inv] using h

lemma restricted_polytabloid_column {ν μ : YoungDiagram} (h : ν ≤ μ) (c : columnGroup ν) :
    tabloidRep ν c.1 (rowRestriction h (polytabloid μ)) =
      signC c.1 • rowRestriction h (polytabloid μ) := by
  rw [← rowRestriction_equivariant h (c.1.viaEmbedding (cellInclusion h)) c.1
    (Equiv.Perm.viaEmbedding_apply _ _)]
  rw [column_polytabloid μ ⟨_, column_extend h c⟩, map_smul, signC_extend]

lemma strip_pairing {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    inner ℂ (polytabloid ν) (rowRestriction hs.1 (polytabloid μ)) =
      (Fintype.card (columnGroup ν) : ℂ) := by
  let x := rowRestriction hs.1 (polytabloid μ)
  have ha : antisym ν x = (Fintype.card (columnGroup ν) : ℂ) • x := by
    dsimp [x]
    unfold antisym
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, restricted_polytabloid_column,
      smul_smul, signC_sq, one_smul, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  rw [antisym_eq_inner] at ha
  have he := congrArg (fun f : EuclideanSpace ℂ (Tabloid ν) => f (canonical ν)) ha
  simpa only [PiLp.smul_apply, smul_eq_mul, polytabloid_canonical, x,
    strip_coefficient hs, mul_one] using he

lemma specht_map_eq (μ : YoungDiagram) (g : Equiv.Perm μ.cells) :
    (spechtSub μ).toSubmodule.map (tabloidRep μ g) = (spechtSub μ).toSubmodule := by
  apply le_antisymm
  · rintro v ⟨u,hu,rfl⟩
    exact (spechtSub μ).apply_mem_toSubmodule g hu
  · intro v hv
    refine ⟨tabloidRep μ g⁻¹ v, (spechtSub μ).apply_mem_toSubmodule g⁻¹ hv, ?_⟩
    simp

lemma spechtProjection_equivariant (μ : YoungDiagram) (g : Equiv.Perm μ.cells)
    (f : EuclideanSpace ℂ (Tabloid μ)) :
    (spechtSub μ).toSubmodule.orthogonalProjectionOnto (tabloidRep μ g f) =
      spechtRep μ g ((spechtSub μ).toSubmodule.orthogonalProjectionOnto f) := by
  apply Subtype.ext
  change (spechtSub μ).toSubmodule.starProjection (tabloidRep μ g f) =
    tabloidRep μ g ((spechtSub μ).toSubmodule.starProjection f)
  let U := (tabloidRep μ g).isometryOfInner (tabloidRep_unitary μ g)
  have h := U.map_starProjection (spechtSub μ).toSubmodule f
  change tabloidRep μ g ((spechtSub μ).toSubmodule.starProjection f) =
    ((spechtSub μ).toSubmodule.map (tabloidRep μ g)).starProjection (tabloidRep μ g f) at h
  have hp := congrArg (fun P : Submodule ℂ (EuclideanSpace ℂ (Tabloid μ)) => P.starProjection)
    (specht_map_eq μ g)
  have he := congrArg (fun A : EuclideanSpace ℂ (Tabloid μ) →L[ℂ]
      EuclideanSpace ℂ (Tabloid μ) => A (tabloidRep μ g f)) hp
  exact he.symm.trans h.symm

def restrictionMap {ν μ : YoungDiagram} (h : ν ≤ μ) :
    (spechtSub μ).toSubmodule →ₗ[ℂ] (spechtSub ν).toSubmodule :=
  (spechtSub ν).toSubmodule.orthogonalProjectionOnto.toLinearMap.comp
    ((rowRestriction h).comp (spechtSub μ).toSubmodule.subtype)

theorem restrictionMap_equivariant {ν μ : YoungDiagram} (h : ν ≤ μ)
    (g : Equiv.Perm μ.cells) (k : Equiv.Perm ν.cells)
    (hg : ∀ x, g (cellInclusion h x) = cellInclusion h (k x))
    (f : (spechtSub μ).toSubmodule) :
    restrictionMap h (spechtRep μ g f) = spechtRep ν k (restrictionMap h f) := by
  change (spechtSub ν).toSubmodule.orthogonalProjectionOnto
      (rowRestriction h (tabloidRep μ g f.1)) =
    spechtRep ν k ((spechtSub ν).toSubmodule.orthogonalProjectionOnto (rowRestriction h f.1))
  rw [rowRestriction_equivariant h g k hg, spechtProjection_equivariant]

theorem restrictionMap_ne_zero {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    restrictionMap hs.1 ≠ 0 := by
  intro hz
  have he : (spechtSub ν).toSubmodule.orthogonalProjectionOnto
      (rowRestriction hs.1 (polytabloid μ)) = 0 :=
    congrArg (fun F => F (⟨polytabloid μ, polytabloid_mem_specht μ⟩ :
      (spechtSub μ).toSubmodule)) hz
  have hp := (spechtSub ν).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (⟨polytabloid ν, polytabloid_mem_specht ν⟩ : (spechtSub ν).toSubmodule)
    (rowRestriction hs.1 (polytabloid μ))
  rw [he, inner_zero_right, strip_pairing hs] at hp
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero :
    (Fintype.card (columnGroup ν) : ℂ) ≠ 0) hp.symm

theorem restrictionMap_surjective {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    Function.Surjective (restrictionMap hs.1) := by
  let F : Representation.IntertwiningMap
      ((spechtRep μ).comp (Equiv.Perm.viaEmbeddingHom (cellInclusion hs.1))) (spechtRep ν) :=
    { toLinearMap := restrictionMap hs.1
      isIntertwining' := by
        intro k
        apply LinearMap.ext
        intro f
        exact restrictionMap_equivariant hs.1 _ k (Equiv.Perm.viaEmbedding_apply _ _) f }
  rcases Representation.IsIrreducible.surjective_or_eq_zero F with h | h
  · exact h
  · exact (restrictionMap_ne_zero hs (congrArg Representation.IntertwiningMap.toLinearMap h)).elim

lemma horizontalStrip_of_covers {ν μ : YoungDiagram} (h : YoungCounts.Covers ν μ) :
    HorizontalStrip ν μ := by
  obtain ⟨c, hc, hcells⟩ := YoungCounts.covers_insert h
  refine ⟨h.1, ?_⟩
  intro x hx hxn y hy hyn _
  have hx' : x ∈ insert c ν.cells := by rw [← hcells]; exact hx
  have hy' : y ∈ insert c ν.cells := by rw [← hcells]; exact hy
  have hxc : x = c := (Finset.mem_insert.mp hx').resolve_right hxn
  have hyc : y = c := (Finset.mem_insert.mp hy').resolve_right hyn
  exact hxc.trans hyc.symm

theorem oneBox_restriction_surjective {ν μ : YoungDiagram} (h : YoungCounts.Covers ν μ) :
    Function.Surjective (restrictionMap h.1) :=
  restrictionMap_surjective (horizontalStrip_of_covers h)

end
end WeldedPath.SpechtPieri

end

-- Solutions.YoungBranchingMaps
section

namespace WeldedPath.YoungBranching

noncomputable section
open Classical YoungCounts SpechtPieri OAI.PartialPermutation
  OAI.PartialPermutation.YoungTabloid OAI.PartialPermutation.DiagramCounting

def extraCell {ν μ : YoungDiagram} (h : Covers ν μ) : μ.cells :=
  ⟨(covers_insert h).choose, by
    exact Eq.mpr (congrArg (fun s : Finset (ℕ × ℕ) => (covers_insert h).choose ∈ s)
      (covers_insert h).choose_spec.2) (Finset.mem_insert_self _ _)⟩

lemma extraCell_not_mem {ν μ : YoungDiagram} (h : Covers ν μ) : (extraCell h).1 ∉ ν :=
  (covers_insert h).choose_spec.1

lemma eq_extraCell_of_not_mem {ν μ : YoungDiagram} (h : Covers ν μ)
    (y : μ.cells) (hy : y.1 ∉ ν) : y = extraCell h := by
  apply Subtype.ext
  have hm : y.1 ∈ insert (covers_insert h).choose ν.cells :=
    (covers_insert h).choose_spec.2 ▸ y.2
  exact (Finset.mem_insert.mp hm).resolve_right hy

def adjoinTableau {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1)) (h : Covers ν.1 μ.1) :
    Fin (n+1) ≃ μ.1.cells :=
  Equiv.ofBijective
    (Fin.snoc (fun i : Fin n => cellInclusion h.1 ((SpechtActual.labels ν).symm i)) (extraCell h))
    ⟨Fin.snoc_injective_of_injective
      ((cellInclusion h.1).injective.comp (SpechtActual.labels ν).symm.injective) (by
        rintro ⟨i,hi⟩
        have he := congrArg (fun x : μ.1.cells => x.1) hi
        exact extraCell_not_mem h (he ▸ ((SpechtActual.labels ν).symm i).2)), by
      intro y
      by_cases hy : y.1 ∈ ν.1
      · refine ⟨((SpechtActual.labels ν) ⟨y.1,hy⟩).castSucc, ?_⟩
        rw [Fin.snoc_castSucc, Equiv.symm_apply_apply]
        rfl
      · exact ⟨Fin.last n, (Fin.snoc_last _ _).trans (eq_extraCell_of_not_mem h y hy).symm⟩⟩

@[simp] lemma adjoinTableau_castSucc {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1))
    (h : Covers ν.1 μ.1) (i : Fin n) :
    adjoinTableau ν μ h i.castSucc = cellInclusion h.1 ((SpechtActual.labels ν).symm i) := by
  change Fin.snoc (α := fun _ : Fin (n+1) => μ.1.cells)
    (fun j : Fin n => cellInclusion h.1 ((SpechtActual.labels ν).symm j))
    (extraCell h) i.castSucc = _
  exact Fin.snoc_castSucc _ _ _

@[simp] lemma adjoinTableau_last {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1))
    (h : Covers ν.1 μ.1) : adjoinTableau ν μ h (Fin.last n) = extraCell h := by
  change Fin.snoc (α := fun _ : Fin (n+1) => μ.1.cells)
    (fun j : Fin n => cellInclusion h.1 ((SpechtActual.labels ν).symm j))
    (extraCell h) (Fin.last n) = _
  exact Fin.snoc_last _ _

def relabelForBranch {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1))
    (h : Covers ν.1 μ.1) : Equiv.Perm μ.1.cells :=
  (SpechtActual.labels μ).trans (adjoinTableau ν μ h)

def restrictedRep {n : ℕ} (μ : DiagramCounting.Shape (n+1)) :=
  (SpechtActual.rep μ).comp (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin n ↪ Fin (n+1)))

lemma branch_conjugacy {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1))
    (h : Covers ν.1 μ.1) (g : Equiv.Perm (Fin n)) :
    relabelForBranch ν μ h *
      (SpechtActual.labels μ).symm.permCongrHom (g.viaEmbedding Fin.castSuccEmb) =
    (adjoinTableau ν μ h).permCongrHom (g.viaEmbedding Fin.castSuccEmb) *
      relabelForBranch ν μ h := by
  apply Equiv.ext
  intro x
  simp [relabelForBranch, Equiv.Perm.mul_apply, Equiv.permCongrHom_coe, Equiv.permCongr_apply]

lemma branch_inclusion {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1))
    (h : Covers ν.1 μ.1) (g : Equiv.Perm (Fin n)) (x : ν.1.cells) :
    (adjoinTableau ν μ h).permCongrHom (g.viaEmbedding Fin.castSuccEmb) (cellInclusion h.1 x) =
      cellInclusion h.1 ((SpechtActual.labels ν).symm.permCongrHom g x) := by
  have he : cellInclusion h.1 x = adjoinTableau ν μ h ((SpechtActual.labels ν x).castSucc) := by
    rw [adjoinTableau_castSucc, Equiv.symm_apply_apply]
  rw [he]
  change adjoinTableau ν μ h
      ((g.viaEmbedding Fin.castSuccEmb) ((adjoinTableau ν μ h).symm
        (adjoinTableau ν μ h (SpechtActual.labels ν x).castSucc))) = _
  rw [Equiv.symm_apply_apply]
  exact (congrArg (adjoinTableau ν μ h)
    (Equiv.Perm.viaEmbedding_apply g Fin.castSuccEmb (SpechtActual.labels ν x))).trans
      (adjoinTableau_castSucc ν μ h (g (SpechtActual.labels ν x)))

def branchMap {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1)) (h : Covers ν.1 μ.1) :
    Representation.IntertwiningMap (restrictedRep μ) (SpechtActual.rep ν) where
  toLinearMap := (restrictionMap h.1).comp (spechtRep μ.1 (relabelForBranch ν μ h))
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro f
    change restrictionMap h.1 (spechtRep μ.1 (relabelForBranch ν μ h)
        (spechtRep μ.1 ((SpechtActual.labels μ).symm.permCongrHom
          (g.viaEmbedding Fin.castSuccEmb)) f)) =
      spechtRep ν.1 ((SpechtActual.labels ν).symm.permCongrHom g)
        (restrictionMap h.1 (spechtRep μ.1 (relabelForBranch ν μ h) f))
    rw [← Module.End.mul_apply, ← map_mul, branch_conjugacy, map_mul, Module.End.mul_apply]
    exact restrictionMap_equivariant h.1 _ _ (branch_inclusion ν μ h g) _

theorem branchMap_surjective {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1))
    (h : Covers ν.1 μ.1) : Function.Surjective (branchMap ν μ h) := by
  intro w
  obtain ⟨v,hv⟩ := oneBox_restriction_surjective h w
  refine ⟨spechtRep μ.1 (relabelForBranch ν μ h)⁻¹ v, ?_⟩
  change restrictionMap h.1 (spechtRep μ.1 (relabelForBranch ν μ h)
    (spechtRep μ.1 (relabelForBranch ν μ h)⁻¹ v)) = w
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  exact hv

theorem branchMap_ne_zero {n : ℕ} (ν : DiagramCounting.Shape n) (μ : DiagramCounting.Shape (n+1))
    (h : Covers ν.1 μ.1) : branchMap ν μ h ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := branchMap_surjective ν μ h ⟨polytabloid ν.1, polytabloid_mem_specht ν.1⟩
  rw [hz] at hv
  exact polytabloid_ne_zero ν.1 (congrArg Subtype.val hv).symm

end
end WeldedPath.YoungBranching

end

-- Solutions.YoungDifferential
section

namespace WeldedPath.YoungCounts

noncomputable section
open Classical
open scoped BigOperators

lemma diagram_card_mono {lam μ : YoungDiagram} (h : lam ≤ μ) : lam.card ≤ μ.card :=
  Finset.card_le_card h

lemma diagram_eq_of_le_card {lam μ : YoungDiagram} (h : lam ≤ μ)
    (hc : lam.card = μ.card) : lam = μ :=
  YoungDiagram.ext (Finset.eq_of_subset_of_card_le h hc.ge)

lemma sup_card_strict {lam μ : YoungDiagram} (hc : lam.card = μ.card) (hne : lam ≠ μ) :
    lam.card < (lam ⊔ μ).card := by
  apply Finset.card_lt_card
  change lam < lam ⊔ μ
  apply lt_of_le_of_ne le_sup_left
  intro he
  have hm : μ ≤ lam := by rw [he]; exact le_sup_right
  exact hne (diagram_eq_of_le_card hm hc.symm).symm

lemma sup_card_add_inf_card (lam μ : YoungDiagram) :
    (lam ⊔ μ).card + (lam ⊓ μ).card = lam.card + μ.card :=
  Finset.card_union_add_card_inter _ _

lemma common_successor_data {lam μ ν : YoungDiagram} (hc : lam.card = μ.card)
    (hne : lam ≠ μ) (hl : Covers lam ν) (hm : Covers μ ν) :
    ν = lam ⊔ μ ∧ Covers (lam ⊓ μ) lam ∧ Covers (lam ⊓ μ) μ := by
  have hs : lam ⊔ μ ≤ ν := sup_le hl.1 hm.1
  have hlo := sup_card_strict hc hne
  have hhi := diagram_card_mono hs
  have he : (lam ⊔ μ).card = ν.card := by have := hl.2; omega
  have hi := sup_card_add_inf_card lam μ
  refine ⟨(diagram_eq_of_le_card hs he).symm, ⟨inf_le_left, ?_⟩, ⟨inf_le_right, ?_⟩⟩ <;>
    have hcard := hl.2 <;> omega

lemma common_predecessor_data {lam μ ρ : YoungDiagram} (hc : lam.card = μ.card)
    (hne : lam ≠ μ) (hl : Covers ρ lam) (hm : Covers ρ μ) :
    ρ = lam ⊓ μ ∧ Covers lam (lam ⊔ μ) ∧ Covers μ (lam ⊔ μ) := by
  have hs : ρ ≤ lam ⊓ μ := le_inf hl.1 hm.1
  have hlo := sup_card_strict hc hne
  have hhi := diagram_card_mono hs
  have hi := sup_card_add_inf_card lam μ
  have he : ρ.card = (lam ⊓ μ).card := by have := hl.2; omega
  refine ⟨diagram_eq_of_le_card hs he, ⟨le_sup_left, ?_⟩, ⟨le_sup_right, ?_⟩⟩ <;>
    have hcard := hl.2 <;> omega

def commonSuccessors (lam μ : YoungDiagram) : Finset YoungDiagram :=
  (oneBoxSuccessors lam).filter fun ν => Covers μ ν

def commonPredecessors (lam μ : YoungDiagram) : Finset YoungDiagram :=
  (oneBoxPredecessors lam).filter fun ρ => Covers ρ μ

lemma mem_commonSuccessors {lam μ ν : YoungDiagram} :
    ν ∈ commonSuccessors lam μ ↔ Covers lam ν ∧ Covers μ ν := by
  simp only [commonSuccessors, Finset.mem_filter, mem_successors]

lemma mem_commonPredecessors {lam μ ρ : YoungDiagram} :
    ρ ∈ commonPredecessors lam μ ↔ Covers ρ lam ∧ Covers ρ μ := by
  simp only [commonPredecessors, Finset.mem_filter, mem_predecessors]

lemma common_card_of_ne {lam μ : YoungDiagram} (hc : lam.card = μ.card) (hne : lam ≠ μ) :
    (commonSuccessors lam μ).card = (commonPredecessors lam μ).card := by
  apply Finset.card_bij (fun _ _ => lam ⊓ μ)
  · intro ν hν
    obtain ⟨hl, hm⟩ := mem_commonSuccessors.mp hν
    have hd := common_successor_data hc hne hl hm
    exact mem_commonPredecessors.mpr hd.2
  · intro ν hν ξ hξ _
    obtain ⟨hl, hm⟩ := mem_commonSuccessors.mp hν
    obtain ⟨hl', hm'⟩ := mem_commonSuccessors.mp hξ
    exact (common_successor_data hc hne hl hm).1.trans
      (common_successor_data hc hne hl' hm').1.symm
  · intro ρ hρ
    obtain ⟨hl, hm⟩ := mem_commonPredecessors.mp hρ
    have hd := common_predecessor_data hc hne hl hm
    exact ⟨lam ⊔ μ, mem_commonSuccessors.mpr hd.2, hd.1.symm⟩

theorem young_differential {lam μ : YoungDiagram} (hc : lam.card = μ.card) :
    (commonSuccessors lam μ).card = (commonPredecessors lam μ).card +
      if lam = μ then 1 else 0 := by
  by_cases he : lam = μ
  · subst μ
    have hs : commonSuccessors lam lam = oneBoxSuccessors lam := by
      ext ν
      simp only [mem_commonSuccessors, mem_successors, and_self]
    have hp : commonPredecessors lam lam = oneBoxPredecessors lam := by
      ext ν
      simp only [mem_commonPredecessors, mem_predecessors, and_self]
    rw [hs, hp, if_pos rfl]
    exact successors_card_eq_predecessors_card_add_one lam
  · rw [if_neg he, Nat.add_zero]
    exact common_card_of_ne hc he

end
end WeldedPath.YoungCounts

end

-- Solutions.YoungSquareSum
section

namespace WeldedPath.YoungCounts

noncomputable section
open Classical
open scoped BigOperators

lemma rectangle_card_le (μ : YoungDiagram) (i j : ℕ) (h : (i,j) ∈ μ) :
    (i+1)*(j+1) ≤ μ.cells.card := by
  have hs : (Finset.range (i+1)) ×ˢ (Finset.range (j+1)) ⊆ μ.cells := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hx,hy⟩
    exact μ.isLowerSet ⟨by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hx,
      by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hy⟩ h
  simpa only [Finset.card_product, Finset.card_range] using Finset.card_le_card hs

lemma cell_bounded (μ : YoungDiagram) (x : μ.cells) :
    x.1.1 < μ.cells.card ∧ x.1.2 < μ.cells.card := by
  have h := rectangle_card_le μ x.1.1 x.1.2 x.2
  constructor <;> nlinarith

abbrev Shape (n : ℕ) := {μ : YoungDiagram // μ.cells.card = n}

def shapeCode (n : ℕ) (μ : Shape n) :
    ((Finset.range n) ×ˢ (Finset.range n)).powerset := by
  refine ⟨μ.1.cells, Finset.mem_powerset.mpr ?_⟩
  intro x hx
  have hh := cell_bounded μ.1 ⟨x,hx⟩
  rw [μ.2] at hh
  simpa only [Finset.mem_product, Finset.mem_range] using hh

lemma shapeCode_injective (n : ℕ) : Function.Injective (shapeCode n) := by
  intro μ ν h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

instance (n : ℕ) : Fintype (Shape n) := Fintype.ofInjective (shapeCode n) (shapeCode_injective n)

def level (n : ℕ) : Finset YoungDiagram := Finset.univ.image (fun μ : Shape n => μ.1)

lemma mem_level {n : ℕ} {μ : YoungDiagram} : μ ∈ level n ↔ μ.card = n := by
  constructor
  · rintro h
    obtain ⟨μ, _, rfl⟩ := Finset.mem_image.mp h
    exact μ.2
  · intro h
    exact Finset.mem_image_of_mem _ (Finset.mem_univ (⟨μ,h⟩ : Shape n))

lemma predecessors_eq_filter (μ : YoungDiagram) (n : ℕ) (h : μ.card = n + 1) :
    oneBoxPredecessors μ = (level n).filter fun lam => Covers lam μ := by
  ext lam
  rw [mem_predecessors, Finset.mem_filter, mem_level]
  constructor
  · intro hl
    exact ⟨by have := hl.2; omega, hl⟩
  · exact And.right

lemma successors_eq_filter (lam : YoungDiagram) :
    oneBoxSuccessors lam = (level (lam.card + 1)).filter fun μ => Covers lam μ := by
  ext μ
  rw [mem_successors, Finset.mem_filter, mem_level]
  exact ⟨fun h => ⟨h.2.symm,h⟩, And.right⟩

lemma commonSuccessors_sum (lam : YoungDiagram) (f : YoungDiagram → ℕ) :
    (∑ ν ∈ oneBoxSuccessors lam, ∑ μ ∈ oneBoxPredecessors ν, f μ) =
      ∑ μ ∈ level lam.card, f μ * (commonSuccessors lam μ).card := by
  calc
    _ = ∑ ν ∈ oneBoxSuccessors lam, ∑ μ ∈ level lam.card,
        if Covers μ ν then f μ else 0 := by
      apply Finset.sum_congr rfl
      intro ν hν
      rw [predecessors_eq_filter ν lam.card (mem_successors.mp hν).2.symm,
        Finset.sum_filter]
    _ = ∑ μ ∈ level lam.card, ∑ ν ∈ oneBoxSuccessors lam,
        if Covers μ ν then f μ else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro μ _
      rw [← Finset.sum_filter]
      simp [commonSuccessors, mul_comm]

lemma commonPredecessors_sum (lam : YoungDiagram) (f : YoungDiagram → ℕ) :
    (∑ ν ∈ oneBoxPredecessors lam, ∑ μ ∈ oneBoxSuccessors ν, f μ) =
      ∑ μ ∈ level lam.card, f μ * (commonPredecessors lam μ).card := by
  calc
    _ = ∑ ν ∈ oneBoxPredecessors lam, ∑ μ ∈ level lam.card,
        if Covers ν μ then f μ else 0 := by
      apply Finset.sum_congr rfl
      intro ν hν
      rw [successors_eq_filter, (mem_predecessors.mp hν).2, Finset.sum_filter]
    _ = ∑ μ ∈ level lam.card, ∑ ν ∈ oneBoxPredecessors lam,
        if Covers ν μ then f μ else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro μ _
      rw [← Finset.sum_filter]
      simp [commonPredecessors, mul_comm]

lemma weighted_differential (lam : YoungDiagram) (f : YoungDiagram → ℕ) :
    (∑ ν ∈ oneBoxSuccessors lam, ∑ μ ∈ oneBoxPredecessors ν, f μ) =
      (∑ ν ∈ oneBoxPredecessors lam, ∑ μ ∈ oneBoxSuccessors ν, f μ) + f lam := by
  rw [commonSuccessors_sum, commonPredecessors_sum]
  calc
    _ = ∑ μ ∈ level lam.card,
        f μ * ((commonPredecessors lam μ).card + if lam = μ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [young_differential (mem_level.mp hμ).symm]
    _ = _ := by
      simp [mul_add, Finset.sum_add_distrib, mem_level]

lemma successor_tableau_sum (lam : YoungDiagram) :
    (∑ μ ∈ oneBoxSuccessors lam, tableauCount μ) = (lam.card + 1) * tableauCount lam := by
  have hmain : ∀ n, ∀ lam : YoungDiagram, lam.card = n →
      (∑ μ ∈ oneBoxSuccessors lam, tableauCount μ) = (n + 1) * tableauCount lam := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro lam hn
      have he : (∑ μ ∈ oneBoxSuccessors lam, tableauCount μ) =
          ∑ μ ∈ oneBoxSuccessors lam, ∑ ρ ∈ oneBoxPredecessors μ, tableauCount ρ := by
        apply Finset.sum_congr rfl
        intro μ hμ
        apply tableauBranching
        apply Finset.card_pos.mp
        have := (mem_successors.mp hμ).2
        change 0 < μ.card
        omega
      rw [he, weighted_differential]
      have hs : (∑ μ ∈ oneBoxPredecessors lam,
          ∑ ρ ∈ oneBoxSuccessors μ, tableauCount ρ) =
          n * ∑ μ ∈ oneBoxPredecessors lam, tableauCount μ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro μ hμ
        have hc := (mem_predecessors.mp hμ).2
        simpa only [hc, hn] using ih μ.card (by omega) μ rfl
      rw [hs]
      by_cases hz : n = 0
      · simp [hz]
      · have hp : lam.cells.Nonempty := Finset.card_pos.mp (by change 0 < lam.card; omega)
        rw [← tableauBranching lam hp]
        ring
  exact hmain lam.card lam rfl

lemma weighted_level_adjacency (n : ℕ) (f g : YoungDiagram → ℕ) :
    (∑ μ ∈ level (n + 1), g μ * ∑ lam ∈ oneBoxPredecessors μ, f lam) =
      ∑ lam ∈ level n, f lam * ∑ μ ∈ oneBoxSuccessors lam, g μ := by
  calc
    _ = ∑ μ ∈ level (n + 1), ∑ lam ∈ level n,
        if Covers lam μ then g μ * f lam else 0 := by
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [predecessors_eq_filter μ n (mem_level.mp hμ), Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro lam _
      split_ifs <;> simp
    _ = ∑ lam ∈ level n, ∑ μ ∈ level (n + 1),
        if Covers lam μ then g μ * f lam else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro lam hlam
      rw [successors_eq_filter, mem_level.mp hlam, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      split_ifs <;> simp [mul_comm]

lemma tableauCount_of_card_zero (lam : YoungDiagram) (hc : lam.card = 0) : tableauCount lam = 1 := by
  letI : IsEmpty (Fin lam.card) := ⟨fun i => by have := i.isLt; omega⟩
  have hcells : lam.cells = ∅ := Finset.card_eq_zero.mp hc
  let t : Fin lam.card → {c : Cell // c ∈ lam.cells} := fun i => isEmptyElim i
  have ht : IsTableau lam (fun i => (t i).val) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; exact isEmptyElim i
    · simp [hcells]
    · intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i
  letI : Unique {t : Fin lam.card → {c : Cell // c ∈ lam.cells} //
      IsTableau lam (fun i => (t i).val)} :=
    ⟨⟨⟨t,ht⟩⟩, fun x => Subtype.ext (funext fun i => isEmptyElim i)⟩
  exact Fintype.card_unique

lemma level_zero : level 0 = {⊥} := by
  ext lam
  rw [mem_level, Finset.mem_singleton]
  constructor
  · intro h
    apply YoungDiagram.ext
    exact Finset.card_eq_zero.mp h
  · rintro rfl
    rfl

theorem tableau_square_sum (n : ℕ) :
    (∑ lam ∈ level n, tableauCount lam ^ 2) = n.factorial := by
  induction n with
  | zero => simp [level_zero, tableauCount_of_card_zero (⊥ : YoungDiagram) rfl]
  | succ n ih =>
      calc
        _ = ∑ μ ∈ level (n + 1), tableauCount μ *
            ∑ lam ∈ oneBoxPredecessors μ, tableauCount lam := by
          apply Finset.sum_congr rfl
          intro μ hμ
          rw [← tableauBranching μ (Finset.card_pos.mp (by
            change 0 < μ.card
            rw [mem_level.mp hμ]
            omega))]
          ring
        _ = ∑ lam ∈ level n, tableauCount lam *
            ∑ μ ∈ oneBoxSuccessors lam, tableauCount μ := weighted_level_adjacency _ _ _
        _ = (n + 1) * ∑ lam ∈ level n, tableauCount lam ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro lam hlam
          rw [successor_tableau_sum, mem_level.mp hlam]
          ring
        _ = _ := by rw [ih, Nat.factorial_succ]

end
end WeldedPath.YoungCounts

end

-- Solutions.YoungStandardCounts
section

namespace WeldedPath.YoungCounts

noncomputable section
open Classical
open scoped BigOperators

abbrev TableauFilling (lam : YoungDiagram) :=
  {t : Fin lam.card → {z : Cell // z ∈ lam.cells} //
    IsTableau lam (fun i => (t i).val)}

def fillingEquiv (lam : YoungDiagram) (t : TableauFilling lam) : Fin lam.card ≃ lam.cells :=
  Equiv.ofBijective t.1 ⟨fun i j h => t.2.1 (congrArg Subtype.val h), by
    intro c
    have hc : c.1 ∈ Finset.univ.image (fun i => (t.1 i).val) := by rw [t.2.2.1]; exact c.2
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    exact ⟨i, Subtype.ext hi⟩⟩

lemma tableau_strictMono (lam : YoungDiagram) (e : Fin lam.card ≃ lam.cells)
    (ht : IsTableau lam (fun i => (e i).val)) : StrictMono e.symm := by
  have hrow (a b : lam.cells) (hr : a.1.1 = b.1.1) (hc : a.1.2 < b.1.2) :
      e.symm a < e.symm b := by
    apply ht.2.2.1
    · simpa only [Equiv.apply_symm_apply] using hr
    · simpa only [Equiv.apply_symm_apply] using hc
  have hcol (a b : lam.cells) (hc : a.1.2 = b.1.2) (hr : a.1.1 < b.1.1) :
      e.symm a < e.symm b := by
    apply ht.2.2.2
    · simpa only [Equiv.apply_symm_apply] using hc
    · simpa only [Equiv.apply_symm_apply] using hr
  intro a b hab
  by_cases hr : a.1.1 = b.1.1
  · apply hrow a b hr
    have hc := hab.le.2
    have hne : a.1.2 ≠ b.1.2 := fun he => hab.ne (Subtype.ext (Prod.ext hr he))
    omega
  · let c : lam.cells := ⟨(b.1.1, a.1.2), lam.up_left_mem le_rfl hab.le.2 b.2⟩
    have hac : e.symm a < e.symm c := hcol a c rfl (by
      change a.1.1 < b.1.1
      have := hab.le.1
      omega)
    have hcb : e.symm c ≤ e.symm b := by
      by_cases hc : a.1.2 = b.1.2
      · have he : c = b := Subtype.ext (Prod.ext rfl hc)
        rw [he]
      · exact (hrow c b rfl (by
          change a.1.2 < b.1.2
          have := hab.le.2
          omega)).le
    exact hac.trans_le hcb

lemma tableau_of_strictMono (lam : YoungDiagram) (e : Fin lam.card ≃ lam.cells)
    (he : StrictMono e.symm) : IsTableau lam (fun i => (e i).val) := by
  refine ⟨fun i j h => e.injective (Subtype.ext h), ?_, ?_, ?_⟩
  · ext c
    constructor
    · rintro h
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact (e i).2
    · intro hc
      exact Finset.mem_image.mpr ⟨e.symm ⟨c,hc⟩, Finset.mem_univ _, by simp⟩
  · intro i j hr hc
    have hlt : e i < e j := by
      refine lt_iff_le_not_ge.mpr ⟨⟨hr.le,hc.le⟩, ?_⟩
      intro hle
      exact not_le_of_gt hc hle.2
    simpa only [Equiv.symm_apply_apply] using he hlt
  · intro i j hc hr
    have hlt : e i < e j := by
      refine lt_iff_le_not_ge.mpr ⟨⟨hr.le,hc.le⟩, ?_⟩
      intro hle
      exact not_le_of_gt hr hle.1
    simpa only [Equiv.symm_apply_apply] using he hlt

def standardFillingEquiv (lam : YoungDiagram) : TableauFilling lam ≃
    {e : lam.cells ≃ Fin lam.card // StrictMono e} where
  toFun t := ⟨(fillingEquiv lam t).symm, tableau_strictMono lam (fillingEquiv lam t) t.2⟩
  invFun e := ⟨e.1.symm, tableau_of_strictMono lam e.1.symm e.2⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro c
    apply e.1.symm.injective
    change e.1.symm ((fillingEquiv lam _).symm c) = e.1.symm (e.1 c)
    rw [Equiv.symm_apply_apply]
    exact (fillingEquiv lam ⟨e.1.symm, tableau_of_strictMono lam e.1.symm e.2⟩).apply_symm_apply c

theorem tableauCount_eq_standardCount (lam : YoungDiagram) :
    tableauCount lam = OAI.PartialPermutation.Tableau.standardCount lam := by
  have hc : Fintype.card lam.cells = lam.card := Fintype.card_coe lam.cells
  let k := Fin.castOrderIso hc.symm
  let E : {e : lam.cells ≃ Fin lam.card // StrictMono e} ≃
      OAI.PartialPermutation.Tableau.StandardFilling lam.cells :=
    { toFun := fun e => ⟨e.1.trans k.toEquiv, k.strictMono.comp e.2⟩
      invFun := fun e => ⟨e.1.trans k.symm.toEquiv, k.symm.strictMono.comp e.2⟩
      left_inv := by
        intro e
        apply Subtype.ext
        apply Equiv.ext
        intro c
        exact k.symm_apply_apply (e.1 c)
      right_inv := by
        intro e
        apply Subtype.ext
        apply Equiv.ext
        intro c
        exact k.apply_symm_apply (e.1 c) }
  exact Fintype.card_congr ((standardFillingEquiv lam).trans E)

theorem standardCount_square_sum (n : ℕ) :
    (∑ lam : OAI.PartialPermutation.DiagramCounting.Shape n,
      OAI.PartialPermutation.Tableau.standardCount lam.1 ^ 2) = n.factorial := by
  rw [← tableau_square_sum n]
  simp_rw [← tableauCount_eq_standardCount]
  unfold level
  rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

end
end WeldedPath.YoungCounts

end

-- Solutions.YoungLeadingWord
section

namespace WeldedPath.YoungLeadingWord
open scoped BigOperators
open Classical
universe uI uX uK
variable {n : ℕ} {D : YoungDiagram}

def Standard (t : Fin n ≃ D.cells) : Prop := StrictMono t.symm

lemma standard_row_lt_iff (t : Fin n ≃ D.cells) (ht : Standard t) (x y : Fin n)
    (hr : (t x).val.1 = (t y).val.1) : x < y ↔ (t x).val.2 < (t y).val.2 := by
  constructor
  · intro hxy
    by_contra hn
    have hc : (t y).val.2 ≤ (t x).val.2 := Nat.le_of_not_gt hn
    have hyx : t y ≤ t x := ⟨by omega, hc⟩
    have hh : y ≤ x := by simpa only [Equiv.symm_apply_apply] using ht.monotone hyx
    exact not_le_of_gt hxy hh
  · intro hc
    have hxy : t x < t y := by
      refine lt_iff_le_not_ge.mpr ⟨⟨by omega, hc.le⟩, ?_⟩
      intro hh
      exact not_le_of_gt hc hh.2
    simpa only [Equiv.symm_apply_apply] using ht hxy

lemma standard_col_lt_iff (t : Fin n ≃ D.cells) (ht : Standard t) (x y : Fin n)
    (hc : (t x).val.2 = (t y).val.2) : x < y ↔ (t x).val.1 < (t y).val.1 := by
  constructor
  · intro hxy
    by_contra hn
    have hr : (t y).val.1 ≤ (t x).val.1 := Nat.le_of_not_gt hn
    have hyx : t y ≤ t x := ⟨hr, by omega⟩
    have hh : y ≤ x := by simpa only [Equiv.symm_apply_apply] using ht.monotone hyx
    exact not_le_of_gt hxy hh
  · intro hr
    have hxy : t x < t y := by
      refine lt_iff_le_not_ge.mpr ⟨⟨hr.le, by omega⟩, ?_⟩
      intro hh
      exact not_le_of_gt hr hh.1
    simpa only [Equiv.symm_apply_apply] using ht hxy

lemma column_eq_rowRank (t : Fin n ≃ D.cells) (ht : Standard t) (x : Fin n) :
    Fintype.card {y : Fin n // y < x ∧ (t y).val.1 = (t x).val.1} = (t x).val.2 := by
  let e : {y : Fin n // y < x ∧ (t y).val.1 = (t x).val.1} ≃ Fin ((t x).val.2) := {
    toFun := fun y => ⟨(t y.val).val.2, (standard_row_lt_iff t ht y.val x y.property.2).mp y.property.1⟩
    invFun := fun j => ⟨t.symm ⟨((t x).val.1, j), D.up_left_mem le_rfl j.isLt.le (t x).property⟩, by
      constructor
      · apply (standard_row_lt_iff t ht _ x (by simp)).mpr
        simpa only [Equiv.apply_symm_apply] using j.isLt
      · simp⟩
    left_inv := by
      intro y
      apply Subtype.ext
      apply t.injective
      simp only [Equiv.apply_symm_apply]
      apply Subtype.ext
      exact Prod.ext y.property.2.symm rfl
    right_inv := by intro j; apply Fin.ext; simp }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma standard_eq_of_rows (t u : Fin n ≃ D.cells) (ht : Standard t) (hu : Standard u)
    (hr : ∀ x, (t x).val.1 = (u x).val.1) : t = u := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Prod.ext (hr x)
  rw [← column_eq_rowRank t ht x, ← column_eq_rowRank u hu x]
  exact Fintype.card_congr ((Equiv.refl (Fin n)).subtypeEquiv (fun y => by simp only [Equiv.refl_apply, hr]))


theorem independent_of_leading {I : Type uI} {X : Type uX} {K : Type uK} [Fintype I] [Fintype X] [LinearOrder K]
    (e : I → EuclideanSpace ℂ X) (b : I → X) (key : X → K)
    (hinj : Function.Injective (key ∘ b)) (hdiag : ∀ i, e i (b i) ≠ 0)
    (htri : ∀ i x, e i x ≠ 0 → key (b i) ≤ key x) : LinearIndependent ℂ e := by
  let : LinearOrder I := LinearOrder.lift' (key ∘ b) hinj
  rw [linearIndependent_iff']
  intro s a ha i hi
  by_contra hai
  let S := s.filter fun j => a j ≠ 0
  have hs : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
  let j := S.min' hs
  have hj : j ∈ S := S.min'_mem hs
  have hj' : j ∈ s := (Finset.mem_filter.mp hj).1
  have haz : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hval := congrArg (fun v : EuclideanSpace ℂ X => v (b j)) ha
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hval
  rw [Finset.sum_eq_single_of_mem j hj'] at hval
  · exact (mul_ne_zero haz (hdiag j)) hval
  · intro k hk hkj
    by_cases hak : a k = 0
    · simp [hak]
    have hks : k ∈ S := Finset.mem_filter.mpr ⟨hk, hak⟩
    have hjk : j ≤ k := S.min'_le k hks
    have hjk' : j < k := lt_of_le_of_ne hjk (Ne.symm hkj)
    have hzero : e k (b j) = 0 := by
      by_contra hn
      have hh := htri k (b j) hn
      exact not_le_of_gt hjk' hh
    simp [hzero]


variable (D : YoungDiagram) (t : Fin n ≃ D.cells)

lemma column_word_le (ht : Standard t) (c : Equiv.Perm (Fin n)) (hc_col : ∀ x, (t (c x)).val.2 = (t x).val.2) :
    toLex ((fun x => (t x).val.1)) ≤ toLex (fun x => (fun x => (t x).val.1) (c⁻¹ x)) := by
  by_cases hc : c = 1
  · simp [hc]
  let S := Finset.univ.filter fun x : Fin n => c⁻¹ x ≠ x
  have hs : S.Nonempty := by
    by_contra hn
    apply hc
    have he : c⁻¹ = 1 := by
      apply Equiv.ext
      intro x
      by_contra hx
      exact hn ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    exact inv_eq_one.mp he
  let x := S.min' hs
  have hx : c⁻¹ x ≠ x := (Finset.mem_filter.mp (S.min'_mem hs)).2
  have hbefore (y : Fin n) (hy : y < x) : c⁻¹ y = y := by
    by_contra hn
    have hm : y ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hn⟩
    exact not_le_of_gt hy (S.min'_le y hm)
  have hlt : x < c⁻¹ x := by
    apply lt_of_le_of_ne
    · by_contra hn
      have hh := hbefore (c⁻¹ x) (lt_of_not_ge hn)
      exact hx (c.symm.injective hh)
    · exact Ne.symm hx
  have hcol : (t x).val.2 = (t (c⁻¹ x)).val.2 := by
    have hh := hc_col (c⁻¹ x)
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hh
  have hrow := (standard_col_lt_iff t ht x (c⁻¹ x) hcol).mp hlt
  apply le_of_lt
  change Pi.Lex (· < ·) (· < ·) ((fun x => (t x).val.1)) (fun y => (fun x => (t x).val.1) (c⁻¹ y))
  exact ⟨x, fun y hy => congrArg ((fun x => (t x).val.1)) (hbefore y hy).symm, hrow⟩


end WeldedPath.YoungLeadingWord

end

-- Solutions.YoungTableauIndependence
section

namespace WeldedPath.YoungTableauIndependence

open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open scoped BigOperators

noncomputable def word (μ : YoungDiagram) (r : Tabloid μ) :=
  toLex (fun i => r.1 ((referenceLabels μ).symm i))

theorem word_tableauTabloid (μ : YoungDiagram) (t : Std μ) :
    word μ (tableauTabloid μ t) = toLex (fun i => (t.1.symm i).1.1) := by
  funext i
  simp [word, tableauTabloid, relabel, canonical, ofPerm, tableauPerm, row, Equiv.Perm.inv_def]

theorem word_injective (μ : YoungDiagram) :
    Function.Injective (fun t : Std μ => word μ (tableauTabloid μ t)) := by
  intro t u h
  change word μ (tableauTabloid μ t) = word μ (tableauTabloid μ u) at h
  rw [word_tableauTabloid, word_tableauTabloid] at h
  have he := YoungLeadingWord.standard_eq_of_rows t.1.symm u.1.symm t.2 u.2 (fun i => congrFun h i)
  apply Subtype.ext
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm he

theorem polytabloid_support (μ : YoungDiagram) (r : Tabloid μ)
    (hr : polytabloid μ r ≠ 0) :
    ∃ c : columnGroup μ, r = relabel μ c.1 (canonical μ) := by
  rw [polytabloid, antisym_apply] at hr
  obtain ⟨c,_,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  have hd : delta μ (canonical μ) (relabel μ c.1⁻¹ r) ≠ 0 :=
    (mul_ne_zero_iff.mp hc).2
  have he : relabel μ c.1⁻¹ r = canonical μ := by
    by_contra hn
    exact hd (by simp [delta,hn])
  refine ⟨c,?_⟩
  have hh := congrArg (relabel μ c.1) he
  simpa only [← relabel_mul, mul_inv_cancel, relabel_one] using hh

theorem tableauVector_diagonal (μ : YoungDiagram) (t : Std μ) :
    tableauVector μ t (tableauTabloid μ t) = 1 := by
  simp only [tableauVector, tableauTabloid, tabloidRep_apply, ← relabel_mul,
    inv_mul_cancel, relabel_one, polytabloid_canonical]

theorem tableauVector_leading (μ : YoungDiagram) (t : Std μ) (r : Tabloid μ)
    (hr : tableauVector μ t r ≠ 0) : word μ (tableauTabloid μ t) ≤ word μ r := by
  obtain ⟨c,hc⟩ := polytabloid_support μ
    (relabel μ (tableauPerm μ t)⁻¹ r) hr
  have he : r = relabel μ (tableauPerm μ t) (relabel μ c.1 (canonical μ)) := by
    have hh := congrArg (relabel μ (tableauPerm μ t)) hc
    simpa only [← relabel_mul, mul_inv_cancel, relabel_one] using hh
  let d : Equiv.Perm (Fin (Fintype.card μ.cells)) := t.1.symm.trans (c.1.trans t.1)
  have hd : ∀ i, (t.1.symm (d i)).1.2 = (t.1.symm i).1.2 := by
    intro i
    dsimp [d]
    rw [Equiv.symm_apply_apply]
    exact c.2 _
  have hw := YoungLeadingWord.column_word_le μ t.1.symm t.2 d hd
  rw [word_tableauTabloid]
  have hw' : word μ r = toLex (fun i => (t.1.symm (d⁻¹ i)).1.1) := by
    rw [he]
    funext i
    simp [word, relabel, canonical, ofPerm, tableauPerm, row, d, Equiv.Perm.inv_def]
  rw [hw']
  exact hw

theorem tableauVector_linearIndependent (μ : YoungDiagram) :
    LinearIndependent ℂ (tableauVector μ) := by
  apply YoungLeadingWord.independent_of_leading (tableauVector μ) (tableauTabloid μ)
    (word μ) (word_injective μ)
  · intro t
    rw [tableauVector_diagonal]
    exact one_ne_zero
  · exact tableauVector_leading μ

theorem standardCount_le_specht_finrank (μ : YoungDiagram) :
    Tableau.standardCount μ ≤ Module.finrank ℂ (spechtSub μ).toSubmodule := by
  let v (t : Std μ) : (spechtSub μ).toSubmodule :=
    ⟨tableauVector μ t, Submodule.subset_span ⟨tableauPerm μ t,rfl⟩⟩
  have hv : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (spechtSub μ).toSubmodule.subtype (tableauVector_linearIndependent μ)
  exact hv.fintype_card_le_finrank

end WeldedPath.YoungTableauIndependence

end

-- Solutions.YoungSpechtDimension
section

namespace WeldedPath.YoungSpechtDimension

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
  OAI.PartialPermutation.DiagramCounting
open scoped BigOperators

theorem irreducible_degree_square_sum (G : Type*) [Group G] [Fintype G] :
    (∑ c : IrreducibleIndex G, irreducibleDegree c ^ 2) = Fintype.card G := by
  have h := sum_regular_character_kernels (1 : G)
  simp only [centralCharacterKernel, inv_one, Representation.char_one, ite_true] at h
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdiv : (∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ)^2) /
      (Fintype.card G : ℂ) = 1 := by
    rw [Finset.sum_div]
    convert h using 1
    apply Finset.sum_congr rfl
    intro c _
    change (irreducibleDegree c : ℂ)^2 / (Fintype.card G : ℂ) =
      (irreducibleDegree c : ℂ) / (Fintype.card G : ℂ) * (irreducibleDegree c : ℂ)
    ring
  have he : (∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ)^2) =
      (Fintype.card G : ℂ) := by
    simpa only [one_mul] using (div_eq_iff hc).mp hdiv
  exact_mod_cast he

theorem specht_degree_square_sum (n : ℕ) :
    (∑ μ : Shape n, Module.finrank ℂ (spechtSub μ.1).toSubmodule ^ 2) = n.factorial := by
  calc
    _ = ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)), irreducibleDegree c ^ 2 := by
      apply Fintype.sum_equiv (SpechtActual.indexEquiv n)
      intro μ
      obtain ⟨E⟩ := SpechtActual.index_spec μ
      have hd := E.toLinearEquiv.finrank_eq
      change irreducibleDegree (SpechtActual.index μ) =
        Module.finrank ℂ (spechtSub μ.1).toSubmodule at hd
      change Module.finrank ℂ (spechtSub μ.1).toSubmodule ^ 2 =
        irreducibleDegree (SpechtActual.index μ) ^ 2
      rw [hd]
    _ = _ := by
      rw [irreducible_degree_square_sum, Fintype.card_perm, Fintype.card_fin]

theorem standardCount_eq_specht_finrank (μ : YoungDiagram) :
    Tableau.standardCount μ = Module.finrank ℂ (spechtSub μ).toSubmodule := by
  have hle (ν : Shape μ.card) : Tableau.standardCount ν.1 ^ 2 ≤
      Module.finrank ℂ (spechtSub ν.1).toSubmodule ^ 2 :=
    Nat.pow_le_pow_left (YoungTableauIndependence.standardCount_le_specht_finrank ν.1) 2
  have he : (∑ ν : Shape μ.card, Tableau.standardCount ν.1 ^ 2) =
      ∑ ν : Shape μ.card, Module.finrank ℂ (spechtSub ν.1).toSubmodule ^ 2 := by
    rw [YoungCounts.standardCount_square_sum, specht_degree_square_sum]
  have ht := (Finset.sum_eq_sum_iff_of_le (fun ν _ => hle ν)).mp he
    (⟨μ,rfl⟩ : Shape μ.card) (Finset.mem_univ _)
  change Tableau.standardCount μ ^ 2 = Module.finrank ℂ (spechtSub μ).toSubmodule ^ 2 at ht
  nlinarith

end
end WeldedPath.YoungSpechtDimension

end

-- Solutions.FiniteRepresentationBranching
section

namespace WeldedPath.FiniteRepresentationBranching

noncomputable section
open Classical
open scoped BigOperators

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def averagedSection (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (B : W →ₗ[ℂ] V) : W →ₗ[ℂ] V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g).comp (B.comp (σ g⁻¹))

lemma averagedSection_apply (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (B : W →ₗ[ℂ] V) (w : W) :
    averagedSection ρ σ B w = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g (B (σ g⁻¹ w)) := by
  simp only [averagedSection, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]

lemma averagedSection_equivariant (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (B : W →ₗ[ℂ] V) (h : G) (w : W) :
    averagedSection ρ σ B (σ h w) = ρ h (averagedSection ρ σ B w) := by
  simp only [averagedSection_apply, map_smul, map_sum]
  congr 1
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft h)
  intro g
  change ρ h (ρ g (B (σ g⁻¹ w))) = ρ (h*g) (B (σ (h*g)⁻¹ (σ h w)))
  simp only [map_mul, Module.End.mul_apply, mul_inv_rev]
  have he : σ h⁻¹ (σ h w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [he]

lemma averagedSection_rightInverse {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (F : Representation.IntertwiningMap ρ σ) (B : W →ₗ[ℂ] V)
    (hB : ∀ w, F (B w) = w) : Function.RightInverse (averagedSection ρ σ B) F := by
  intro w
  rw [averagedSection_apply, map_smul, map_sum]
  have hterm (g : G) : F (ρ g (B (σ g⁻¹ w))) = w := by
    rw [F.isIntertwining, hB]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  simp only [hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem exists_equivariant_section {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Surjective F) :
    ∃ J : Representation.IntertwiningMap σ ρ, Function.RightInverse J F := by
  obtain ⟨B,hB⟩ := F.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hF)
  have hB' (w : W) : F (B w) = w := LinearMap.congr_fun hB w
  refine ⟨⟨averagedSection ρ σ B, ?_⟩, averagedSection_rightInverse F B hB'⟩
  intro g
  ext w
  exact averagedSection_equivariant ρ σ B g w

section Family

variable {I : Type*} [Fintype I] {D : I → Type*}
  [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
  (ρ : Representation ℂ G V) (σ : ∀ i, Representation ℂ G (D i))
  [∀ i, Representation.IsIrreducible (σ i)]

theorem joint_surjective
    (hne : ∀ i j, i ≠ j → ¬ Nonempty (Representation.Equiv (σ i) (σ j)))
    (F : ∀ i, Representation.IntertwiningMap ρ (σ i)) (hF : ∀ i, F i ≠ 0) :
    Function.Surjective (fun v : V => fun i => F i v) := by
  have hsurj (i : I) : Function.Surjective (F i) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (F i)).resolve_right (hF i)
  choose J hJ using fun i => exists_equivariant_section (F i) (hsurj i)
  have hcross (i j : I) (hij : i ≠ j) : (F i).comp (J j) = 0 := by
    rcases Representation.IsIrreducible.bijective_or_eq_zero ((F i).comp (J j)) with h | h
    · exact (hne j i hij.symm ⟨((F i).comp (J j)).ofBijective h⟩).elim
    · exact h
  intro w
  refine ⟨∑ i, J i (w i), ?_⟩
  funext i
  change F i (∑ j, J j (w j)) = w i
  rw [map_sum, Finset.sum_eq_single i]
  · exact hJ i (w i)
  · intro j _ hji
    have he := congrArg (fun A : Representation.IntertwiningMap (σ j) (σ i) => A (w j))
      (hcross i j hji.symm)
    exact he
  · simp

theorem exists_equiv_of_dim_sum [FiniteDimensional ℂ V]
    [∀ i, FiniteDimensional ℂ (D i)]
    (hne : ∀ i j, i ≠ j → ¬ Nonempty (Representation.Equiv (σ i) (σ j)))
    (F : ∀ i, Representation.IntertwiningMap ρ (σ i)) (hF : ∀ i, F i ≠ 0)
    (hdim : Module.finrank ℂ V = ∑ i, Module.finrank ℂ (D i)) :
    ∃ E : V ≃ₗ[ℂ] (∀ i, D i), ∀ v i, E v i = F i v := by
  let P : V →ₗ[ℂ] (∀ i, D i) := LinearMap.pi (fun i => (F i).toLinearMap)
  have hs : Function.Surjective P := joint_surjective ρ σ hne F hF
  have hd : Module.finrank ℂ V = Module.finrank ℂ (∀ i, D i) := by
    rw [Module.finrank_pi_fintype]
    exact hdim
  have hi : Function.Injective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs
  exact ⟨LinearEquiv.ofBijective P ⟨hi,hs⟩, fun _ _ => rfl⟩

end Family
end
end WeldedPath.FiniteRepresentationBranching

end

-- Solutions.FiniteRepresentationFixed
section

namespace WeldedPath.FiniteRepresentationBranching

noncomputable section
open Classical
open scoped BigOperators

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

def fixedUnder (ρ : Representation ℂ G V) (H : Subgroup G) : Submodule ℂ V where
  carrier := {v | ∀ g : H, ρ g.1 v = v}
  zero_mem' := by intro g; exact map_zero _
  add_mem' := by intro x y hx hy g; rw [map_add, hx, hy]
  smul_mem' := by intro a v hv g; rw [map_smul, hv]

variable {I : Type*} [Fintype I] {D : I → Type*}
  [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]

def fixedPiEquiv (ρ : Representation ℂ G V) (σ : ∀ i, Representation ℂ G (D i))
    (H : Subgroup G) (E : V ≃ₗ[ℂ] (∀ i, D i))
    (hE : ∀ g v i, E (ρ g v) i = σ i g (E v i)) :
    fixedUnder ρ H ≃ₗ[ℂ] (∀ i, fixedUnder (σ i) H) where
  toFun v i := ⟨E v.1 i, by
    intro g
    rw [← hE, v.2 g]⟩
  invFun w := ⟨E.symm (fun i => (w i).1), by
    intro g
    apply E.injective
    funext i
    rw [hE, E.apply_symm_apply]
    exact (w i).2 g⟩
  left_inv v := by
    apply Subtype.ext
    exact E.symm_apply_apply v.1
  right_inv w := by
    funext i
    apply Subtype.ext
    exact congrFun (E.apply_symm_apply (fun j => (w j).1)) i
  map_add' v w := by
    funext i
    apply Subtype.ext
    exact congrFun (E.map_add v.1 w.1) i
  map_smul' a v := by
    funext i
    apply Subtype.ext
    exact congrFun (E.map_smul a v.1) i

theorem finrank_fixed_pi [∀ i, FiniteDimensional ℂ (D i)]
    (ρ : Representation ℂ G V) (σ : ∀ i, Representation ℂ G (D i))
    (H : Subgroup G) (E : V ≃ₗ[ℂ] (∀ i, D i))
    (hE : ∀ g v i, E (ρ g v) i = σ i g (E v i)) :
    Module.finrank ℂ (fixedUnder ρ H) = ∑ i, Module.finrank ℂ (fixedUnder (σ i) H) := by
  rw [(fixedPiEquiv ρ σ H E hE).finrank_eq, Module.finrank_pi_fintype]

end
end WeldedPath.FiniteRepresentationBranching

end

-- Solutions.YoungBranchingComplete
section

-- MODULE YoungBranching
section

namespace WeldedPath.YoungBranching

noncomputable section
open Classical YoungCounts SpechtPieri OAI.PartialPermutation
  OAI.PartialPermutation.YoungTabloid OAI.PartialPermutation.DiagramCounting
open scoped BigOperators

abbrev Predecessor {n : ℕ} (μ : DiagramCounting.Shape (n+1)) := ↥(oneBoxPredecessors μ.1)

abbrev predecessorShape {n : ℕ} (μ : DiagramCounting.Shape (n+1)) (ν : Predecessor μ) : DiagramCounting.Shape n :=
  ⟨ν.1, by
    have h := (mem_predecessors.mp ν.2).2
    change ν.1.cells.card + 1 = μ.1.cells.card at h
    have hm := μ.2
    omega⟩

lemma predecessor_covers {n : ℕ} (μ : DiagramCounting.Shape (n+1)) (ν : Predecessor μ) :
    Covers (predecessorShape μ ν).1 μ.1 := mem_predecessors.mp ν.2

lemma predecessorShape_injective {n : ℕ} (μ : DiagramCounting.Shape (n+1)) :
    Function.Injective (predecessorShape μ) := by
  intro ν ξ h
  apply Subtype.ext
  exact congrArg (fun ξ : DiagramCounting.Shape n => ξ.1) h

theorem dimension_branching {n : ℕ} (μ : DiagramCounting.Shape (n+1)) :
    Module.finrank ℂ (spechtSub μ.1).toSubmodule =
      ∑ ν : Predecessor μ, Module.finrank ℂ (spechtSub (predecessorShape μ ν).1).toSubmodule := by
  have hm : μ.1.cells.Nonempty := by
    apply Finset.card_pos.mp
    have hc := μ.2
    omega
  simp only [← YoungSpechtDimension.standardCount_eq_specht_finrank,
    ← tableauCount_eq_standardCount]
  rw [tableauBranching μ.1 hm]
  change (∑ ν ∈ oneBoxPredecessors μ.1, tableauCount ν) =
    ∑ ν : ↥(oneBoxPredecessors μ.1), tableauCount ν.1
  exact (Finset.sum_coe_sort _ _).symm

/-- The actual canonical one-box restriction is the multiplicity-free sum of
the canonical Specht modules indexed by removable corners. -/
theorem branching_equiv {n : ℕ} (μ : DiagramCounting.Shape (n+1)) :
    ∃ E : (spechtSub μ.1).toSubmodule ≃ₗ[ℂ]
      (∀ ν : Predecessor μ, (spechtSub (predecessorShape μ ν).1).toSubmodule),
      ∀ v ν, E v ν = branchMap (predecessorShape μ ν) μ (predecessor_covers μ ν) v := by
  apply FiniteRepresentationBranching.exists_equiv_of_dim_sum
    (restrictedRep μ) (fun ν : Predecessor μ => SpechtActual.rep (predecessorShape μ ν))
  · intro ν ξ hne he
    obtain ⟨E⟩ := he
    exact hne (predecessorShape_injective μ
      (SpechtActual.rep_equiv_shape_eq _ _ E))
  · exact fun ν => branchMap_ne_zero (predecessorShape μ ν) μ (predecessor_covers μ ν)
  · exact dimension_branching μ

theorem fixed_dimension_branching {n : ℕ} (μ : DiagramCounting.Shape (n+1))
    (K : Subgroup (Equiv.Perm (Fin n))) :
    Module.finrank ℂ (FiniteRepresentationBranching.fixedUnder (restrictedRep μ) K) =
      ∑ ν : Predecessor μ, Module.finrank ℂ
        (FiniteRepresentationBranching.fixedUnder (SpechtActual.rep (predecessorShape μ ν)) K) := by
  obtain ⟨E,hE⟩ := branching_equiv μ
  apply FiniteRepresentationBranching.finrank_fixed_pi (restrictedRep μ)
    (fun ν => SpechtActual.rep (predecessorShape μ ν)) K E
  intro g v ν
  rw [hE, hE]
  exact LinearMap.congr_fun
    ((branchMap (predecessorShape μ ν) μ (predecessor_covers μ ν)).isIntertwining' g) v

end
end WeldedPath.YoungBranching
end

-- MODULE YoungTrivialSpecht
section

namespace WeldedPath.YoungBranching

noncomputable section
open Classical YoungCounts SpechtPieri OAI.PartialPermutation
  OAI.PartialPermutation.YoungTabloid OAI.PartialPermutation.DiagramCounting
open scoped BigOperators

def rowDiagram (n : ℕ) : YoungDiagram where
  cells := {0} ×ˢ Finset.range n
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hy ⊢
    exact ⟨Nat.eq_zero_of_le_zero (hy.1 ▸ hxy.1), hxy.2.trans_lt hy.2⟩

@[simp] lemma mem_rowDiagram (n : ℕ) (x : ℕ × ℕ) :
    x ∈ rowDiagram n ↔ x.1 = 0 ∧ x.2 < n := by
  change x ∈ ({0} ×ˢ Finset.range n) ↔ _
  rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_range]

@[simp] lemma rowDiagram_card (n : ℕ) : (rowDiagram n).card = n := by
  simp [rowDiagram, YoungDiagram.card]

abbrev rowShape (n : ℕ) : DiagramCounting.Shape n := ⟨rowDiagram n, rowDiagram_card n⟩

@[simp] lemma rowDiagram_rowLen (n : ℕ) : (rowDiagram n).rowLen 0 = n := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowDiagram]
  simp

lemma eq_rowDiagram_of_rows_zero (μ : YoungDiagram)
    (h : ∀ x : μ.cells, row μ x = 0) : μ = rowDiagram μ.card := by
  have he : μ.cells = {0} ×ˢ Finset.range (μ.rowLen 0) := by
    ext x
    constructor
    · intro hx
      have hr := h ⟨x,hx⟩
      change x.1 = 0 at hr
      have hc := μ.mem_iff_lt_rowLen.mp hx
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hr,
        Finset.mem_range.mpr (by simpa only [hr] using hc)⟩
    · intro hx
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hx
      apply μ.mem_iff_lt_rowLen.mpr
      simpa only [hx.1] using hx.2
  have hc : μ.card = μ.rowLen 0 := by
    change μ.cells.card = _
    rw [he]
    simp
  apply YoungDiagram.ext
  change μ.cells = {0} ×ˢ Finset.range μ.card
  rw [hc]
  exact he

lemma eq_rowDiagram_of_rowLen_eq_card (μ : YoungDiagram) (h : μ.rowLen 0 = μ.card) :
    μ = rowDiagram μ.card := by
  apply eq_rowDiagram_of_rows_zero μ
  intro x
  have hs : μ.row 0 ⊆ μ.cells := by
    intro y hy
    exact (YoungDiagram.mem_row_iff.mp hy).1
  have he : μ.row 0 = μ.cells := Finset.eq_of_subset_of_card_le hs (by
    rw [← μ.rowLen_eq_card]
    exact h.ge)
  have hx : x.1 ∈ μ.row 0 := he.symm ▸ x.2
  exact (YoungDiagram.mem_row_iff.mp hx).2

lemma tabloid_subsingleton_of_rows_zero (μ : YoungDiagram)
    (h : ∀ x : μ.cells, row μ x = 0) : Subsingleton (Tabloid μ) := by
  constructor
  intro r s
  obtain ⟨p,hp⟩ := r.2
  obtain ⟨q,hq⟩ := s.2
  apply Subtype.ext
  funext x
  rw [hp,hq]
  exact (h (p x)).trans (h (q x)).symm

lemma row_specht_action (n : ℕ) (g : Equiv.Perm (rowDiagram n).cells)
    (v : (spechtSub (rowDiagram n)).toSubmodule) : spechtRep (rowDiagram n) g v = v := by
  letI : Subsingleton (Tabloid (rowDiagram n)) := tabloid_subsingleton_of_rows_zero _
    (fun x => (mem_rowDiagram n x.1).mp x.2 |>.1)
  apply Subtype.ext
  ext r
  change v.1 (relabel (rowDiagram n) g⁻¹ r) = v.1 r
  rw [Subsingleton.elim (relabel (rowDiagram n) g⁻¹ r) r]

lemma row_specht_finrank (n : ℕ) :
    Module.finrank ℂ (spechtSub (rowDiagram n)).toSubmodule = 1 := by
  letI : Subsingleton (Tabloid (rowDiagram n)) := tabloid_subsingleton_of_rows_zero _
    (fun x => (mem_rowDiagram n x.1).mp x.2 |>.1)
  letI : Unique (Tabloid (rowDiagram n)) :=
    ⟨⟨canonical _⟩, fun _ => Subsingleton.elim _ _⟩
  have hle := (spechtSub (rowDiagram n)).toSubmodule.finrank_le
  have hne : (spechtSub (rowDiagram n)).toSubmodule ≠ ⊥ := by
    intro h
    have hp := polytabloid_mem_specht (rowDiagram n)
    change polytabloid (rowDiagram n) ∈ (spechtSub (rowDiagram n)).toSubmodule at hp
    rw [h] at hp
    exact polytabloid_ne_zero _ hp
  have hpos := Submodule.one_le_finrank_iff.mpr hne
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Tabloid (rowDiagram n))) = 1 := by
    simp
  omega

lemma full_fixed_zero_of_nonrow (μ : YoungDiagram) (hn : μ ≠ rowDiagram μ.card)
    (f : (spechtSub μ).toSubmodule)
    (hf : ∀ g : Equiv.Perm μ.cells, spechtRep μ g f = f) : f = 0 := by
  by_contra hne
  have hfne : f.1 ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨g,hg⟩ := specht_detect μ f.1 f.2 hfne
  have hfixed (g : Equiv.Perm μ.cells) : tabloidRep μ g f.1 = f.1 :=
    congrArg Subtype.val (hf g)
  rw [hfixed] at hg
  have hex : ∃ x : μ.cells, row μ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (eq_rowDiagram_of_rows_zero μ h)
  obtain ⟨x,hx⟩ := hex
  let a : μ.cells := ⟨(0,0), μ.up_left_mem (Nat.zero_le _) (Nat.zero_le _) x.2⟩
  let b : μ.cells := ⟨(1,0), μ.up_left_mem (by change 1 ≤ x.1.1; exact Nat.one_le_iff_ne_zero.mpr hx)
    (Nat.zero_le _) x.2⟩
  have hab : a ≠ b := by intro h; have := congrArg (fun z : μ.cells => z.1.1) h; simp [a,b] at this
  have hc : Equiv.swap a b ∈ columnGroup μ := by
    intro z
    by_cases hza : z = a
    · subst z; simp [a,b,OAI.PartialPermutation.YoungTabloid.col]
    by_cases hzb : z = b
    · subst z; simp [a,b,OAI.PartialPermutation.YoungTabloid.col]
    rw [Equiv.swap_apply_of_ne_of_ne hza hzb]
  have hi := tabloidRep_unitary μ (Equiv.swap a b) (polytabloid μ) f.1
  rw [column_polytabloid μ ⟨_,hc⟩, signC_swap a b hab, hfixed] at hi
  have hz : inner ℂ (polytabloid μ) f.1 = 0 := by
    exact CharZero.neg_eq_self_iff.mp (by simpa only [neg_one_smul, inner_neg_left] using hi)
  exact hg hz

theorem full_fixed_finrank {n : ℕ} (μ : DiagramCounting.Shape n) :
    Module.finrank ℂ (FiniteRepresentationBranching.fixedUnder (SpechtActual.rep μ) ⊤) =
      if μ = rowShape n then 1 else 0 := by
  by_cases hm : μ = rowShape n
  · subst μ
    rw [if_pos rfl]
    have ht : FiniteRepresentationBranching.fixedUnder (SpechtActual.rep (rowShape n)) ⊤ = ⊤ := by
      apply top_unique
      intro f _ g
      exact row_specht_action n _ f
    rw [ht, finrank_top]
    exact row_specht_finrank n
  · rw [if_neg hm]
    have hb : FiniteRepresentationBranching.fixedUnder (SpechtActual.rep μ) ⊤ = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro f hf
      apply full_fixed_zero_of_nonrow μ.1
      · intro h
        apply hm
        apply Subtype.ext
        simpa only [μ.2] using h
      · intro g
        have hh := hf ⟨(SpechtActual.labels μ).permCongrHom g, trivial⟩
        change spechtRep μ.1 ((SpechtActual.labels μ).symm.permCongrHom
          ((SpechtActual.labels μ).permCongrHom g)) f = f at hh
        simpa only [← Equiv.permCongrHom_symm, MulEquiv.symm_apply_apply] using hh
    rw [hb, finrank_bot]

end
end WeldedPath.YoungBranching
end

-- MODULE YoungFixedBranching
section

namespace WeldedPath.YoungBranching

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
  OAI.PartialPermutation.DiagramCounting FiniteRepresentationBranching
open scoped BigOperators

lemma viaEmbedding_trans {A B C : Type*} (e : Equiv.Perm A)
    (i : A ↪ B) (j : B ↪ C) :
    (e.viaEmbedding i).viaEmbedding j = e.viaEmbedding (i.trans j) := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y,rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply]
    by_cases hy : y ∈ Set.range i
    · obtain ⟨z,rfl⟩ := hy
      rw [Equiv.Perm.viaEmbedding_apply]
      exact (Equiv.Perm.viaEmbedding_apply e (i.trans j) z).symm
    · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy]
      symm
      apply Equiv.Perm.viaEmbedding_apply_of_notMem
      rintro ⟨z,hz⟩
      exact hy ⟨z,j.injective hz⟩
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]
    symm
    apply Equiv.Perm.viaEmbedding_apply_of_notMem
    rintro ⟨z,hz⟩
    exact hx ⟨i z,hz⟩

lemma viaEmbedding_initial_step {m n : ℕ} (h : m ≤ n) (g : Equiv.Perm (Fin m)) :
    (g.viaEmbedding (Fin.castLEEmb h)).viaEmbedding Fin.castSuccEmb =
      g.viaEmbedding (Fin.castLEEmb (h.trans (Nat.le_succ n))) := by
  rw [viaEmbedding_trans]
  congr 1

lemma viaEmbedding_initial_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (g : Equiv.Perm (Fin a)) :
    (g.viaEmbedding (Fin.castLEEmb hab)).viaEmbedding (Fin.castLEEmb hbc) =
      g.viaEmbedding (Fin.castLEEmb (hab.trans hbc)) := by
  rw [viaEmbedding_trans]
  congr 1

def initialRep {m n : ℕ} (μ : DiagramCounting.Shape n) (h : m ≤ n) :
    Representation ℂ (Equiv.Perm (Fin m)) (spechtSub μ.1).toSubmodule :=
  (SpechtActual.rep μ).comp (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h))

def initialFixed {m n : ℕ} (μ : DiagramCounting.Shape n) (h : m ≤ n) :
    Submodule ℂ (spechtSub μ.1).toSubmodule := fixedUnder (initialRep μ h) ⊤

theorem initialFixed_eq_invariants {m n : ℕ} (μ : DiagramCounting.Shape n) (h : m ≤ n) :
    initialFixed μ h = (initialRep μ h).invariants := by
  apply Submodule.ext
  intro v
  constructor
  · intro hv g
    exact hv ⟨g,trivial⟩
  · intro hv g
    exact hv g.1

theorem initialFixed_mono {a b n : ℕ} (μ : DiagramCounting.Shape n) (hab : a ≤ b) (hbn : b ≤ n) :
    initialFixed μ hbn ≤ initialFixed μ (hab.trans hbn) := by
  intro v hv g
  have hh := hv ⟨g.1.viaEmbedding (Fin.castLEEmb hab), trivial⟩
  change SpechtActual.rep μ
    ((g.1.viaEmbedding (Fin.castLEEmb hab)).viaEmbedding (Fin.castLEEmb hbn)) v = v at hh
  rw [viaEmbedding_initial_trans] at hh
  exact hh

theorem initial_fixed_dimension_branching {m n : ℕ} (μ : DiagramCounting.Shape (n+1)) (h : m ≤ n) :
    Module.finrank ℂ (initialFixed μ (h.trans (Nat.le_succ n))) =
      ∑ ν : Predecessor μ, Module.finrank ℂ (initialFixed (predecessorShape μ ν) h) := by
  obtain ⟨E,hE⟩ := branching_equiv μ
  apply finrank_fixed_pi (initialRep μ (h.trans (Nat.le_succ n)))
    (fun ν => initialRep (predecessorShape μ ν) h) ⊤ E
  intro g v ν
  rw [hE,hE]
  have hi := LinearMap.congr_fun
    ((branchMap (predecessorShape μ ν) μ (predecessor_covers μ ν)).isIntertwining'
      (g.viaEmbedding (Fin.castLEEmb h))) v
  change branchMap (predecessorShape μ ν) μ (predecessor_covers μ ν)
    (SpechtActual.rep μ ((g.viaEmbedding (Fin.castLEEmb h)).viaEmbedding Fin.castSuccEmb) v) = _ at hi
  rw [viaEmbedding_initial_step] at hi
  exact hi

lemma viaEmbedding_initial_refl {n : ℕ} (g : Equiv.Perm (Fin n)) :
    g.viaEmbedding (Fin.castLEEmb (le_refl n)) = g := by
  apply Equiv.ext
  intro i
  exact Equiv.Perm.viaEmbedding_apply g (Fin.castLEEmb (le_refl n)) i

theorem initial_fixed_dimension_self {n : ℕ} (μ : DiagramCounting.Shape n) :
    Module.finrank ℂ (initialFixed μ (le_refl n)) = if μ = rowShape n then 1 else 0 := by
  have he : initialFixed μ (le_refl n) = fixedUnder (SpechtActual.rep μ) ⊤ := by
    apply Submodule.ext
    intro v
    change (∀ g : (⊤ : Subgroup (Equiv.Perm (Fin n))),
      SpechtActual.rep μ (g.1.viaEmbedding (Fin.castLEEmb (le_refl n))) v = v) ↔ _
    simp only [viaEmbedding_initial_refl]
    rfl
  rw [he]
  exact full_fixed_finrank μ

end
end WeldedPath.YoungBranching
end

-- MODULE YoungTails
section

namespace WeldedPath.YoungCounts

noncomputable section
open Classical

def rowShift : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun x := (x.1+1,x.2)
  inj' := by intro x y h; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
             exact Prod.ext (Nat.add_right_cancel h1) h2

def rowTail (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.preimage rowShift rowShift.injective.injOn
  isLowerSet := by
    intro y x hxy hy
    have hy' : rowShift y ∈ μ := Finset.mem_preimage.mp hy
    apply Finset.mem_preimage.mpr
    exact μ.up_left_mem (Nat.add_le_add_right hxy.1 1) hxy.2 hy'

@[simp] lemma mem_rowTail (μ : YoungDiagram) (x : ℕ × ℕ) :
    x ∈ rowTail μ ↔ (x.1+1,x.2) ∈ μ := by
  change x ∈ μ.cells.preimage rowShift rowShift.injective.injOn ↔ _
  exact Finset.mem_preimage

lemma rowTail_rowLen (μ : YoungDiagram) (i : ℕ) :
    (rowTail μ).rowLen i = μ.rowLen (i+1) := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowTail, YoungDiagram.mem_iff_lt_rowLen]

lemma rowShift_range (x : ℕ × ℕ) : x ∈ Set.range rowShift ↔ x.1 ≠ 0 := by
  constructor
  · rintro ⟨y,rfl⟩
    simp [rowShift]
  · intro h
    refine ⟨(x.1-1,x.2), ?_⟩
    apply Prod.ext
    · change x.1-1+1 = x.1
      omega
    · rfl

lemma rowTail_card (μ : YoungDiagram) :
    (rowTail μ).card + μ.rowLen 0 = μ.card := by
  have ht : (rowTail μ).card = (μ.cells.filter (fun x => x.1 ≠ 0)).card := by
    change (μ.cells.preimage rowShift rowShift.injective.injOn).card = _
    rw [Finset.card_preimage]
    congr 1
    ext x
    simp only [Finset.mem_filter, rowShift_range]
  have hr : μ.cells.filter (fun x => x.1 = 0) = μ.row 0 := rfl
  rw [ht, μ.rowLen_eq_card, ← hr]
  exact (Nat.add_comm _ _).trans
    (Finset.card_filter_add_card_filter_not (s := μ.cells) (fun x => x.1 = 0))

lemma rowTail_mono {μ ν : YoungDiagram} (h : μ ≤ ν) : rowTail μ ≤ rowTail ν := by
  intro x hx
  exact (mem_rowTail ν x).mpr (h ((mem_rowTail μ x).mp hx))

lemma rowLen_mono {μ ν : YoungDiagram} (h : μ ≤ ν) (i : ℕ) : μ.rowLen i ≤ ν.rowLen i := by
  by_contra hn
  have hx : (i,ν.rowLen i) ∈ μ := μ.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hn)
  exact (Nat.lt_irrefl _) (ν.mem_iff_lt_rowLen.mp (h hx))

def prependRow (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) : YoungDiagram where
  cells := ({0} ×ˢ Finset.range m) ∪ ν.cells.map rowShift
  isLowerSet := by
    intro y x hxy hy
    rcases Finset.mem_union.mp hy with hy | hy
    · apply Finset.mem_union_left
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hy ⊢
      exact ⟨Nat.eq_zero_of_le_zero (hy.1 ▸ hxy.1), hxy.2.trans_lt hy.2⟩
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hy
      by_cases hx : x.1 = 0
      · apply Finset.mem_union_left
        simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
        refine ⟨hx, hxy.2.trans_lt ((ν.mem_iff_lt_rowLen.mp hz).trans_le ?_)⟩
        exact (ν.rowLen_anti 0 z.1 (Nat.zero_le _)).trans hm
      · apply Finset.mem_union_right
        refine Finset.mem_map.mpr ⟨(x.1-1,x.2), ?_, ?_⟩
        · apply ν.up_left_mem (by have := hxy.1; change x.1 ≤ z.1+1 at this; omega) hxy.2 hz
        · apply Prod.ext
          · change x.1-1+1=x.1; omega
          · rfl

lemma mem_prependRow (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) (x : ℕ × ℕ) :
    x ∈ prependRow m ν hm ↔
      (x.1 = 0 ∧ x.2 < m) ∨ (x.1 ≠ 0 ∧ (x.1-1,x.2) ∈ ν) := by
  change x ∈ ({0} ×ˢ Finset.range m) ∪ ν.cells.map rowShift ↔ _
  rw [Finset.mem_union]
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp h
    change y.1+1 ≠ 0 ∧ (y.1+1-1,y.2) ∈ ν
    refine ⟨by omega, ?_⟩
    simpa only [Nat.add_sub_cancel, Prod.eta, YoungDiagram.mem_cells] using hy
  · intro hx
    refine Finset.mem_map.mpr ⟨(x.1-1,x.2), hx.2, ?_⟩
    apply Prod.ext
    · change x.1-1+1=x.1; omega
    · rfl

lemma prependRow_card (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) :
    (prependRow m ν hm).card = m + ν.card := by
  change (({0} ×ˢ Finset.range m) ∪ ν.cells.map rowShift).card = _
  rw [Finset.card_union_of_disjoint]
  · simp [YoungDiagram.card]
  · apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hx0 : x.1=0 := (Finset.mem_product.mp hx).1 |> Finset.mem_singleton.mp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx'
    simpa [rowShift] using hx0

lemma rowTail_prependRow (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) :
    rowTail (prependRow m ν hm) = ν := by
  ext x
  simp [mem_rowTail, mem_prependRow]

lemma prependRow_rowLen (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) :
    (prependRow m ν hm).rowLen 0 = m := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_prependRow]
  simp

lemma rowTail_rowLen_le (μ : YoungDiagram) : (rowTail μ).rowLen 0 ≤ μ.rowLen 0 := by
  rw [rowTail_rowLen]
  exact μ.rowLen_anti 0 1 (by omega)

lemma prependRow_rowTail (μ : YoungDiagram) :
    prependRow (μ.rowLen 0) (rowTail μ) (rowTail_rowLen_le μ) = μ := by
  ext x
  change x ∈ prependRow (μ.rowLen 0) (rowTail μ) (rowTail_rowLen_le μ) ↔ x ∈ μ
  rw [mem_prependRow, mem_rowTail]
  by_cases hx : x.1=0
  · simp only [hx, true_and, ne_eq, not_true_eq_false, false_and, or_false]
    constructor
    · intro hj
      have hm : (0,x.2) ∈ μ := μ.mem_iff_lt_rowLen.mpr hj
      simpa only [← hx, Prod.eta] using hm
    · intro hm
      have hj := μ.mem_iff_lt_rowLen.mp hm
      simpa only [hx] using hj
  · have he : x.1-1+1=x.1 := by omega
    simp only [hx, false_and, ne_eq, not_false_eq_true, true_and, false_or, he, Prod.eta]

lemma diagram_le_iff (μ ν : YoungDiagram) : μ ≤ ν ↔
    μ.rowLen 0 ≤ ν.rowLen 0 ∧ rowTail μ ≤ rowTail ν := by
  constructor
  · intro h
    exact ⟨rowLen_mono h 0, rowTail_mono h⟩
  · rintro ⟨hr,ht⟩ x hx
    by_cases hx0 : x.1=0
    · apply ν.mem_iff_lt_rowLen.mpr
      have hm := μ.mem_iff_lt_rowLen.mp hx
      rw [hx0] at hm ⊢
      exact hm.trans_le hr
    · have he : x.1-1+1=x.1 := by omega
      have hx' : (x.1-1,x.2) ∈ rowTail μ := by
        rw [mem_rowTail]
        simpa only [he,Prod.eta] using hx
      have hn := (mem_rowTail ν (x.1-1,x.2)).mp (ht hx')
      simpa only [he,Prod.eta] using hn

lemma covers_tail_of_firstRow_eq {μ ν : YoungDiagram} (h : Covers ν μ)
    (hr : ν.rowLen 0 = μ.rowLen 0) : Covers (rowTail ν) (rowTail μ) := by
  refine ⟨rowTail_mono h.1, ?_⟩
  have hv := rowTail_card ν
  have hm := rowTail_card μ
  have hc := h.2
  omega

lemma covers_prependRow {μ ν : YoungDiagram} (h : Covers ν (rowTail μ)) :
    Covers (prependRow (μ.rowLen 0) ν ((rowLen_mono h.1 0).trans (rowTail_rowLen_le μ))) μ := by
  constructor
  · apply (diagram_le_iff _ _).mpr
    rw [prependRow_rowLen, rowTail_prependRow]
    exact ⟨le_refl _,h.1⟩
  · rw [prependRow_card]
    have hm := rowTail_card μ
    have hc := h.2
    omega

abbrev SameRowPredecessor (μ : YoungDiagram) :=
  {ν : ↥(oneBoxPredecessors μ) // ν.1.rowLen 0 = μ.rowLen 0}

abbrev tailPredecessorEquiv (μ : YoungDiagram) :
    SameRowPredecessor μ ≃ ↥(oneBoxPredecessors (rowTail μ)) where
  toFun ν := ⟨rowTail ν.1.1, mem_predecessors.mpr
    (covers_tail_of_firstRow_eq (mem_predecessors.mp ν.1.2) ν.2)⟩
  invFun ν := ⟨⟨prependRow (μ.rowLen 0) ν.1
      ((rowLen_mono (mem_predecessors.mp ν.2).1 0).trans (rowTail_rowLen_le μ)),
    mem_predecessors.mpr (covers_prependRow (mem_predecessors.mp ν.2))⟩,
      prependRow_rowLen (μ.rowLen 0) ν.1
        ((rowLen_mono (mem_predecessors.mp ν.2).1 0).trans (rowTail_rowLen_le μ))⟩
  left_inv ν := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp only
    have hr := ν.2
    simpa only [← hr] using prependRow_rowTail ν.1.1
  right_inv ν := by
    apply Subtype.ext
    dsimp only
    exact rowTail_prependRow (μ.rowLen 0) ν.1
      ((rowLen_mono (mem_predecessors.mp ν.2).1 0).trans (rowTail_rowLen_le μ))

@[simp] lemma tailPredecessorEquiv_apply (μ : YoungDiagram) (ν : SameRowPredecessor μ) :
    (tailPredecessorEquiv μ ν).1 = rowTail ν.1.1 := rfl

end
end WeldedPath.YoungCounts
end

-- MODULE YoungFixedMultiplicity
section

namespace WeldedPath.YoungBranching

noncomputable section
open Classical YoungCounts OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
  OAI.PartialPermutation.DiagramCounting
open scoped BigOperators

lemma sum_sameRow_predecessors (μ : YoungDiagram) :
    (∑ ν : ↥(oneBoxPredecessors μ),
      if ν.1.rowLen 0 = μ.rowLen 0 then tableauCount (rowTail ν.1) else 0) =
      ∑ ξ : ↥(oneBoxPredecessors (rowTail μ)), tableauCount ξ.1 := by
  calc
    _ = ∑ ν : SameRowPredecessor μ, tableauCount (rowTail ν.1.1) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := Fintype.sum_equiv (tailPredecessorEquiv μ) _ _ (fun _ => by
      rw [tailPredecessorEquiv_apply])

/-- At the first possible level, the subgroup-fixed multiplicity is exactly
the standard-tableau count below the first row. Below that level it vanishes. -/
theorem initial_fixed_multiplicity (m n : ℕ) (h : m ≤ n) (μ : DiagramCounting.Shape n) :
    (μ.1.rowLen 0 < m → Module.finrank ℂ (initialFixed μ h) = 0) ∧
    (μ.1.rowLen 0 = m → Module.finrank ℂ (initialFixed μ h) = tableauCount (rowTail μ.1)) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hmn : m=n
    · subst m
      constructor
      · intro hr
        have hne : μ ≠ rowShape n := by
          intro he
          have hh : μ.1.rowLen 0 = n := by rw [he]; exact rowDiagram_rowLen n
          omega
        rw [initial_fixed_dimension_self, if_neg hne]
      · intro hr
        have he : μ = rowShape n := by
          apply Subtype.ext
          have hc : μ.1.card = n := μ.2
          simpa only [hc] using eq_rowDiagram_of_rowLen_eq_card μ.1 (hr.trans hc.symm)
        rw [he, initial_fixed_dimension_self, if_pos rfl]
        symm
        apply tableauCount_of_card_zero
        change (rowTail (rowDiagram n)).card = 0
        have hc := rowTail_card (rowDiagram n)
        rw [rowDiagram_card, rowDiagram_rowLen] at hc
        omega
    · have hm : m < n := lt_of_le_of_ne h hmn
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      have hmk : m ≤ k := by omega
      have hs := initial_fixed_dimension_branching μ hmk
      constructor
      · intro hr
        rw [hs]
        apply Finset.sum_eq_zero
        intro ν _
        apply (ih k (Nat.lt_succ_self _) m hmk (predecessorShape μ ν)).1
        exact (rowLen_mono (predecessor_covers μ ν).1 0).trans_lt hr
      · intro hr
        rw [hs]
        have ht : (rowTail μ.1).cells.Nonempty := by
          apply Finset.card_pos.mp
          change 0 < (rowTail μ.1).card
          have hc := rowTail_card μ.1
          have hn : μ.1.card = k+1 := μ.2
          omega
        calc
          _ = ∑ ν : Predecessor μ,
              if ν.1.rowLen 0 = μ.1.rowLen 0 then tableauCount (rowTail ν.1) else 0 := by
            apply Finset.sum_congr rfl
            intro ν _
            by_cases hv : ν.1.rowLen 0 = μ.1.rowLen 0
            · rw [if_pos hv]
              exact (ih k (Nat.lt_succ_self _) m hmk (predecessorShape μ ν)).2 (hv.trans hr)
            · rw [if_neg hv]
              apply (ih k (Nat.lt_succ_self _) m hmk (predecessorShape μ ν)).1
              change ν.1.rowLen 0 < m
              have hle := rowLen_mono (predecessor_covers μ ν).1 0
              change ν.1.rowLen 0 ≤ μ.1.rowLen 0 at hle
              omega
          _ = ∑ ξ : ↥(oneBoxPredecessors (rowTail μ.1)), tableauCount ξ.1 :=
            sum_sameRow_predecessors μ.1
          _ = _ := by
            rw [Finset.sum_coe_sort]
            exact (tableauBranching (rowTail μ.1) ht).symm

theorem initial_fixed_eq_tail_count {m n : ℕ} (μ : DiagramCounting.Shape n) (h : m ≤ n)
    (hr : μ.1.rowLen 0 = m) :
    Module.finrank ℂ (initialFixed μ h) = tableauCount (rowTail μ.1) :=
  (initial_fixed_multiplicity m n h μ).2 hr

theorem initial_fixed_eq_zero_of_firstRow_lt {m n : ℕ} (μ : DiagramCounting.Shape n) (h : m ≤ n)
    (hr : μ.1.rowLen 0 < m) : Module.finrank ℂ (initialFixed μ h) = 0 :=
  (initial_fixed_multiplicity m n h μ).1 hr

lemma tableauCount_pos (μ : YoungDiagram) : 0 < tableauCount μ := by
  rw [tableauCount_eq_standardCount]
  exact Fintype.card_pos_iff.mpr ⟨Tableau.chosenFilling μ.cells⟩

theorem initial_fixed_pos_iff {m n : ℕ} (μ : DiagramCounting.Shape n) (h : m ≤ n) :
    0 < Module.finrank ℂ (initialFixed μ h) ↔ m ≤ μ.1.rowLen 0 := by
  constructor
  · intro hp
    by_contra hn
    have hz := initial_fixed_eq_zero_of_firstRow_lt μ h (Nat.lt_of_not_ge hn)
    omega
  · intro hr
    have hsize : μ.1.rowLen 0 ≤ n := by
      simpa only [μ.2] using DiagramCounting.rowLen_le_card μ.1 0
    have he := initial_fixed_eq_tail_count μ hsize rfl
    have hp : 0 < Module.finrank ℂ (initialFixed μ hsize) := by
      rw [he]
      exact tableauCount_pos _
    exact hp.trans_le (Submodule.finrank_mono (initialFixed_mono μ hr hsize))

theorem initial_invariants_dimension_firstRow {m n : ℕ}
    (μ : DiagramCounting.Shape n) (h : m ≤ n) (hr : μ.1.rowLen 0 = m) :
    Module.finrank ℂ (initialRep μ h).invariants =
      Module.finrank ℂ (spechtSub (rowTail μ.1)).toSubmodule := by
  rw [← initialFixed_eq_invariants, initial_fixed_eq_tail_count μ h hr,
    tableauCount_eq_standardCount, YoungSpechtDimension.standardCount_eq_specht_finrank]

theorem initial_invariants_pos_iff {m n : ℕ} (μ : DiagramCounting.Shape n) (h : m ≤ n) :
    0 < Module.finrank ℂ (initialRep μ h).invariants ↔ m ≤ μ.1.rowLen 0 := by
  rw [← initialFixed_eq_invariants]
  exact initial_fixed_pos_iff μ h

end
end WeldedPath.YoungBranching
end


end

-- Solutions.YoungHookFormula
section
-- Complete port of accepted P26 hook-formula proof closure.

section

noncomputable section

namespace WeldedPath.YoungCounts

def cellHook (cells : Finset (ℕ × ℕ)) (b : ℕ × ℕ) : ℕ :=
  1 + (cells.filter fun a => a.1 = b.1 ∧ b.2 < a.2).card +
    (cells.filter fun a => a.2 = b.2 ∧ b.1 < a.1).card


open scoped BigOperators

attribute [local instance] Classical.propDecidable


/- Occupied removable corners, in zero-based English coordinates (§1, p.3). -/

/- The noncorner cells, and the cells D_rs of equation (3) (p.4). -/
def noncorners (lam : YoungDiagram) : Finset Cell := lam.cells \ corners lam

def offCross (lam : YoungDiagram) (r s : ℕ) : Finset Cell :=
  (noncorners lam).filter fun z => z.1 ≠ r ∧ z.2 ≠ s

/- Exactly the one-box predecessor diagrams of §1 (p.3). -/

/- The accepted inverse filling predicate, restricted to the finite occupied-cell
codomain. Labels and coordinates are zero-based; there is no dimension cutoff (p.3). -/

/- The accepted hook counts the occupied cell, its strict arm and strict leg (p.3). -/
abbrev hook (lam : YoungDiagram) (z : Cell) : ℕ :=
  WeldedPath.YoungCounts.cellHook lam.cells z

/- Hook products in the rational numbers; subtraction is subsequently in ℚ (pp.3–4). -/
def hookProduct (lam : YoungDiagram) : ℚ := ∏ z ∈ lam.cells, (hook lam z : ℚ)

/- Strict-hook linear weight, equation (4), p.4. -/
def strictHook {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (i j : ℕ) : K :=
  (∑ k ∈ Finset.Ico (i + 1) (lam.colLen j), x k) +
    ∑ l ∈ Finset.Ico (j + 1) (lam.rowLen i), y l

/- The two cross denominators in WHL; all bounds have been shifted from
one-based source indices to zero-based indices (pp.2,6). -/
def rowGap {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (i r s : ℕ) : K :=
  (∑ k ∈ Finset.Ico (i + 1) (r + 1), x k) +
    ∑ l ∈ Finset.Ico (s + 1) (lam.rowLen i), y l

def colGap {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (j r s : ℕ) : K :=
  (∑ k ∈ Finset.Ico (r + 1) (lam.colLen j), x k) +
    ∑ l ∈ Finset.Ico (j + 1) (s + 1), y l

/- Total starting weight W (pp.2,8). -/
def totalWeight {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) : K := ∑ z ∈ lam.cells, x z.1 * y z.2

/- The named corner weight Π_rs of Theorem 2 (p.6), not a further product. -/
def cornerWeight {K : Type*} [Field K] (lam : YoungDiagram)
    (x y : ℕ → K) (r s : ℕ) : K :=
  x r * y s * (∏ i ∈ Finset.range r, (1 + x i / rowGap lam x y i r s)) *
    ∏ j ∈ Finset.range s, (1 + y j / colGap lam x y j r s)

/- The two outside denominators of Theorem 2(b–d), p.6. -/
def outsideA {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (r s : ℕ) : K :=
  (∑ k ∈ Finset.Ico (r + 1) (lam.colLen 0), x k) +
    ∑ l ∈ Finset.range (s + 1), y l

def outsideB {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (r s : ℕ) : K :=
  (∑ k ∈ Finset.range (r + 1), x k) +
    ∑ l ∈ Finset.Ico (s + 1) (lam.rowLen 0), y l

/- The polynomial ring on exactly the occupied rows and columns (pp.2,6). -/
abbrev WeightPoly (lam : YoungDiagram) :=
  MvPolynomial (Sum (Fin (lam.colLen 0)) (Fin (lam.rowLen 0))) ℚ

abbrev WeightRat (lam : YoungDiagram) := FractionRing (WeightPoly lam)

/- Canonical tagged row/column indeterminates; unused out-of-range indices
are extended by zero and are never used in the displayed formulas (p.4). -/
def polyX (lam : YoungDiagram) (i : ℕ) : WeightPoly lam :=
  if h : i < lam.colLen 0 then MvPolynomial.X (Sum.inl ⟨i, h⟩) else 0

def polyY (lam : YoungDiagram) (j : ℕ) : WeightPoly lam :=
  if h : j < lam.rowLen 0 then MvPolynomial.X (Sum.inr ⟨j, h⟩) else 0

def ratX (lam : YoungDiagram) (i : ℕ) : WeightRat lam :=
  algebraMap (WeightPoly lam) (WeightRat lam) (polyX lam i)

def ratY (lam : YoungDiagram) (j : ℕ) : WeightRat lam :=
  algebraMap (WeightPoly lam) (WeightRat lam) (polyY lam j)

/- The single corner summand of the polynomial equation (4), p.4. -/
def polynomialTerm (lam : YoungDiagram) (r s : ℕ) : WeightPoly lam :=
  polyX lam r * polyY lam s *
    (∏ z ∈ offCross lam r s, strictHook lam (polyX lam) (polyY lam) z.1 z.2) *
    (∏ i ∈ Finset.range r, (polyX lam i + rowGap lam (polyX lam) (polyY lam) i r s)) *
    ∏ j ∈ Finset.range s, (polyY lam j + colGap lam (polyX lam) (polyY lam) j r s)

/- Corrected Kerov corner factors, Corollary 3, p.7. X_i in Lean means
source X_(i+1), whereas Y_i retains its source index. -/
def kerovPi (d : ℕ) (q : ℝ) (X Y : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k,
    (q ^ Y (i + 1) - q ^ X k) / (q ^ X i - q ^ X k)) *
  ∏ i ∈ Finset.Ico (k + 1) d,
    (q ^ X k - q ^ Y i) / (q ^ X k - q ^ X i)

/- Z and S of Corollary 3, p.7. -/
def kerovZ (d : ℕ) (q : ℝ) (X Y : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range d, q ^ X i) - ∑ i ∈ Finset.Ico 1 d, q ^ Y i

def kerovS (d : ℕ) (q : ℝ) (X Y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range d, ∑ j ∈ Finset.Ico i d,
    (q ^ Y i - q ^ X i) * (q ^ X j - q ^ Y (j + 1))

/- Strict legal arm/leg successors of §4.1, p.8; diagonals are excluded. -/
def successors (lam : YoungDiagram) (z : Cell) : Finset Cell :=
  lam.cells.filter fun t => (t.2 = z.2 ∧ z.1 < t.1) ∨ (t.1 = z.1 ∧ z.2 < t.2)

/- Modified hook of §4.2, p.8: skip the entire equal-length row or column
block. Finset.min is +infinity if the eligible corner set is empty, so bad
inputs yield no successors in that direction. -/
def modifiedSuccessors (lam : YoungDiagram) (z : Cell) : Finset Cell :=
  lam.cells.filter fun t =>
    (t.2 = z.2 ∧
      (((corners lam).filter fun c => z.1 ≤ c.1).image Prod.fst).min < (t.1 : WithTop ℕ)) ∨
    (t.1 = z.1 ∧
      (((corners lam).filter fun c => z.2 ≤ c.2).image Prod.snd).min < (t.2 : WithTop ℕ))

/- Single transition mass, normalized over the entire strict or modified hook,
not separately over its two directions (§4, p.8). -/
def moveWeight (x y : ℕ → ℝ) (z t : Cell) : ℝ :=
  if t.2 = z.2 then x t.1 else y t.2

/- Finite evaluation of the actual stopped path law (§4, pp.8–9).
At a terminal cell return the event on [z]; otherwise sum the normalized
transition masses. At insufficient fuel return zero. On a valid diagram,
card(lam) fuel covers every path, as every move strictly increases a coordinate. -/
def walkEval (next : Cell → Finset Cell) (x y : ℕ → ℝ) :
    ℕ → Cell → (List Cell → ℝ) → ℝ
  | 0, z, event => if next z = ∅ then event [z] else 0
  | fuel + 1, z, event =>
    if next z = ∅ then event [z] else
      ∑ t ∈ next z, moveWeight x y z t /
        (∑ u ∈ next z, moveWeight x y z u) *
          walkEval next x y fuel t (fun tail => event (z :: tail))

/- Probability of the actual terminal cell, including the random initial cell
with probability x_i y_j/W (§4, pp.8–9). -/
def terminalProb (lam : YoungDiagram) (next : Cell → Finset Cell)
    (x y : ℕ → ℝ) (c : Cell) : ℝ :=
  ∑ z ∈ lam.cells, (x z.1 * y z.2 / totalWeight lam x y) *
    walkEval next x y lam.card z (fun p => if p.getLast? = some c then 1 else 0)

/- Strict positivity only on the occupied row/column ranges (p.8). -/
def PositiveWeights (lam : YoungDiagram) (x y : ℕ → ℝ) : Prop :=
  (∀ i < lam.colLen 0, 0 < x i) ∧ (∀ j < lam.rowLen 0, 0 < y j)

/- Row and column block endpoints, sorted in increasing coordinate (§4.2, pp.8–9). -/
def rowEnds (lam : YoungDiagram) : List ℕ := ((corners lam).image Prod.fst).sort (· ≤ ·)

def colEnds (lam : YoungDiagram) : List ℕ := ((corners lam).image Prod.snd).sort (· ≤ ·)

/- Output corner of a terminal modified block (p.9, staircase proof).
The raw cell need not be its block's southeast endpoint: on a rectangle
every modified hook is empty. Identify its equal-row/equal-column block
with that endpoint, as required by the source's staircase equivalence.
On out-of-range raw inputs the find operations default to the given coordinate. -/
def blockCorner (lam : YoungDiagram) (z : Cell) : Cell :=
  (((rowEnds lam).find? (fun r => decide (z.1 ≤ r))).getD z.1,
    ((colEnds lam).find? (fun s => decide (z.2 ≤ s))).getD z.2)

/- Terminal-corner output law of the modified process (pp.8–9).
Sum the actual modified transition law on raw cells, and identify the final
block with its corner, rather than requiring the last raw cell to be that corner. -/
def modifiedTerminalProb (lam : YoungDiagram) (x y : ℕ → ℝ) (c : Cell) : ℝ :=
  ∑ z ∈ lam.cells, (x z.1 * y z.2 / totalWeight lam x y) *
    walkEval (modifiedSuccessors lam) x y lam.card z (fun p =>
      if p.getLast?.map (blockCorner lam) = some c then 1 else 0)

/- X_k is the sum of row weights, and Y_k the sum of column weights, over
equal-length blocks (p.9, Figure 4 and proof of Theorem 5). The prose on p.9
mistakenly says elements of U for both sums; the example fixes the intended meaning. -/
def blockX (lam : YoungDiagram) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (lam.colLen 0),
    if lam.rowLen i = lam.rowLen ((rowEnds lam).getD k 0) then x i else 0

def blockY (lam : YoungDiagram) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (lam.rowLen 0),
    if lam.colLen j = lam.colLen ((colEnds lam).getD k 0) then y j else 0

/- Zero-based rank of an actual corner, from top right to bottom left (p.9). -/
def cornerRank (lam : YoungDiagram) (c : Cell) : ℕ :=
  ((corners lam).filter fun t => t.1 < c.1).card

/- Corner factor for the c-row staircase in Theorem 5, p.9. -/
def staircaseWeight (c : ℕ) (X Y : ℕ → ℝ) (r s : ℕ) : ℝ :=
  X r * Y s *
    (∏ i ∈ Finset.range r, (1 + X i /
      ((∑ k ∈ Finset.Ico (i + 1) (r + 1), X k) +
        ∑ l ∈ Finset.Ico (s + 1) (c - i), Y l))) *
    ∏ j ∈ Finset.range s, (1 + Y j /
      ((∑ k ∈ Finset.Ico (r + 1) (c - j), X k) +
        ∑ l ∈ Finset.Ico (j + 1) (s + 1), Y l))

/- Projection-event probability from a deterministic starting cell, equivalent
to conditioning on that positive-probability start (§5, pp.9–10). -/
def projectionProb (lam : YoungDiagram) (x y : ℕ → ℝ) (start : Cell)
    (I J : Finset ℕ) : ℝ :=
  walkEval (successors lam) x y lam.card start (fun p =>
    if p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J then 1 else 0)

/- Tagged formal labels; row and column labels are distinct regardless of
any later numerical specialization (§2.2, pp.4–5). -/
abbrev Label := Sum ℕ ℕ

/- Raw arrangement with canonical dummy labels at corners. The predicates
below restrict exactly the labels used in F_lambda and G_lambda (pp.4–5). -/
abbrev Arrangement (lam : YoungDiagram) := Cell × ({z : Cell // z ∈ lam.cells} → Label)

/- Read an old label, with a fixed dummy outside the occupied diagram (p.5). -/
def oldLabel (lam : YoungDiagram) (a : Arrangement lam) (z : Cell) : Label :=
  if h : z ∈ lam.cells then a.2 ⟨z, h⟩ else Sum.inl 0

/- Strict-hook admissibility of a tagged label (§2.2, p.4). -/
def StrictLabel (lam : YoungDiagram) (z : Cell) : Label → Prop
  | Sum.inl k => z.1 < k ∧ k < lam.colLen z.2
  | Sum.inr l => z.2 < l ∧ l < lam.rowLen z.1

/- F_lambda, including the starting-square special labels (§2.2, p.4). -/
def hookLabelInputs (lam : YoungDiagram) : Set (Arrangement lam) :=
  {a | a.1 ∈ lam.cells ∧ ∀ z : {z : Cell // z ∈ lam.cells},
    if z.val ∈ corners lam then a.2 z = Sum.inl 0 else StrictLabel lam z.val (a.2 z)}

/- G_lambda with the source's special rules on the terminal row and column;
at a corner lambda'_s=r+1 and lambda_r=s+1 in zero-based coordinates (p.4). -/
def hookLabelOutputs (lam : YoungDiagram) : Set (Arrangement lam) :=
  {a | a.1 ∈ corners lam ∧ ∀ z : {z : Cell // z ∈ lam.cells},
    if z.val ∈ corners lam then a.2 z = Sum.inl 0 else
      if z.val.2 = a.1.2 then
        match a.2 z with
        | Sum.inl k => z.val.1 ≤ k ∧ k ≤ a.1.1
        | Sum.inr l => a.1.2 < l ∧ l < lam.rowLen z.val.1
      else if z.val.1 = a.1.1 then
        match a.2 z with
        | Sum.inl k => a.1.1 < k ∧ k < lam.colLen z.val.2
        | Sum.inr l => z.val.2 ≤ l ∧ l ≤ a.1.2
      else StrictLabel lam z.val (a.2 z)}

/- Arrow encoded by a tagged label (p.5). -/
def arrowTarget (z : Cell) : Label → Cell
  | Sum.inl k => (k, z.2)
  | Sum.inr l => (z.1, l)

/- Follow the old labels, stopping at the first corner (p.5). Fuel card(lam)
suffices on hookLabelInputs because every strict-hook arrow advances a coordinate. -/
def arrowPath (lam : YoungDiagram) (a : Arrangement lam) : ℕ → Cell → List Cell
  | 0, z => [z]
  | fuel + 1, z => if z ∈ corners lam then [z] else
    z :: arrowPath lam a fuel (arrowTarget z (oldLabel lam a z))

/- The p.5 rearrangement, evaluated from the old arrangement simultaneously.
Projected visited rows get their own x-label and projected columns their own
y-label. Other walk cells receive the old label from the shaded row/column.
This also handles a walk that starts at a corner without reading a corner label. -/
def rearrangeHookLabels (lam : YoungDiagram) (a : Arrangement lam) : Arrangement lam :=
  let path := arrowPath lam a lam.card a.1
  let c := path.getLast?.getD a.1
  (c, fun z =>
    if z.val ∈ corners lam then Sum.inl 0 else
    if z.val.2 = c.2 ∧ z.val.1 ∈ path.toFinset.image Prod.fst then Sum.inl z.val.1 else
    if z.val.1 = c.1 ∧ z.val.2 ∈ path.toFinset.image Prod.snd then Sum.inr z.val.2 else
    if z.val ∈ path then
      match oldLabel lam a z.val with
      | Sum.inl _ => oldLabel lam a (z.val.1, c.2)
      | Sum.inr _ => oldLabel lam a (c.1, z.val.2)
    else a.2 z)

/- Sanity: the strict hook has no labels in the empty diagram. -/
example : corners (⊥ : YoungDiagram) = ∅ := by simp [corners]

/- Sanity: arrow tags retain the intended axis and target. -/
example (i j k : ℕ) : arrowTarget (i, j) (Sum.inl k) = (k, j) := by rfl

/- Sanity: an already terminal starting cell is evaluated exactly once. -/
example (x y : ℕ → ℝ) (z : Cell) (event : List Cell → ℝ) :
    walkEval (fun _ => ∅) x y 0 z event = event [z] := by
  simp [walkEval]

/- Sanity: both products in the one-corner q-factor are empty. -/
example (q : ℝ) (X Y : ℕ → ℝ) : kerovPi 1 q X Y 0 = 1 := by
  simp [kerovPi]

/- Sanity: the empty shape has no one-box oneBoxPredecessors. -/
example : oneBoxPredecessors (⊥ : YoungDiagram) = ∅ := by
  simp [oneBoxPredecessors, YoungDiagram.card]

/- Sanity: the empty hook product is one. -/
example : hookProduct (⊥ : YoungDiagram) = 1 := by
  simp [hookProduct]

/- Sanity: zero weights make every strict-hook sum and total weight zero. -/
example (lam : YoungDiagram) (i j : ℕ) :
    strictHook lam (fun _ => (0 : ℚ)) (fun _ => 0) i j = 0 ∧
      totalWeight lam (fun _ => (0 : ℚ)) (fun _ => 0) = 0 := by
  simp [strictHook, totalWeight]

/- Sanity: the first unused row/column is not a formal variable. -/
example (lam : YoungDiagram) :
    polyX lam (lam.colLen 0) = 0 ∧ polyY lam (lam.rowLen 0) = 0 := by
  simp [polyX, polyY]

/- Sanity: singleton-corner factors have two empty products. -/
example (lam : YoungDiagram) (x y : ℕ → ℚ) :
    cornerWeight lam x y 0 0 = x 0 * y 0 := by
  simp [cornerWeight]

/- Sanity: the ordinary hook cannot contain its own starting cell. -/
example (lam : YoungDiagram) (z : Cell) : z ∉ successors lam z := by
  simp [successors]

/- Sanity: the empty diagram has no modified successors or terminal mass. -/
example (z c : Cell) (x y : ℕ → ℝ) :
    modifiedSuccessors (⊥ : YoungDiagram) z = ∅ ∧
      terminalProb (⊥ : YoungDiagram) (successors ⊥) x y c = 0 := by
  simp [modifiedSuccessors, terminalProb]

/- Sanity: a vertical transition carries the target row weight. -/
example (x y : ℕ → ℝ) (i j k : ℕ) :
    moveWeight x y (i, j) (k, j) = x k := by
  simp [moveWeight]

/- Sanity: a one-block staircase has no nontrivial product factors. -/
example (X Y : ℕ → ℝ) : staircaseWeight 1 X Y 0 0 = X 0 * Y 0 := by
  simp [staircaseWeight]

/- Sanity: a one-term Z and S use the two outside endpoints. -/
example (q : ℝ) (X Y : ℕ → ℝ) :
    kerovZ 1 q X Y = q ^ X 0 ∧
      kerovS 1 q X Y = (q ^ Y 0 - q ^ X 0) * (q ^ X 0 - q ^ Y 1) := by
  simp [kerovZ, kerovS]

/- Sanity: reading outside the empty diagram is the canonical dummy. -/
example (a : Arrangement ⊥) (z : Cell) : oldLabel ⊥ a z = Sum.inl 0 := by
  simp [oldLabel]

/- Sanity: the arrow path stops at a corner before reading any label. -/
example (lam : YoungDiagram) (a : Arrangement lam) (z : Cell)
    (hz : z ∈ corners lam) : arrowPath lam a 1 z = [z] := by
  simp [arrowPath, hz]

/- Sanity: a single modified block outputs its southeast corner even when
its raw starting cell is interior, as on every rectangular diagram. -/
example (lam : YoungDiagram) (z : Cell) (r s : ℕ)
    (hr : rowEnds lam = [r]) (hs : colEnds lam = [s])
    (hrow : z.1 ≤ r) (hcol : z.2 ≤ s) : blockCorner lam z = (r, s) := by
  simp [blockCorner, hr, hs, hrow, hcol]

end WeldedPath.YoungCounts
end

-- Accepted proof: 6f7ff2bd-5f2e-4322-b73e-6c2f6088e6cb
section

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7T_succ_le {lam : YoungDiagram} {z t : Cell} (ht : t ∈ successors lam z) : z ≤ t := by
  simp only [successors, Finset.mem_filter] at ht
  rcases ht.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.le_def.mpr ⟨h2.le, h1.ge⟩
  · exact Prod.le_def.mpr ⟨h1.ge, h2.le⟩

theorem X7T_congr (lam : YoungDiagram) (x y : ℕ → ℝ) : ∀ (f : ℕ) (z : Cell) (e1 e2 : List Cell → ℝ),
    (∀ p : List Cell, (∀ c ∈ p, z ≤ c) → e1 (z :: p) = e2 (z :: p)) →
    walkEval (successors lam) x y f z e1 = walkEval (successors lam) x y f z e2 := by
  intro f
  induction f with
  | zero =>
    intro z e1 e2 h
    simp only [walkEval, h [] (by simp)]
  | succ f ih =>
    intro z e1 e2 h
    simp only [walkEval]
    split_ifs
    · exact h [] (by simp)
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      congr 1
      apply ih
      intro p hp
      apply h (t :: p)
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact X7T_succ_le ht
      · exact le_trans (X7T_succ_le ht) (hp c hc)

theorem X7T_zero (lam : YoungDiagram) (x y : ℕ → ℝ) : ∀ (f : ℕ) (z : Cell) (e : List Cell → ℝ),
    (∀ p : List Cell, (∀ c ∈ p, z ≤ c) → e (z :: p) = 0) →
    walkEval (successors lam) x y f z e = 0 := by
  intro f
  induction f with
  | zero =>
    intro z e h
    simp only [walkEval, h [] (by simp)]
    split_ifs <;> rfl
  | succ f ih =>
    intro z e h
    simp only [walkEval]
    split_ifs
    · exact h [] (by simp)
    · apply Finset.sum_eq_zero
      intro t ht
      rw [ih t _ (fun p hp => h (t :: p) (by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact X7T_succ_le ht
        · exact le_trans (X7T_succ_le ht) (hp c hc))), mul_zero]

theorem X7T_succ_eq (lam : YoungDiagram) (i0 j0 : ℕ) :
    successors lam (i0, j0) =
      (Finset.Ico (i0 + 1) (lam.colLen j0)).image (fun k => (k, j0)) ∪
      (Finset.Ico (j0 + 1) (lam.rowLen i0)).image (fun l => (i0, l)) := by
  ext ⟨a, b⟩
  simp only [successors, Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_union,
    Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨hab, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · left
      subst h1
      exact ⟨a, ⟨h2, YoungDiagram.mem_iff_lt_colLen.mp hab⟩, rfl, rfl⟩
    · right
      subst h1
      exact ⟨b, ⟨h2, YoungDiagram.mem_iff_lt_rowLen.mp hab⟩, rfl, rfl⟩
  · rintro (⟨k, ⟨hk1, hk2⟩, rfl, rfl⟩ | ⟨l, ⟨hl1, hl2⟩, rfl, rfl⟩)
    · exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr hk2, Or.inl ⟨rfl, hk1⟩⟩
    · exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hl2, Or.inr ⟨rfl, hl1⟩⟩

theorem X7T_denom (lam : YoungDiagram) (x y : ℕ → ℝ) (i0 j0 : ℕ) :
    ∑ u ∈ successors lam (i0, j0), moveWeight x y (i0, j0) u =
      (∑ k ∈ Finset.Ico (i0 + 1) (lam.colLen j0), x k) +
        ∑ l ∈ Finset.Ico (j0 + 1) (lam.rowLen i0), y l := by
  rw [X7T_succ_eq, Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [moveWeight]
    · refine Finset.sum_congr rfl (fun l hl => ?_)
      have : l ≠ j0 := by simp only [Finset.mem_Ico] at hl; omega
      simp [moveWeight, this]
  · intro a _ b _ h; simpa using h
  · intro a _ b _ h; simpa using h
  · rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at h1 h2
    obtain ⟨k, ⟨hk, _⟩, rfl, rfl⟩ := h1
    obtain ⟨l, ⟨hl, _⟩, h3, rfl⟩ := h2
    omega


theorem X7T_corner_facts {lam : YoungDiagram} {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (r, s) ∈ lam ∧ lam.colLen s = r + 1 ∧ lam.rowLen r = s + 1 := by
  simp only [corners, Finset.mem_filter, YoungDiagram.mem_cells] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  refine ⟨h0, ?_, ?_⟩
  · have a := YoungDiagram.mem_iff_lt_colLen.mp h0
    have b : ¬ (r + 1 < lam.colLen s) := fun h => h1 (YoungDiagram.mem_iff_lt_colLen.mpr h)
    omega
  · have a := YoungDiagram.mem_iff_lt_rowLen.mp h0
    have b : ¬ (s + 1 < lam.rowLen r) := fun h => h2 (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    omega

theorem X7T_main (lam : YoungDiagram) (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y)
    (r s : ℕ) (hc : (r, s) ∈ corners lam)
    (ev : Finset ℕ → Finset ℕ → List Cell → ℝ)
    (hev1 : ∀ I J p, (p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J) →
      ev I J p = 1)
    (hev0 : ∀ I J p, ¬ (p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J) →
      ev I J p = 0) :
    ∀ (f i0 j0 : ℕ) (I J : Finset ℕ), i0 ∈ I → r ∈ I → (∀ i ∈ I, i0 ≤ i ∧ i ≤ r) →
      j0 ∈ J → s ∈ J → (∀ j ∈ J, j0 ≤ j ∧ j ≤ s) → (r - i0) + (s - j0) ≤ f →
      walkEval (successors lam) x y f (i0, j0) (ev I J) =
        ((∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
        ((∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by
  obtain ⟨hrs, hcol, hrow⟩ := X7T_corner_facts hc
  obtain ⟨hx, hy⟩ := hpos
  have hr0 : r < lam.colLen 0 :=
    YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem le_rfl (Nat.zero_le s) hrs)
  have hs0 : s < lam.rowLen 0 :=
    YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem (Nat.zero_le r) le_rfl hrs)
  have hxn : ∀ k, k < lam.colLen 0 → 0 ≤ x k := fun k hk => (hx k hk).le
  have hyn : ∀ l, l < lam.rowLen 0 → 0 ≤ y l := fun l hl => (hy l hl).le
  have hrg_nn : ∀ i, 0 ≤ rowGap lam x y i r s := by
    intro i
    unfold rowGap
    apply add_nonneg
    · apply Finset.sum_nonneg; intro k hk; simp only [Finset.mem_Ico] at hk
      exact hxn k (by omega)
    · apply Finset.sum_nonneg; intro l hl; simp only [Finset.mem_Ico] at hl
      have := lam.rowLen_anti 0 i (Nat.zero_le i)
      exact hyn l (by omega)
  have hcg_nn : ∀ j, 0 ≤ colGap lam x y j r s := by
    intro j
    unfold colGap
    apply add_nonneg
    · apply Finset.sum_nonneg; intro k hk; simp only [Finset.mem_Ico] at hk
      have := lam.colLen_anti 0 j (Nat.zero_le j)
      exact hxn k (by omega)
    · apply Finset.sum_nonneg; intro l hl; simp only [Finset.mem_Ico] at hl
      exact hyn l (by omega)
  have hrg_pos : ∀ i, i < r → 0 < rowGap lam x y i r s := by
    intro i hi
    unfold rowGap
    have h1 : x r ≤ ∑ k ∈ Finset.Ico (i + 1) (r + 1), x k :=
      Finset.single_le_sum (f := x) (fun k hk => by
        simp only [Finset.mem_Ico] at hk; exact hxn k (by omega))
        (by simp only [Finset.mem_Ico]; omega)
    have h2 : 0 ≤ ∑ l ∈ Finset.Ico (s + 1) (lam.rowLen i), y l := by
      apply Finset.sum_nonneg; intro l hl; simp only [Finset.mem_Ico] at hl
      have := lam.rowLen_anti 0 i (Nat.zero_le i)
      exact hyn l (by omega)
    have := hx r hr0
    linarith
  have hcg_pos : ∀ j, j < s → 0 < colGap lam x y j r s := by
    intro j hj
    unfold colGap
    have h1 : y s ≤ ∑ l ∈ Finset.Ico (j + 1) (s + 1), y l :=
      Finset.single_le_sum (f := y) (fun l hl => by
        simp only [Finset.mem_Ico] at hl; exact hyn l (by omega))
        (by simp only [Finset.mem_Ico]; omega)
    have h2 : 0 ≤ ∑ k ∈ Finset.Ico (r + 1) (lam.colLen j), x k := by
      apply Finset.sum_nonneg; intro k hk; simp only [Finset.mem_Ico] at hk
      have := lam.colLen_anti 0 j (Nat.zero_le j)
      exact hxn k (by omega)
    have := hy s hs0
    linarith
  have hrg_r : rowGap lam x y r r s = 0 := by simp [rowGap, hrow]
  have hcg_s : colGap lam x y s r s = 0 := by simp [colGap, hcol]
  have hsucc_rs : successors lam (r, s) = ∅ := by
    rw [X7T_succ_eq, hcol, hrow]; simp
  have hcorner : ∀ (f : ℕ) (I J : Finset ℕ), r ∈ I → (∀ i ∈ I, r ≤ i ∧ i ≤ r) →
      s ∈ J → (∀ j ∈ J, s ≤ j ∧ j ≤ s) →
      walkEval (successors lam) x y f (r, s) (ev I J) =
        ((∏ i ∈ I.erase r, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
        ((∏ j ∈ J.erase s, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by
    intro f I J hrI hI hsJ hJ
    have hI1 : I = {r} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hrI, fun i hi => le_antisymm (hI i hi).2 (hI i hi).1⟩
    have hJ1 : J = {s} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hsJ, fun j hj => le_antisymm (hJ j hj).2 (hJ j hj).1⟩
    subst hI1 hJ1
    have hev : ev {r} {s} [(r, s)] = 1 := hev1 _ _ _ (by simp)
    cases f <;> simp [walkEval, hsucc_rs, hev]
  intro f
  induction f with
  | zero =>
    intro i0 j0 I J hi0 hrI hI hj0 hsJ hJ hf
    have e1 : i0 = r := by have := hI i0 hi0; omega
    have e2 : j0 = s := by have := hJ j0 hj0; omega
    subst e1 e2
    exact hcorner 0 I J hrI hI hsJ hJ
  | succ f ih =>
    intro i0 j0 I J hi0 hrI hI hj0 hsJ hJ hf
    by_cases hzc : i0 = r ∧ j0 = s
    · obtain ⟨rfl, rfl⟩ := hzc
      exact hcorner (f + 1) I J hrI hI hsJ hJ
    have hi0r : i0 ≤ r := (hI i0 hi0).2
    have hj0s : j0 ≤ s := (hJ j0 hj0).2
    set I' := I.erase i0 with hI'def
    set J' := J.erase j0 with hJ'def
    -- reduction of the events
    have hdown : ∀ k, i0 < k →
        walkEval (successors lam) x y f (k, j0) (fun tail => ev I J ((i0, j0) :: tail)) =
          walkEval (successors lam) x y f (k, j0) (ev I' J) := by
      intro k hk
      apply X7T_congr
      intro p hp
      have hiR : i0 ∉ (((k, j0) :: p).toFinset.image Prod.fst) := by
        intro h
        simp only [Finset.mem_image, List.mem_toFinset] at h
        obtain ⟨c, hc, hc1⟩ := h
        rcases List.mem_cons.mp hc with rfl | hc
        · simp at hc1; omega
        · have := (Prod.le_def.mp (hp c hc)).1; simp at this; omega
      have hjC : j0 ∈ (((k, j0) :: p).toFinset.image Prod.snd) := by
        simp only [Finset.mem_image, List.mem_toFinset]
        exact ⟨(k, j0), List.mem_cons_self .., rfl⟩
      have key : ((((i0, j0) :: (k, j0) :: p).toFinset.image Prod.fst = I ∧
          ((i0, j0) :: (k, j0) :: p).toFinset.image Prod.snd = J) ↔
          ((((k, j0) :: p).toFinset.image Prod.fst = I' ∧
            ((k, j0) :: p).toFinset.image Prod.snd = J))) := by
        rw [List.toFinset_cons (a := (i0, j0)), Finset.image_insert, Finset.image_insert,
          Finset.insert_eq_of_mem hjC]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rw [hI'def, ← h1, Finset.erase_insert hiR]
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rw [h1, hI'def, Finset.insert_erase hi0]
      by_cases h : (((k, j0) :: p).toFinset.image Prod.fst = I' ∧
            ((k, j0) :: p).toFinset.image Prod.snd = J)
      · rw [hev1 _ _ _ h, hev1 _ _ _ (key.mpr h)]
      · rw [hev0 _ _ _ h, hev0 _ _ _ (fun h' => h (key.mp h'))]
    have hright : ∀ l, j0 < l →
        walkEval (successors lam) x y f (i0, l) (fun tail => ev I J ((i0, j0) :: tail)) =
          walkEval (successors lam) x y f (i0, l) (ev I J') := by
      intro l hl
      apply X7T_congr
      intro p hp
      have hjC : j0 ∉ (((i0, l) :: p).toFinset.image Prod.snd) := by
        intro h
        simp only [Finset.mem_image, List.mem_toFinset] at h
        obtain ⟨c, hc, hc1⟩ := h
        rcases List.mem_cons.mp hc with rfl | hc
        · simp at hc1; omega
        · have := (Prod.le_def.mp (hp c hc)).2; simp at this; omega
      have hiR : i0 ∈ (((i0, l) :: p).toFinset.image Prod.fst) := by
        simp only [Finset.mem_image, List.mem_toFinset]
        exact ⟨(i0, l), List.mem_cons_self .., rfl⟩
      have key : ((((i0, j0) :: (i0, l) :: p).toFinset.image Prod.fst = I ∧
          ((i0, j0) :: (i0, l) :: p).toFinset.image Prod.snd = J) ↔
          ((((i0, l) :: p).toFinset.image Prod.fst = I ∧
            ((i0, l) :: p).toFinset.image Prod.snd = J'))) := by
        rw [List.toFinset_cons (a := (i0, j0)), Finset.image_insert, Finset.image_insert,
          Finset.insert_eq_of_mem hiR]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rw [hJ'def, ← h2, Finset.erase_insert hjC]
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rw [h2, hJ'def, Finset.insert_erase hj0]
      by_cases h : (((i0, l) :: p).toFinset.image Prod.fst = I ∧
            ((i0, l) :: p).toFinset.image Prod.snd = J')
      · rw [hev1 _ _ _ h, hev1 _ _ _ (key.mpr h)]
      · rw [hev0 _ _ _ h, hev0 _ _ _ (fun h' => h (key.mp h'))]
    have hdown0 : ∀ k, (∀ h : I'.Nonempty, k ≠ I'.min' h) →
        walkEval (successors lam) x y f (k, j0) (ev I' J) = 0 := by
      intro k hk
      apply X7T_zero
      intro p hp
      apply hev0
      rintro ⟨h1, -⟩
      have hkI : k ∈ I' := by
        rw [← h1]; simp only [Finset.mem_image, List.mem_toFinset]
        exact ⟨(k, j0), List.mem_cons_self .., rfl⟩
      have hne : I'.Nonempty := ⟨k, hkI⟩
      have hle := I'.min'_le k hkI
      have hm : I'.min' hne ∈ (((k, j0) :: p).toFinset.image Prod.fst) := by
        rw [h1]; exact I'.min'_mem hne
      simp only [Finset.mem_image, List.mem_toFinset] at hm
      obtain ⟨c, hc, hc1⟩ := hm
      have : k ≤ c.1 := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · exact (Prod.le_def.mp (hp c hc)).1
      exact hk hne (le_antisymm (by rw [← hc1] at hle ⊢; omega) hle)
    have hright0 : ∀ l, (∀ h : J'.Nonempty, l ≠ J'.min' h) →
        walkEval (successors lam) x y f (i0, l) (ev I J') = 0 := by
      intro l hl
      apply X7T_zero
      intro p hp
      apply hev0
      rintro ⟨-, h1⟩
      have hlJ : l ∈ J' := by
        rw [← h1]; simp only [Finset.mem_image, List.mem_toFinset]
        exact ⟨(i0, l), List.mem_cons_self .., rfl⟩
      have hne : J'.Nonempty := ⟨l, hlJ⟩
      have hle := J'.min'_le l hlJ
      have hm : J'.min' hne ∈ (((i0, l) :: p).toFinset.image Prod.snd) := by
        rw [h1]; exact J'.min'_mem hne
      simp only [Finset.mem_image, List.mem_toFinset] at hm
      obtain ⟨c, hc, hc1⟩ := hm
      have : l ≤ c.2 := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · exact (Prod.le_def.mp (hp c hc)).2
      exact hl hne (le_antisymm (by rw [← hc1] at hle ⊢; omega) hle)
    have hrI' : i0 < r → r ∈ I' := fun h => Finset.mem_erase.mpr ⟨by omega, hrI⟩
    have hI'r : I'.Nonempty → i0 < r := fun ⟨m, hm⟩ => by
      have h1 := Finset.mem_erase.mp hm; have := hI m h1.2; omega
    have hsJ' : j0 < s → s ∈ J' := fun h => Finset.mem_erase.mpr ⟨by omega, hsJ⟩
    have hJ's : J'.Nonempty → j0 < s := fun ⟨m, hm⟩ => by
      have h1 := Finset.mem_erase.mp hm; have := hJ m h1.2; omega
    set kk : ℕ := if h : I'.Nonempty then I'.min' h else i0 + 1 with hkk
    set ll : ℕ := if h : J'.Nonempty then J'.min' h else j0 + 1 with hll
    have hkk_spec : ∀ h : I'.Nonempty, kk = I'.min' h := fun h => by rw [hkk, dif_pos h]
    have hll_spec : ∀ h : J'.Nonempty, ll = J'.min' h := fun h => by rw [hll, dif_pos h]
    have hkk_I : ∀ h : I'.Nonempty, i0 < kk ∧ kk ≤ r := fun h => by
      rw [hkk_spec h]
      have hm := Finset.mem_erase.mp (I'.min'_mem h)
      have := hI _ hm.2
      omega
    have hll_J : ∀ h : J'.Nonempty, j0 < ll ∧ ll ≤ s := fun h => by
      rw [hll_spec h]
      have hm := Finset.mem_erase.mp (J'.min'_mem h)
      have := hJ _ hm.2
      omega
    have hkk_gt : i0 < kk := by
      by_cases h : I'.Nonempty
      · exact (hkk_I h).1
      · rw [hkk, dif_neg h]; omega
    have hll_gt : j0 < ll := by
      by_cases h : J'.Nonempty
      · exact (hll_J h).1
      · rw [hll, dif_neg h]; omega
    have hamem : I'.Nonempty → (kk, j0) ∈ successors lam (i0, j0) := fun h => by
      rw [X7T_succ_eq]
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      refine ⟨kk, Finset.mem_Ico.mpr ⟨hkk_gt, ?_⟩, rfl⟩
      exact YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem (hkk_I h).2 hj0s hrs)
    have hbmem : J'.Nonempty → (i0, ll) ∈ successors lam (i0, j0) := fun h => by
      rw [X7T_succ_eq]
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨ll, Finset.mem_Ico.mpr ⟨hll_gt, ?_⟩, rfl⟩
      exact YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem hi0r (hll_J h).2 hrs)
    have hne_succ : successors lam (i0, j0) ≠ ∅ := by
      by_cases h : i0 < r
      · exact Finset.ne_empty_of_mem (hamem ⟨r, hrI' h⟩)
      · have : j0 < s := by omega
        exact Finset.ne_empty_of_mem (hbmem ⟨s, hsJ' this⟩)
    -- nonvanishing of the products
    have hPr : ∀ K : Finset ℕ, (∀ i ∈ K, i < r) → ∏ i ∈ K, rowGap lam x y i r s ≠ 0 := by
      intro K hK
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => (hrg_pos i (hK i hi)).ne')
    have hPc : ∀ K : Finset ℕ, (∀ j ∈ K, j < s) → ∏ j ∈ K, colGap lam x y j r s ≠ 0 := by
      intro K hK
      exact Finset.prod_ne_zero_iff.mpr (fun j hj => (hcg_pos j (hK j hj)).ne')
    have hIr : ∀ i ∈ I.erase r, i < r := fun i hi => by
      have h1 := Finset.mem_erase.mp hi; have := hI i h1.2; omega
    have hJs : ∀ j ∈ J.erase s, j < s := fun j hj => by
      have h1 := Finset.mem_erase.mp hj; have := hJ j h1.2; omega
    have hI'r' : ∀ i ∈ I'.erase r, i < r := fun i hi => by
      have h1 := Finset.mem_erase.mp hi
      exact hIr i (Finset.mem_erase.mpr ⟨h1.1, Finset.mem_of_mem_erase h1.2⟩)
    have hJ's' : ∀ j ∈ J'.erase s, j < s := fun j hj => by
      have h1 := Finset.mem_erase.mp hj
      exact hJs j (Finset.mem_erase.mpr ⟨h1.1, Finset.mem_of_mem_erase h1.2⟩)
    -- values at the two distinguished successors
    have hWa : moveWeight x y (i0, j0) (kk, j0) *
        walkEval (successors lam) x y f (kk, j0) (fun tail => ev I J ((i0, j0) :: tail)) =
        rowGap lam x y i0 r s *
          (((∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
          ((∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s))) := by
      rw [hdown kk hkk_gt]
      by_cases h : I'.Nonempty
      · have hk := hkk_I h
        rw [hkk_spec h] at hk ⊢
        rw [ih (I'.min' h) j0 I' J (I'.min'_mem h) (hrI' (hI'r h))
          (fun i hi => ⟨I'.min'_le i hi, (hI i (Finset.mem_of_mem_erase hi)).2⟩) hj0 hsJ hJ
          (by omega)]
        have hmw : moveWeight x y (i0, j0) (I'.min' h, j0) = x (I'.min' h) := by
          simp [moveWeight]
        rw [hmw]
        have hi0Ir : i0 ∈ I.erase r := Finset.mem_erase.mpr ⟨by omega, hi0⟩
        rw [← Finset.mul_prod_erase I' x (I'.min'_mem h),
          ← Finset.mul_prod_erase (I.erase r) (fun i => rowGap lam x y i r s) hi0Ir,
          Finset.erase_right_comm (s := I) (a := r) (b := i0), ← hI'def]
        have h1 := hPr _ hI'r'
        have h2 := hPc _ hJs
        have h3 := (hrg_pos i0 (by omega)).ne'
        field_simp
      · rw [hdown0 kk (fun h' => absurd h' h), mul_zero]
        have : i0 = r := by
          by_contra hne; exact h ⟨r, hrI' (by omega)⟩
        rw [this, hrg_r, zero_mul]
    have hWb : moveWeight x y (i0, j0) (i0, ll) *
        walkEval (successors lam) x y f (i0, ll) (fun tail => ev I J ((i0, j0) :: tail)) =
        colGap lam x y j0 r s *
          (((∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
          ((∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s))) := by
      rw [hright ll hll_gt]
      by_cases h : J'.Nonempty
      · have hl := hll_J h
        rw [hll_spec h] at hl ⊢
        rw [ih i0 (J'.min' h) I J' hi0 hrI hI (J'.min'_mem h) (hsJ' (hJ's h))
          (fun j hj => ⟨J'.min'_le j hj, (hJ j (Finset.mem_of_mem_erase hj)).2⟩)
          (by omega)]
        have hmw : moveWeight x y (i0, j0) (i0, J'.min' h) = y (J'.min' h) := by
          have : J'.min' h ≠ j0 := by omega
          simp [moveWeight, this]
        rw [hmw]
        have hj0Js : j0 ∈ J.erase s := Finset.mem_erase.mpr ⟨by omega, hj0⟩
        rw [← Finset.mul_prod_erase J' y (J'.min'_mem h),
          ← Finset.mul_prod_erase (J.erase s) (fun j => colGap lam x y j r s) hj0Js,
          Finset.erase_right_comm (s := J) (a := s) (b := j0), ← hJ'def]
        have h1 := hPc _ hJ's'
        have h2 := hPr _ hIr
        have h3 := (hcg_pos j0 (by omega)).ne'
        field_simp
      · rw [hright0 ll (fun h' => absurd h' h), mul_zero]
        have : j0 = s := by
          by_contra hne; exact h ⟨s, hsJ' (by omega)⟩
        rw [this, hcg_s, zero_mul]
    -- denominators
    have hH : (∑ k ∈ Finset.Ico (i0 + 1) (lam.colLen j0), x k) +
        ∑ l ∈ Finset.Ico (j0 + 1) (lam.rowLen i0), y l =
        rowGap lam x y i0 r s + colGap lam x y j0 r s := by
      have h1 : r + 1 ≤ lam.colLen j0 :=
        YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem le_rfl hj0s hrs)
      have h2 : s + 1 ≤ lam.rowLen i0 :=
        YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem hi0r le_rfl hrs)
      unfold rowGap colGap
      rw [← Finset.sum_Ico_consecutive x (show i0 + 1 ≤ r + 1 by omega) h1,
        ← Finset.sum_Ico_consecutive y (show j0 + 1 ≤ s + 1 by omega) h2]
      ring
    have hHpos : 0 < rowGap lam x y i0 r s + colGap lam x y j0 r s := by
      by_cases h : i0 < r
      · have := hrg_pos i0 h; have := hcg_nn j0; linarith
      · have h' : j0 < s := by omega
        have := hcg_pos j0 h'; have := hrg_nn i0; linarith
    simp only [walkEval]
    rw [if_neg hne_succ, X7T_denom lam x y i0 j0, hH]
    simp only [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    have hab : (kk, j0) ≠ (i0, ll) := by
      intro h; simp only [Prod.mk.injEq] at h; omega
    rw [Finset.sum_eq_add (kk, j0) (i0, ll) hab]
    · rw [hWa, hWb, ← add_mul, mul_div_cancel_left₀ _ hHpos.ne']
      simp only [← hI'def, ← hJ'def]
      ring
    · intro c hc hne
      rw [X7T_succ_eq] at hc
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at hc
      rcases hc with ⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨l, ⟨hl1, hl2⟩, rfl⟩
      · rw [hdown k (by omega), hdown0 k (fun h hk => hne.1 (by rw [hkk_spec h, hk])), mul_zero]
      · rw [hright l (by omega), hright0 l (fun h hl => hne.2 (by rw [hll_spec h, hl])),
          mul_zero]
    · intro hnot
      by_cases h : I'.Nonempty
      · exact absurd (hamem h) hnot
      · rw [hdown kk hkk_gt, hdown0 kk (fun h' => absurd h' h), mul_zero]
    · intro hnot
      by_cases h : J'.Nonempty
      · exact absurd (hbmem h) hnot
      · rw [hright ll hll_gt, hright0 ll (fun h' => absurd h' h), mul_zero]

theorem X7T_card (lam : YoungDiagram) (r s : ℕ) (hrs : (r, s) ∈ lam) :
    r + s ≤ lam.card := by
  have hsub : (Finset.range (r + 1) ×ˢ Finset.range (s + 1)) ⊆ lam.cells := by
    rintro ⟨a, b⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    rw [YoungDiagram.mem_cells]
    exact lam.up_left_mem (by omega) (by omega) hrs
  have := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at this
  have : r + s ≤ (r + 1) * (s + 1) := by nlinarith
  unfold YoungDiagram.card
  omega


theorem X7T_congr2 (lam : YoungDiagram) (x y : ℕ → ℝ) : ∀ (f : ℕ) (z : Cell) (e1 e2 : List Cell → ℝ),
    (∀ p : List Cell, List.IsChain (· ≤ ·) (z :: p) → e1 (z :: p) = e2 (z :: p)) →
    walkEval (successors lam) x y f z e1 = walkEval (successors lam) x y f z e2 := by
  intro f
  induction f with
  | zero =>
    intro z e1 e2 h
    simp only [walkEval, h [] (by simp)]
  | succ f ih =>
    intro z e1 e2 h
    simp only [walkEval]
    split_ifs
    · exact h [] (by simp)
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      congr 1
      apply ih
      intro p hp
      apply h (t :: p)
      exact List.isChain_cons_cons.mpr ⟨X7T_succ_le ht, hp⟩

theorem X7T_lin (lam : YoungDiagram) (x y : ℕ → ℝ) {ι : Type} (K : Finset ι) :
    ∀ (f : ℕ) (z : Cell) (e : ι → List Cell → ℝ),
    walkEval (successors lam) x y f z (fun p => ∑ k ∈ K, e k p) =
      ∑ k ∈ K, walkEval (successors lam) x y f z (e k) := by
  intro f
  induction f with
  | zero =>
    intro z e
    simp only [walkEval]
    split_ifs
    · rfl
    · simp
  | succ f ih =>
    intro z e
    simp only [walkEval]
    split_ifs
    · rfl
    · have h1 : ∀ t, walkEval (successors lam) x y f t
          (fun tail => ∑ k ∈ K, e k (z :: tail)) =
          ∑ k ∈ K, walkEval (successors lam) x y f t (fun tail => e k (z :: tail)) :=
        fun t => ih t (fun k tail => e k (z :: tail))
      simp only [h1, Finset.mul_sum]
      exact Finset.sum_comm

theorem X7T_chain_le_last : ∀ (z : Cell) (p : List Cell), List.IsChain (· ≤ ·) (z :: p) →
    ∀ a ∈ z :: p, z ≤ a ∧ a ≤ (z :: p).getLast (List.cons_ne_nil _ _) := by
  intro z p
  induction p generalizing z with
  | nil =>
    intro _ a ha
    simp only [List.mem_singleton] at ha
    subst ha
    simp
  | cons t p ih =>
    intro hc a ha
    have hzt := (List.isChain_cons_cons.mp hc).1
    have hrest := ih t (List.isChain_cons_cons.mp hc).2
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨le_rfl, le_trans hzt (hrest t (List.mem_cons_self ..)).2⟩
    · have := hrest a ha
      exact ⟨le_trans hzt this.1, this.2⟩

/-- the admissible row sets from i0 to r -/
def X7T_S (i0 r : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc i0 r).powerset.filter (fun I => i0 ∈ I ∧ r ∈ I)

theorem X7T_mem_S {i0 r : ℕ} {I : Finset ℕ} :
    I ∈ X7T_S i0 r ↔ i0 ∈ I ∧ r ∈ I ∧ ∀ i ∈ I, i0 ≤ i ∧ i ≤ r := by
  simp only [X7T_S, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h3, fun i hi => Finset.mem_Icc.mp (h1 hi)⟩
  · rintro ⟨h2, h3, h1⟩
    exact ⟨fun i hi => Finset.mem_Icc.mpr (h1 i hi), h2, h3⟩

theorem X7T_decomp (r s : ℕ) (z : Cell) (p : List Cell) (hc : List.IsChain (· ≤ ·) (z :: p)) :
    (if (z :: p).getLast? = some (r, s) then (1 : ℝ) else 0) =
      ∑ I ∈ X7T_S z.1 r, ∑ J ∈ X7T_S z.2 s,
        (if (z :: p).toFinset.image Prod.fst = I ∧ (z :: p).toFinset.image Prod.snd = J
          then (1 : ℝ) else 0) := by
  have hle := X7T_chain_le_last z p hc
  set L := (z :: p).getLast (List.cons_ne_nil _ _) with hLdef
  have hLmem : L ∈ z :: p := List.getLast_mem _
  rw [List.getLast?_eq_getLast (List.cons_ne_nil _ _)]
  by_cases hL : L = (r, s)
  · rw [if_pos (by rw [← hLdef, hL])]
    have hrows : (z :: p).toFinset.image Prod.fst ∈ X7T_S z.1 r := by
      rw [X7T_mem_S]
      refine ⟨Finset.mem_image.mpr ⟨z, by simp, rfl⟩,
        Finset.mem_image.mpr ⟨L, List.mem_toFinset.mpr hLmem, by rw [hL]⟩, ?_⟩
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have := hle a (List.mem_toFinset.mp ha)
      rw [hL] at this
      exact ⟨(Prod.le_def.mp this.1).1, (Prod.le_def.mp this.2).1⟩
    have hcols : (z :: p).toFinset.image Prod.snd ∈ X7T_S z.2 s := by
      rw [X7T_mem_S]
      refine ⟨Finset.mem_image.mpr ⟨z, by simp, rfl⟩,
        Finset.mem_image.mpr ⟨L, List.mem_toFinset.mpr hLmem, by rw [hL]⟩, ?_⟩
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have := hle a (List.mem_toFinset.mp ha)
      rw [hL] at this
      exact ⟨(Prod.le_def.mp this.1).2, (Prod.le_def.mp this.2).2⟩
    simp only [ite_and]
    rw [Finset.sum_eq_single ((z :: p).toFinset.image Prod.fst)]
    · simp only [eq_self_iff_true, if_true, ite_true]
      rw [Finset.sum_ite_eq, if_pos hcols]
    · intro I _ hI
      rw [Finset.sum_eq_zero]
      intro J _
      rw [if_neg (Ne.symm hI)]
    · intro h; exact absurd hrows h
  · rw [if_neg (by rw [← hLdef]; intro h; exact hL (Option.some_injective _ h))]
    symm
    apply Finset.sum_eq_zero
    intro I hI
    apply Finset.sum_eq_zero
    intro J hJ
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [X7T_mem_S] at hI hJ
    apply hL
    have hL1 : L.1 ∈ I := by
      rw [← h1]; exact Finset.mem_image.mpr ⟨L, List.mem_toFinset.mpr hLmem, rfl⟩
    have hL2 : L.2 ∈ J := by
      rw [← h2]; exact Finset.mem_image.mpr ⟨L, List.mem_toFinset.mpr hLmem, rfl⟩
    have hr : r ∈ (z :: p).toFinset.image Prod.fst := by rw [h1]; exact hI.2.1
    have hs : s ∈ (z :: p).toFinset.image Prod.snd := by rw [h2]; exact hJ.2.1
    obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hr
    obtain ⟨b, hb, hbs⟩ := Finset.mem_image.mp hs
    have ha' := (Prod.le_def.mp (hle a (List.mem_toFinset.mp ha)).2).1
    have hb' := (Prod.le_def.mp (hle b (List.mem_toFinset.mp hb)).2).2
    have h3 := (hI.2.2 _ hL1).2
    have h4 := (hJ.2.2 _ hL2).2
    ext
    · simp only; omega
    · simp only; omega

theorem X7T_rowsum (x g : ℕ → ℝ) (r : ℕ) (hg : ∀ i < r, g i ≠ 0) :
    ∑ i0 ∈ Finset.range (r + 1), x i0 *
      ∑ I ∈ X7T_S i0 r, (∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, g i) =
    x r * ∏ i ∈ Finset.range r, (1 + x i / g i) := by
  have step1 : ∀ i0 ∈ Finset.range (r + 1), x i0 *
      ∑ I ∈ X7T_S i0 r, (∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, g i) =
      ∑ I ∈ X7T_S i0 r, (∏ i ∈ I, x i) / (∏ i ∈ I.erase r, g i) := by
    intro i0 _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun I hI => ?_)
    rw [← Finset.mul_prod_erase I x (X7T_mem_S.mp hI).1, mul_div_assoc]
  rw [Finset.sum_congr rfl step1]
  have hdisj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint (fun i0 => X7T_S i0 r) := by
    intro i hi j hj hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro I h1 h2
    rw [X7T_mem_S] at h1 h2
    have a := h1.2.2 j h2.1
    have b := h2.2.2 i h1.1
    exact hij (le_antisymm a.1 b.1)
  rw [← Finset.sum_biUnion hdisj]
  have hU : (Finset.range (r + 1)).biUnion (fun i0 => X7T_S i0 r) =
      (Finset.range (r + 1)).powerset.filter (fun I => r ∈ I) := by
    ext I
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset, Finset.mem_range]
    constructor
    · rintro ⟨i0, hi0, hI⟩
      rw [X7T_mem_S] at hI
      refine ⟨fun i hi => Finset.mem_range.mpr (by have := hI.2.2 i hi; omega), hI.2.1⟩
    · rintro ⟨hsub, hr⟩
      have hne : I.Nonempty := ⟨r, hr⟩
      refine ⟨I.min' hne, ?_, ?_⟩
      · have := Finset.mem_range.mp (hsub (I.min'_mem hne)); omega
      · rw [X7T_mem_S]
        refine ⟨I.min'_mem hne, hr, fun i hi => ⟨I.min'_le i hi, ?_⟩⟩
        have := Finset.mem_range.mp (hsub hi); omega
  rw [hU, Finset.sum_filter, Finset.range_add_one,
    Finset.sum_powerset_insert (Finset.notMem_range_self)]
  have h0 : ∑ t ∈ (Finset.range r).powerset,
      (if r ∈ t then (∏ i ∈ t, x i) / (∏ i ∈ t.erase r, g i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg]
    intro h
    exact Finset.notMem_range_self (Finset.mem_powerset.mp ht h)
  rw [h0, zero_add, Finset.prod_one_add, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have hrt : r ∉ t := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp ht h)
  rw [if_pos (Finset.mem_insert_self _ _), Finset.prod_insert hrt, Finset.erase_insert hrt,
    Finset.prod_div_distrib, mul_div_assoc]

theorem X7T_S_empty {i0 r : ℕ} (h : r < i0) : X7T_S i0 r = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro I hI
  rw [X7T_mem_S] at hI
  have := hI.2.2 i0 hI.1
  omega

theorem X7T_gaps_pos (lam : YoungDiagram) (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y)
    (r s : ℕ) (hc : (r, s) ∈ corners lam) :
    (∀ i, i < r → 0 < rowGap lam x y i r s) ∧ (∀ j, j < s → 0 < colGap lam x y j r s) := by
  obtain ⟨hrs, hcol, hrow⟩ := X7T_corner_facts hc
  obtain ⟨hx, hy⟩ := hpos
  have hr0 : r < lam.colLen 0 :=
    YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem le_rfl (Nat.zero_le s) hrs)
  have hs0 : s < lam.rowLen 0 :=
    YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem (Nat.zero_le r) le_rfl hrs)
  have hxn : ∀ k, k < lam.colLen 0 → 0 ≤ x k := fun k hk => (hx k hk).le
  have hyn : ∀ l, l < lam.rowLen 0 → 0 ≤ y l := fun l hl => (hy l hl).le
  constructor
  · intro i hi
    unfold rowGap
    have h1 : x r ≤ ∑ k ∈ Finset.Ico (i + 1) (r + 1), x k :=
      Finset.single_le_sum (f := x) (fun k hk => by
        simp only [Finset.mem_Ico] at hk; exact hxn k (by omega))
        (by simp only [Finset.mem_Ico]; omega)
    have h2 : 0 ≤ ∑ l ∈ Finset.Ico (s + 1) (lam.rowLen i), y l := by
      apply Finset.sum_nonneg; intro l hl; simp only [Finset.mem_Ico] at hl
      have := lam.rowLen_anti 0 i (Nat.zero_le i)
      exact hyn l (by omega)
    have := hx r hr0
    linarith
  · intro j hj
    unfold colGap
    have h1 : y s ≤ ∑ l ∈ Finset.Ico (j + 1) (s + 1), y l :=
      Finset.single_le_sum (f := y) (fun l hl => by
        simp only [Finset.mem_Ico] at hl; exact hyn l (by omega))
        (by simp only [Finset.mem_Ico]; omega)
    have h2 : 0 ≤ ∑ k ∈ Finset.Ico (r + 1) (lam.colLen j), x k := by
      apply Finset.sum_nonneg; intro k hk; simp only [Finset.mem_Ico] at hk
      have := lam.colLen_anti 0 j (Nat.zero_le j)
      exact hxn k (by omega)
    have := hy s hs0
    linarith

end WeldedPath.YoungCounts

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open WeldedPath.YoungCounts in
theorem WeldedPath.YoungCounts.weightedHookWalk (lam : YoungDiagram) (hne : lam.cells.Nonempty)
    (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y) (c : Cell) (hc : c ∈ corners lam) :
    terminalProb lam (successors lam) x y c =
      cornerWeight lam x y c.1 c.2 / totalWeight lam x y := by
  obtain ⟨r, s⟩ := c
  obtain ⟨hrs, hcol, hrow⟩ := X7T_corner_facts hc
  obtain ⟨hrg, hcg⟩ := X7T_gaps_pos lam x y hpos r s hc
  have hcard := X7T_card lam r s hrs
  set ev : Finset ℕ → Finset ℕ → List Cell → ℝ := fun I J p =>
    if p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J then 1 else 0 with hev
  have hW : ∀ z ∈ lam.cells,
      walkEval (successors lam) x y lam.card z
        (fun p => if p.getLast? = some (r, s) then 1 else 0) =
      (∑ I ∈ X7T_S z.1 r, (∏ i ∈ I.erase z.1, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
      (∑ J ∈ X7T_S z.2 s, (∏ j ∈ J.erase z.2, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by
    intro z _
    obtain ⟨i0, j0⟩ := z
    rw [X7T_congr2 lam x y _ (i0, j0) _ (fun p => ∑ I ∈ X7T_S i0 r, ∑ J ∈ X7T_S j0 s, ev I J p)
      (fun p hp => X7T_decomp r s (i0, j0) p hp)]
    have h1 := X7T_lin lam x y (X7T_S i0 r) lam.card (i0, j0)
      (fun I p => ∑ J ∈ X7T_S j0 s, ev I J p)
    rw [h1, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun I hI => ?_)
    have h2 := X7T_lin lam x y (X7T_S j0 s) lam.card (i0, j0) (fun J p => ev I J p)
    rw [h2]
    refine Finset.sum_congr rfl (fun J hJ => ?_)
    rw [X7T_mem_S] at hI hJ
    exact X7T_main lam x y hpos r s hc ev (fun I J p h => if_pos h) (fun I J p h => if_neg h)
      lam.card i0 j0 I J hI.1 hI.2.1 hI.2.2 hJ.1 hJ.2.1 hJ.2.2 (by omega)
  unfold terminalProb
  rw [Finset.sum_congr rfl (fun z hz => by rw [hW z hz])]
  set AR : ℕ → ℝ := fun i0 => ∑ I ∈ X7T_S i0 r,
    (∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s) with hAR
  set AC : ℕ → ℝ := fun j0 => ∑ J ∈ X7T_S j0 s,
    (∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s) with hAC
  have hsub : (Finset.range (r + 1) ×ˢ Finset.range (s + 1)) ⊆ lam.cells := by
    rintro ⟨a, b⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    rw [YoungDiagram.mem_cells]
    exact lam.up_left_mem (by omega) (by omega) hrs
  have hR := X7T_rowsum x (fun i => rowGap lam x y i r s) r (fun i hi => (hrg i hi).ne')
  have hC := X7T_rowsum y (fun j => colGap lam x y j r s) s (fun j hj => (hcg j hj).ne')
  calc ∑ z ∈ lam.cells, x z.1 * y z.2 / totalWeight lam x y * (AR z.1 * AC z.2)
      = ∑ z ∈ Finset.range (r + 1) ×ˢ Finset.range (s + 1),
          x z.1 * y z.2 / totalWeight lam x y * (AR z.1 * AC z.2) := by
        symm
        apply Finset.sum_subset hsub
        intro z _ hz
        simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hz
        rcases hz with hz | hz
        · have : AR z.1 = 0 := by
            simp only [hAR]; rw [X7T_S_empty (by omega)]; simp
          rw [this]; ring
        · have : AC z.2 = 0 := by
            simp only [hAC]; rw [X7T_S_empty (by omega)]; simp
          rw [this]; ring
    _ = ∑ i0 ∈ Finset.range (r + 1), ∑ j0 ∈ Finset.range (s + 1),
          x i0 * y j0 / totalWeight lam x y * (AR i0 * AC j0) := Finset.sum_product _ _ _
    _ = (∑ i0 ∈ Finset.range (r + 1), x i0 * AR i0) *
          (∑ j0 ∈ Finset.range (s + 1), y j0 * AC j0) / totalWeight lam x y := by
        rw [Finset.sum_mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun i0 _ => ?_)
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun j0 _ => ?_)
        ring
    _ = cornerWeight lam x y r s / totalWeight lam x y := by
        rw [hR, hC]
        unfold cornerWeight
        ring

end
end

-- Accepted proof: ebf5ffa6-3bee-4d39-9ee8-cb962f91429e
section

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_walk_sum (next : Cell → Finset Cell) (x y : ℕ → ℝ) {ι : Type*} (S : Finset ι) :
    ∀ (fuel : ℕ) (z : Cell) (f : ι → List Cell → ℝ),
      walkEval next x y fuel z (fun p => ∑ c ∈ S, f c p) =
        ∑ c ∈ S, walkEval next x y fuel z (f c) := by
  intro fuel
  induction fuel with
  | zero =>
    intro z f
    simp only [walkEval]
    split_ifs <;> simp
  | succ n ih =>
    intro z f
    simp only [walkEval]
    split_ifs with h
    · rfl
    · have := fun t => ih t (fun c tail => f c (z :: tail))
      simp only [this, Finset.mul_sum]
      exact Finset.sum_comm

theorem X7hk_mem_lam {lam : YoungDiagram} {t : Cell} (ht : t ∈ lam) :
    t.1 < lam.colLen 0 ∧ t.2 < lam.rowLen 0 := by
  have h1 : t.1 < lam.colLen t.2 := YoungDiagram.mem_iff_lt_colLen.mp (by simpa using ht)
  have h2 : t.2 < lam.rowLen t.1 := YoungDiagram.mem_iff_lt_rowLen.mp (by simpa using ht)
  exact ⟨lt_of_lt_of_le h1 (lam.colLen_anti 0 t.2 (Nat.zero_le _)),
    lt_of_lt_of_le h2 (lam.rowLen_anti 0 t.1 (Nat.zero_le _))⟩

theorem X7hk_succ_empty {lam : YoungDiagram} {z : Cell} (hz : z ∈ lam.cells)
    (h : successors lam z = ∅) : z ∈ corners lam := by
  simp only [corners, Finset.mem_filter]
  refine ⟨hz, ?_, ?_⟩
  · intro hm
    have : (z.1 + 1, z.2) ∈ successors lam z := by
      simp [successors, hm]
    simp [h] at this
  · intro hm
    have : (z.1, z.2 + 1) ∈ successors lam z := by
      simp [successors, hm]
    simp [h] at this

theorem X7hk_walk_one (lam : YoungDiagram) :
    ∀ (fuel : ℕ) (z : Cell), z ∈ lam.cells →
      lam.colLen 0 + lam.rowLen 0 ≤ fuel + z.1 + z.2 + 2 →
      ∀ E : List Cell → ℝ, (∀ l c, c ∈ corners lam → E (l ++ [c]) = 1) →
        walkEval (successors lam) (fun _ => 1) (fun _ => 1) fuel z E = 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro z hz hf E hE
    have hs : successors lam z = ∅ := by
      ext t
      simp only [successors, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro ht h
      have := X7hk_mem_lam (lam := lam) ht
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    simp only [walkEval, hs, if_true]
    simpa using hE [] z (X7hk_succ_empty hz hs)
  | succ n ih =>
    intro z hz hf E hE
    simp only [walkEval]
    split_ifs with h
    · simpa using hE [] z (X7hk_succ_empty hz h)
    · have hne : (successors lam z).Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      have hw : ∀ t u : Cell, moveWeight (fun _ => (1:ℝ)) (fun _ => 1) t u = 1 := by
        intro t u; simp [moveWeight]
      have hcard : ((successors lam z).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr hne).ne'
      have key : ∀ t ∈ successors lam z,
          walkEval (successors lam) (fun _ => 1) (fun _ => 1) n t (fun tail => E (z :: tail)) = 1 := by
        intro t ht
        simp only [successors, Finset.mem_filter] at ht
        apply ih t ht.1
        · rcases ht.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        · intro l c hc
          simpa using hE (z :: l) c hc
      rw [Finset.sum_congr rfl (fun t ht => by rw [key t ht])]
      simp only [hw, Finset.sum_const, nsmul_eq_mul, mul_one]
      field_simp

theorem X7hk_card_bound (lam : YoungDiagram) : lam.colLen 0 + lam.rowLen 0 ≤ lam.card + 1 := by
  let A := (Finset.range (lam.rowLen 0)).image fun j => ((0 : ℕ), j)
  let B := (Finset.Ico 1 (lam.colLen 0)).image fun i => (i, (0 : ℕ))
  have hA : A.card = lam.rowLen 0 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]; simp
  have hB : B.card = lam.colLen 0 - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]; simp
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [A, B, Finset.mem_image, Finset.mem_range, Finset.mem_Ico] at ha hb
    obtain ⟨j, -, rfl⟩ := ha
    obtain ⟨i, hi, he⟩ := hb
    simp only [Prod.mk.injEq] at he
    omega
  have hsub : A ∪ B ⊆ lam.cells := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · simp only [A, Finset.mem_image, Finset.mem_range] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
    · simp only [B, Finset.mem_image, Finset.mem_Ico] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact YoungDiagram.mem_iff_lt_colLen.mpr hi.2
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hA, hB] at this
  unfold YoungDiagram.card
  omega

/-- Total terminal mass of the unit-weight walk is one. -/
theorem X7hk_total (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ∑ c ∈ corners lam, terminalProb lam (successors lam) (fun _ => 1) (fun _ => 1) c = 1 := by
  unfold terminalProb
  rw [Finset.sum_comm]
  have hW : totalWeight lam (fun _ => (1:ℝ)) (fun _ => 1) = lam.card := by
    simp [totalWeight, YoungDiagram.card]
  have hn : (lam.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have : ∀ z ∈ lam.cells,
      ∑ c ∈ corners lam, (1 * 1 / totalWeight lam (fun _ => (1:ℝ)) (fun _ => 1)) *
        walkEval (successors lam) (fun _ => 1) (fun _ => 1) lam.card z
          (fun p => if p.getLast? = some c then 1 else 0) = 1 / lam.card := by
    intro z hz
    rw [← Finset.mul_sum, ← X7hk_walk_sum, X7hk_walk_one lam lam.card z hz, hW]
    · simp
    · have := X7hk_card_bound lam; omega
    · intro l c hc
      simp [Finset.sum_ite_eq', hc]
  rw [Finset.sum_congr rfl this]
  simp only [Finset.sum_const, nsmul_eq_mul]
  unfold YoungDiagram.card at hn ⊢
  field_simp

end WeldedPath.YoungCounts

end

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_arm (lam : YoungDiagram) (i j : ℕ) :
    (lam.cells.filter fun a => a.1 = i ∧ j < a.2).card = lam.rowLen i - (j + 1) := by
  have : (lam.cells.filter fun a => a.1 = i ∧ j < a.2) =
      (Finset.Ico (j + 1) (lam.rowLen i)).image fun l => (i, l) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl, hb⟩
      exact ⟨b, ⟨hb, YoungDiagram.mem_iff_lt_rowLen.mp h⟩, rfl, rfl⟩
    · rintro ⟨l, ⟨h1, h2⟩, rfl, rfl⟩
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr h2, rfl, h1⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

theorem X7hk_leg (lam : YoungDiagram) (i j : ℕ) :
    (lam.cells.filter fun a => a.2 = j ∧ i < a.1).card = lam.colLen j - (i + 1) := by
  have : (lam.cells.filter fun a => a.2 = j ∧ i < a.1) =
      (Finset.Ico (i + 1) (lam.colLen j)).image fun k => (k, j) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl, hb⟩
      exact ⟨a, ⟨hb, YoungDiagram.mem_iff_lt_colLen.mp h⟩, rfl, rfl⟩
    · rintro ⟨l, ⟨h1, h2⟩, rfl, rfl⟩
      exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr h2, rfl, h1⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

theorem X7hk_hook (lam : YoungDiagram) (i j : ℕ) :
    hook lam (i, j) = 1 + (lam.rowLen i - (j + 1)) + (lam.colLen j - (i + 1)) := by
  simp only [hook, WeldedPath.YoungCounts.cellHook]
  rw [X7hk_arm, X7hk_leg]

theorem X7hk_corner {lam : YoungDiagram} {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (r, s) ∈ lam ∧ lam.colLen s = r + 1 ∧ lam.rowLen r = s + 1 := by
  simp only [corners, Finset.mem_filter] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  have hm : (r, s) ∈ lam := by simpa using h0
  refine ⟨hm, ?_, ?_⟩
  · have a := YoungDiagram.mem_iff_lt_colLen.mp hm
    have b : ¬ r + 1 < lam.colLen s := fun h => h1 (by simpa using YoungDiagram.mem_iff_lt_colLen.mpr h)
    omega
  · have a := YoungDiagram.mem_iff_lt_rowLen.mp hm
    have b : ¬ s + 1 < lam.rowLen r := fun h => h2 (by simpa using YoungDiagram.mem_iff_lt_rowLen.mpr h)
    omega

/-- Column cells above a corner have hook ≥ 2 and rowGap = hook - 1. -/
theorem X7hk_col {lam : YoungDiagram} {r s i : ℕ} (hc : (r, s) ∈ corners lam) (hi : i < r) :
    2 ≤ hook lam (i, s) ∧
      rowGap lam (fun _ => (1:ℝ)) (fun _ => 1) i r s = (hook lam (i, s) : ℝ) - 1 := by
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  have hin : (i, s) ∈ lam := lam.isLowerSet (show (i, s) ≤ (r, s) from ⟨hi.le, le_rfl⟩) hm
  have hl := YoungDiagram.mem_iff_lt_rowLen.mp hin
  rw [X7hk_hook, hcol]
  refine ⟨by omega, ?_⟩
  simp only [rowGap, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have e1 : r + 1 - (i + 1) = r - i := by omega
  rw [e1]
  push_cast
  ring

theorem X7hk_row {lam : YoungDiagram} {r s j : ℕ} (hc : (r, s) ∈ corners lam) (hj : j < s) :
    2 ≤ hook lam (r, j) ∧
      colGap lam (fun _ => (1:ℝ)) (fun _ => 1) j r s = (hook lam (r, j) : ℝ) - 1 := by
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  have hin : (r, j) ∈ lam := lam.isLowerSet (show (r, j) ≤ (r, s) from ⟨le_rfl, hj.le⟩) hm
  have hl := YoungDiagram.mem_iff_lt_colLen.mp hin
  rw [X7hk_hook, hrow]
  refine ⟨by omega, ?_⟩
  simp only [colGap, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have e1 : s + 1 - (j + 1) = s - j := by omega
  rw [e1]
  push_cast
  ring

/-- Clause (3) over ℝ. -/
theorem X7hk_clause3R (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ∑ z ∈ corners lam, (1 / (lam.card : ℝ)) *
      (∏ i ∈ Finset.range z.1,
        (hook lam (i, z.2) : ℝ) / ((hook lam (i, z.2) : ℝ) - 1)) *
      ∏ j ∈ Finset.range z.2,
        (hook lam (z.1, j) : ℝ) / ((hook lam (z.1, j) : ℝ) - 1) = 1 := by
  refine Eq.trans (Finset.sum_congr rfl ?_) (X7hk_total lam hne)
  rintro ⟨r, s⟩ hc
  have hpos : PositiveWeights lam (fun _ => (1:ℝ)) (fun _ => 1) := ⟨fun _ _ => one_pos, fun _ _ => one_pos⟩
  rw [weightedHookWalk lam hne _ _ hpos (r, s) hc]
  have hW : totalWeight lam (fun _ => (1:ℝ)) (fun _ => 1) = lam.card := by
    simp [totalWeight, YoungDiagram.card]
  rw [hW]
  simp only [cornerWeight, one_mul]
  have hP : (∏ i ∈ Finset.range r, (hook lam (i, s) : ℝ) / ((hook lam (i, s) : ℝ) - 1)) =
      ∏ i ∈ Finset.range r, (1 + 1 / rowGap lam (fun _ => (1:ℝ)) (fun _ => 1) i r s) := by
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨h2, hg⟩ := X7hk_col hc (Finset.mem_range.mp hi)
    rw [hg]
    have : (hook lam (i, s) : ℝ) - 1 ≠ 0 := by
      have : (2:ℝ) ≤ hook lam (i, s) := by exact_mod_cast h2
      linarith
    field_simp
    ring
  have hQ : (∏ j ∈ Finset.range s, (hook lam (r, j) : ℝ) / ((hook lam (r, j) : ℝ) - 1)) =
      ∏ j ∈ Finset.range s, (1 + 1 / colGap lam (fun _ => (1:ℝ)) (fun _ => 1) j r s) := by
    apply Finset.prod_congr rfl
    intro j hj
    obtain ⟨h2, hg⟩ := X7hk_row hc (Finset.mem_range.mp hj)
    rw [hg]
    have : (hook lam (r, j) : ℝ) - 1 ≠ 0 := by
      have : (2:ℝ) ≤ hook lam (r, j) := by exact_mod_cast h2
      linarith
    field_simp
    ring
  simp only at hP hQ ⊢
  rw [hP, hQ]
  ring

/-- Clause (3) over ℚ. -/
theorem X7hk_clause3 (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
      (∏ i ∈ Finset.range z.1,
        (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
      ∏ j ∈ Finset.range z.2,
        (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1) = 1 := by
  have := X7hk_clause3R lam hne
  apply (Rat.cast_injective (α := ℝ))
  push_cast
  exact this

end WeldedPath.YoungCounts

end

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_prod_cross {M : Type*} [CommMonoid M] (T : Finset Cell) (r s : ℕ) (g : Cell → M)
    (hA : ∀ i < r, (i, s) ∈ T) (hB : ∀ j < s, (r, j) ∈ T)
    (hT : ∀ z ∈ T, ¬(z.1 ≠ r ∧ z.2 ≠ s) → (z.1 < r ∧ z.2 = s) ∨ (z.1 = r ∧ z.2 < s)) :
    ∏ z ∈ T, g z = (∏ i ∈ Finset.range r, g (i, s)) * (∏ j ∈ Finset.range s, g (r, j)) *
      ∏ z ∈ T.filter (fun z => z.1 ≠ r ∧ z.2 ≠ s), g z := by
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun z => z.1 ≠ r ∧ z.2 ≠ s), mul_comm]
  congr 1
  have hE : T.filter (fun z => ¬(z.1 ≠ r ∧ z.2 ≠ s)) =
      (Finset.range r).image (fun i => (i, s)) ∪ (Finset.range s).image (fun j => (r, j)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hz, hn⟩
      rcases hT _ hz hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨a, h1, rfl, h2.symm⟩
      · exact Or.inr ⟨b, h2, h1.symm, rfl⟩
    · rintro (⟨i, hi, rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩)
      · exact ⟨hA i hi, by simp⟩
      · exact ⟨hB j hj, by simp⟩
  rw [hE, Finset.prod_union, Finset.prod_image (fun a _ b _ h => by simpa using h),
    Finset.prod_image (fun a _ b _ h => by simpa using h)]
  rw [Finset.disjoint_left]
  rintro ⟨a, b⟩ h1 h2
  simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at h1 h2
  obtain ⟨i, hi, rfl, rfl⟩ := h1
  obtain ⟨j, hj, h3, rfl⟩ := h2
  omega

theorem X7hk_hook_ge (lam : YoungDiagram) (z : Cell) : 1 ≤ hook lam z := by
  simp only [hook, WeldedPath.YoungCounts.cellHook]; omega

/-- Cross structure of the noncorners around a corner. -/
theorem X7hk_noncorner_cross {lam : YoungDiagram} {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (∀ i < r, (i, s) ∈ noncorners lam) ∧ (∀ j < s, (r, j) ∈ noncorners lam) ∧
    (∀ z ∈ noncorners lam, ¬(z.1 ≠ r ∧ z.2 ≠ s) → (z.1 < r ∧ z.2 = s) ∨ (z.1 = r ∧ z.2 < s)) := by
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h1 : (i + 1, s) ∈ lam := lam.isLowerSet (show (i + 1, s) ≤ (r, s) from ⟨hi, le_rfl⟩) hm
    have h0 : (i, s) ∈ lam := lam.isLowerSet (show (i, s) ≤ (r, s) from ⟨hi.le, le_rfl⟩) hm
    simp only [noncorners, corners, Finset.mem_sdiff, Finset.mem_filter]
    exact ⟨by simpa using h0, fun h => h.2.1 (by simpa using h1)⟩
  · intro j hj
    have h1 : (r, j + 1) ∈ lam := lam.isLowerSet (show (r, j + 1) ≤ (r, s) from ⟨le_rfl, hj⟩) hm
    have h0 : (r, j) ∈ lam := lam.isLowerSet (show (r, j) ≤ (r, s) from ⟨le_rfl, hj.le⟩) hm
    simp only [noncorners, corners, Finset.mem_sdiff, Finset.mem_filter]
    exact ⟨by simpa using h0, fun h => h.2.2 (by simpa using h1)⟩
  · rintro ⟨a, b⟩ hz hn
    simp only [noncorners, Finset.mem_sdiff] at hz
    have hz1 : (a, b) ∈ lam := by simpa using hz.1
    have hne : (a, b) ≠ (r, s) := fun h => hz.2 (h ▸ hc)
    simp only [ne_eq, not_and, not_not] at hn
    by_cases ha : a = r
    · subst ha
      have := YoungDiagram.mem_iff_lt_rowLen.mp hz1
      have : b ≠ s := fun h => hne (by rw [h])
      right; constructor <;> omega
    · have hb := hn ha
      subst hb
      have := YoungDiagram.mem_iff_lt_colLen.mp hz1
      left; constructor <;> omega

/-- Clause (4). -/
theorem X7hk_clause4 (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    (lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) =
      ∑ z ∈ corners lam,
        (∏ i ∈ Finset.range z.1, (hook lam (i, z.2) : ℚ)) *
        (∏ j ∈ Finset.range z.2, (hook lam (z.1, j) : ℚ)) *
        ∏ u ∈ offCross lam z.1 z.2, ((hook lam u : ℚ) - 1) := by
  have h3 := X7hk_clause3 lam hne
  have hn : (lam.card : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have e : (lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) =
      (lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) *
        ∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
          (∏ i ∈ Finset.range z.1,
            (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
          ∏ j ∈ Finset.range z.2,
            (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1) := by
    rw [h3, mul_one]
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨r, s⟩ hc
  dsimp only
  obtain ⟨hA, hB, hT⟩ := X7hk_noncorner_cross hc
  rw [X7hk_prod_cross _ r s (fun z => (hook lam z : ℚ) - 1) hA hB hT]
  simp only [offCross]
  have hP : (∏ i ∈ Finset.range r, ((hook lam (i, s) : ℚ) - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have := (X7hk_col hc (Finset.mem_range.mp hi)).1
    have : (2:ℚ) ≤ hook lam (i, s) := by exact_mod_cast this
    linarith
  have hQ : (∏ j ∈ Finset.range s, ((hook lam (r, j) : ℚ) - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    have := (X7hk_row hc (Finset.mem_range.mp hj)).1
    have : (2:ℚ) ≤ hook lam (r, j) := by exact_mod_cast this
    linarith
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  field_simp

theorem X7hk_mem_preds (lam mu : YoungDiagram) :
    mu ∈ oneBoxPredecessors lam ↔ mu.cells ⊆ lam.cells ∧ mu.cells.card + 1 = lam.card := by
  simp only [oneBoxPredecessors, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at ha
    exact ⟨ha.1, ha.2.1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨mu.cells, ?_⟩, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h1, h2, mu.isLowerSet⟩

/-- The diagram obtained by removing a corner. -/
def X7hk_rem (lam : YoungDiagram) (c : Cell) (hc : c ∈ corners lam) : YoungDiagram :=
  ⟨lam.cells.erase c, by
    intro a b hba ha
    have ha' : a ∈ lam.cells.erase c := ha
    rw [Finset.mem_erase] at ha'
    show b ∈ lam.cells.erase c
    rw [Finset.mem_erase]
    have hb : b ∈ lam.cells := lam.isLowerSet hba ha'.2
    refine ⟨?_, hb⟩
    rintro rfl
    apply ha'.1
    simp only [corners, Finset.mem_filter] at hc
    obtain ⟨-, h1, h2⟩ := hc
    obtain ⟨hb1, hb2⟩ := hba
    rcases Nat.lt_or_ge b.1 a.1 with h | h
    · exact absurd (lam.isLowerSet (show (b.1 + 1, b.2) ≤ a from ⟨h, hb2⟩) ha'.2) (by simpa using h1)
    rcases Nat.lt_or_ge b.2 a.2 with h' | h'
    · exact absurd (lam.isLowerSet (show (b.1, b.2 + 1) ≤ a from ⟨hb1, h'⟩) ha'.2) (by simpa using h2)
    exact Prod.ext (le_antisymm h hb1) (le_antisymm h' hb2)⟩

theorem X7hk_sum_preds (lam : YoungDiagram) (F : YoungDiagram → ℚ) :
    ∑ mu ∈ oneBoxPredecessors lam, F mu =
      ∑ c ∈ (corners lam).attach, F (X7hk_rem lam c.1 c.2) := by
  symm
  apply Finset.sum_bij (fun c _ => X7hk_rem lam c.1 c.2)
  · rintro ⟨c, hc⟩ -
    rw [X7hk_mem_preds]
    have hcl : c ∈ lam.cells := (Finset.mem_filter.mp hc).1
    refine ⟨Finset.erase_subset _ _, ?_⟩
    show (lam.cells.erase c).card + 1 = lam.cells.card
    rw [Finset.card_erase_of_mem hcl]
    have := Finset.card_pos.mpr ⟨c, hcl⟩
    omega
  · rintro ⟨c, hc⟩ - ⟨d, hd⟩ - h
    have h' : lam.cells.erase c = lam.cells.erase d := congrArg YoungDiagram.cells h
    have hcl : c ∈ lam.cells := (Finset.mem_filter.mp hc).1
    by_contra hne
    have hcd : c ≠ d := fun e => hne (Subtype.ext e)
    have : c ∈ lam.cells.erase d := Finset.mem_erase.mpr ⟨hcd, hcl⟩
    rw [← h'] at this
    simp at this
  · intro mu hmu
    rw [X7hk_mem_preds] at hmu
    obtain ⟨hsub, hcard⟩ := hmu
    have : (lam.cells \ mu.cells).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub]
      unfold YoungDiagram.card at hcard
      omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp this
    have hcl : c ∈ lam.cells := (Finset.mem_sdiff.mp (hc ▸ Finset.mem_singleton_self c)).1
    have hcm : c ∉ mu.cells := (Finset.mem_sdiff.mp (hc ▸ Finset.mem_singleton_self c)).2
    have hmu_eq : mu.cells = lam.cells.erase c := by
      ext z
      rw [Finset.mem_erase]
      constructor
      · intro hz
        exact ⟨fun e => hcm (e ▸ hz), hsub hz⟩
      · rintro ⟨hzc, hz⟩
        by_contra hzm
        have : z ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hz, hzm⟩
        rw [hc] at this
        exact hzc (Finset.mem_singleton.mp this)
    have hcor : c ∈ corners lam := by
      simp only [corners, Finset.mem_filter]
      refine ⟨hcl, ?_, ?_⟩
      · intro h
        have h1 : (c.1 + 1, c.2) ∈ mu.cells := by
          rw [hmu_eq, Finset.mem_erase]
          refine ⟨?_, by simpa using h⟩
          intro e; have := congrArg Prod.fst e; simp at this
        exact hcm (mu.isLowerSet (show c ≤ (c.1 + 1, c.2) from ⟨Nat.le_succ _, le_rfl⟩) h1)
      · intro h
        have h1 : (c.1, c.2 + 1) ∈ mu.cells := by
          rw [hmu_eq, Finset.mem_erase]
          refine ⟨?_, by simpa using h⟩
          intro e; have := congrArg Prod.snd e; simp at this
        exact hcm (mu.isLowerSet (show c ≤ (c.1, c.2 + 1) from ⟨le_rfl, Nat.le_succ _⟩) h1)
    refine ⟨⟨c, hcor⟩, Finset.mem_attach _ _, ?_⟩
    cases mu
    simp only [X7hk_rem] at hmu_eq ⊢
    subst hmu_eq
    rfl
  · intro _ _; rfl

/-- Hooks after removing a corner. -/
theorem X7hk_hook_rem (lam : YoungDiagram) {r s : ℕ} (hc : (r, s) ∈ corners lam) (z : Cell) :
    hook (X7hk_rem lam (r, s) hc) z + (if z.1 < r ∧ z.2 = s then 1 else 0) +
      (if z.1 = r ∧ z.2 < s then 1 else 0) = hook lam z := by
  have hcl : (r, s) ∈ lam.cells := (Finset.mem_filter.mp hc).1
  simp only [hook, WeldedPath.YoungCounts.cellHook, X7hk_rem,
    Finset.filter_erase]
  have e1 : ((lam.cells.filter fun a => a.1 = z.1 ∧ z.2 < a.2).erase (r, s)).card +
      (if z.1 = r ∧ z.2 < s then 1 else 0) =
      (lam.cells.filter fun a => a.1 = z.1 ∧ z.2 < a.2).card := by
    split_ifs with h
    · exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hcl, h.1.symm, h.2⟩)
    · rw [Finset.erase_eq_of_notMem]
      · rfl
      · intro hm
        exact h ⟨(Finset.mem_filter.mp hm).2.1.symm, (Finset.mem_filter.mp hm).2.2⟩
  have e2 : ((lam.cells.filter fun a => a.2 = z.2 ∧ z.1 < a.1).erase (r, s)).card +
      (if z.1 < r ∧ z.2 = s then 1 else 0) =
      (lam.cells.filter fun a => a.2 = z.2 ∧ z.1 < a.1).card := by
    split_ifs with h
    · exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hcl, h.2.symm, h.1⟩)
    · rw [Finset.erase_eq_of_notMem]
      · rfl
      · intro hm
        exact h ⟨(Finset.mem_filter.mp hm).2.2, (Finset.mem_filter.mp hm).2.1.symm⟩
  omega

/-- Hook products of λ and of λ minus a corner, as cross products. -/
theorem X7hk_hookProducts (lam : YoungDiagram) {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    let R := ∏ z ∈ (lam.cells.erase (r, s)).filter (fun z => z.1 ≠ r ∧ z.2 ≠ s), (hook lam z : ℚ)
    hookProduct lam = (∏ i ∈ Finset.range r, (hook lam (i, s) : ℚ)) *
        (∏ j ∈ Finset.range s, (hook lam (r, j) : ℚ)) * R ∧
    hookProduct (X7hk_rem lam (r, s) hc) = (∏ i ∈ Finset.range r, ((hook lam (i, s) : ℚ) - 1)) *
        (∏ j ∈ Finset.range s, ((hook lam (r, j) : ℚ) - 1)) * R := by
  intro R
  have hcl : (r, s) ∈ lam.cells := (Finset.mem_filter.mp hc).1
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  have hA : ∀ i < r, (i, s) ∈ lam.cells.erase (r, s) := by
    intro i hi
    rw [Finset.mem_erase]
    refine ⟨fun e => by simp at e; omega, ?_⟩
    simpa using lam.isLowerSet (show (i, s) ≤ (r, s) from ⟨hi.le, le_rfl⟩) hm
  have hB : ∀ j < s, (r, j) ∈ lam.cells.erase (r, s) := by
    intro j hj
    rw [Finset.mem_erase]
    refine ⟨fun e => by simp at e; omega, ?_⟩
    simpa using lam.isLowerSet (show (r, j) ≤ (r, s) from ⟨le_rfl, hj.le⟩) hm
  have hT : ∀ z ∈ lam.cells.erase (r, s), ¬(z.1 ≠ r ∧ z.2 ≠ s) →
      (z.1 < r ∧ z.2 = s) ∨ (z.1 = r ∧ z.2 < s) := by
    rintro ⟨a, b⟩ hz hn
    rw [Finset.mem_erase] at hz
    have hz1 : (a, b) ∈ lam := by simpa using hz.2
    simp only [ne_eq, not_and, not_not] at hn
    by_cases ha : a = r
    · subst ha
      have := YoungDiagram.mem_iff_lt_rowLen.mp hz1
      have : b ≠ s := fun h => hz.1 (by rw [h])
      right; constructor <;> omega
    · have hb := hn ha
      subst hb
      have := YoungDiagram.mem_iff_lt_colLen.mp hz1
      left; constructor <;> omega
  have hcs : hook lam (r, s) = 1 := by
    rw [X7hk_hook, hcol, hrow]; omega
  constructor
  · unfold hookProduct
    rw [← Finset.mul_prod_erase _ _ hcl, hcs, Nat.cast_one, one_mul]
    exact X7hk_prod_cross _ r s _ hA hB hT
  · unfold hookProduct
    show ∏ z ∈ lam.cells.erase (r, s), (hook (X7hk_rem lam (r, s) hc) z : ℚ) = _
    rw [X7hk_prod_cross _ r s _ hA hB hT]
    congr 1
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have := X7hk_hook_rem lam hc (i, s)
      have hi' := Finset.mem_range.mp hi
      simp only [hi', and_self, if_true, lt_irrefl, false_and, and_false, if_false, add_zero] at this
      have : (hook lam (i, s) : ℚ) = hook (X7hk_rem lam (r, s) hc) (i, s) + 1 := by
        exact_mod_cast (by omega : hook lam (i, s) = hook (X7hk_rem lam (r, s) hc) (i, s) + 1)
      rw [this]; ring
    · apply Finset.prod_congr rfl
      intro j hj
      have := X7hk_hook_rem lam hc (r, j)
      have hj' := Finset.mem_range.mp hj
      simp only [hj', and_self, if_true, lt_irrefl, false_and, and_false, true_and, if_false, zero_add, add_zero] at this
      have : (hook lam (r, j) : ℚ) = hook (X7hk_rem lam (r, s) hc) (r, j) + 1 := by
        exact_mod_cast (by omega : hook lam (r, j) = hook (X7hk_rem lam (r, s) hc) (r, j) + 1)
      rw [this]; ring
    · apply Finset.prod_congr rfl
      rintro ⟨a, b⟩ hz
      have hz' := (Finset.mem_filter.mp hz).2
      have := X7hk_hook_rem lam hc (a, b)
      simp only at hz' this
      have h1 : ¬(a < r ∧ b = s) := fun h => hz'.2 h.2
      have h2 : ¬(a = r ∧ b < s) := fun h => hz'.1 h.1
      simp only [h1, h2, if_false, add_zero] at this
      rw [this]

end WeldedPath.YoungCounts

end

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_nonzero (lam : YoungDiagram) {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (∏ i ∈ Finset.range r, ((hook lam (i, s) : ℚ) - 1)) ≠ 0 ∧
    (∏ j ∈ Finset.range s, ((hook lam (r, j) : ℚ) - 1)) ≠ 0 ∧
    (∏ z ∈ (lam.cells.erase (r, s)).filter (fun z => z.1 ≠ r ∧ z.2 ≠ s), (hook lam z : ℚ)) ≠ 0 ∧
    (∏ i ∈ Finset.range r, (hook lam (i, s) : ℚ)) ≠ 0 ∧
    (∏ j ∈ Finset.range s, (hook lam (r, j) : ℚ)) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [Finset.prod_ne_zero_iff]
  · intro i hi
    have := (X7hk_col hc (Finset.mem_range.mp hi)).1
    have : (2:ℚ) ≤ hook lam (i, s) := by exact_mod_cast this
    linarith
  · intro j hj
    have := (X7hk_row hc (Finset.mem_range.mp hj)).1
    have : (2:ℚ) ≤ hook lam (r, j) := by exact_mod_cast this
    linarith
  all_goals
    intro z _
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (X7hk_hook_ge lam _))

theorem X7hk_branching (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ((lam.card.factorial : ℚ) / hookProduct lam =
      ∑ mu ∈ oneBoxPredecessors lam, ((lam.card - 1).factorial : ℚ) / hookProduct mu) ∧
    ((∑ mu ∈ oneBoxPredecessors lam,
      (((lam.card - 1).factorial : ℚ) / (lam.card.factorial : ℚ)) *
        (hookProduct lam / hookProduct mu)) = 1) ∧
    ((∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
      (∏ i ∈ Finset.range z.1,
        (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
      ∏ j ∈ Finset.range z.2,
        (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1)) = 1) ∧
    ((lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) =
      ∑ z ∈ corners lam,
        (∏ i ∈ Finset.range z.1, (hook lam (i, z.2) : ℚ)) *
        (∏ j ∈ Finset.range z.2, (hook lam (z.1, j) : ℚ)) *
        ∏ u ∈ offCross lam z.1 z.2, ((hook lam u : ℚ) - 1)) := by
  have h3 := X7hk_clause3 lam hne
  obtain ⟨m, hm⟩ : ∃ m, lam.card = m + 1 :=
    ⟨lam.card - 1, by have := Finset.card_pos.mpr hne; unfold YoungDiagram.card; omega⟩
  refine ⟨?_, ?_, h3, X7hk_clause4 lam hne⟩
  · have e : (lam.card.factorial : ℚ) / hookProduct lam =
        (lam.card.factorial : ℚ) / hookProduct lam *
          ∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
            (∏ i ∈ Finset.range z.1,
              (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
            ∏ j ∈ Finset.range z.2,
              (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1) := by
      rw [h3, mul_one]
    rw [e, Finset.mul_sum, X7hk_sum_preds, ← Finset.sum_attach]
    apply Finset.sum_congr rfl
    rintro ⟨⟨r, s⟩, hc⟩ -
    dsimp only
    obtain ⟨hl, hmu⟩ := X7hk_hookProducts lam hc
    obtain ⟨n1, n2, n3, n4, n5⟩ := X7hk_nonzero lam hc
    rw [hl, hmu, Finset.prod_div_distrib, Finset.prod_div_distrib, hm, Nat.add_sub_cancel,
      Nat.factorial_succ]
    push_cast
    field_simp
  · refine Eq.trans ?_ (Eq.trans (Finset.sum_attach _ _) h3)
    rw [X7hk_sum_preds]
    apply Finset.sum_congr rfl
    rintro ⟨⟨r, s⟩, hc⟩ -
    dsimp only
    obtain ⟨hl, hmu⟩ := X7hk_hookProducts lam hc
    obtain ⟨n1, n2, n3, n4, n5⟩ := X7hk_nonzero lam hc
    rw [hl, hmu, Finset.prod_div_distrib, Finset.prod_div_distrib, hm, Nat.add_sub_cancel,
      Nat.factorial_succ]
    push_cast
    field_simp

end WeldedPath.YoungCounts

end

open WeldedPath.YoungCounts in
theorem WeldedPath.YoungCounts.hookBranching (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ((lam.card.factorial : ℚ) / hookProduct lam =
      ∑ mu ∈ oneBoxPredecessors lam, ((lam.card - 1).factorial : ℚ) / hookProduct mu) ∧
    ((∑ mu ∈ oneBoxPredecessors lam,
      (((lam.card - 1).factorial : ℚ) / (lam.card.factorial : ℚ)) *
        (hookProduct lam / hookProduct mu)) = 1) ∧
    ((∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
      (∏ i ∈ Finset.range z.1,
        (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
      ∏ j ∈ Finset.range z.2,
        (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1)) = 1) ∧
    ((lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) =
      ∑ z ∈ corners lam,
        (∏ i ∈ Finset.range z.1, (hook lam (i, z.2) : ℚ)) *
        (∏ j ∈ Finset.range z.2, (hook lam (z.1, j) : ℚ)) *
        ∏ u ∈ offCross lam z.1 z.2, ((hook lam u : ℚ) - 1)) :=
  WeldedPath.YoungCounts.X7hk_branching lam hne
end

-- Accepted proof: 4981ef5f-6891-40d5-b93c-8eed1d9a3d0e
section

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace X6N26H

open WeldedPath.YoungCounts

theorem pred_card (lam mu : YoungDiagram) (h : mu ∈ oneBoxPredecessors lam) :
    mu.card + 1 = lam.card := by
  unfold oneBoxPredecessors at h
  rw [Finset.mem_image] at h
  obtain ⟨a, -, rfl⟩ := h
  exact (Finset.mem_filter.1 a.property).2.1

theorem empty_count (lam : YoungDiagram) (h : lam.card = 0) : tableauCount lam = 1 := by
  have hcells : lam.cells = ∅ := Finset.card_eq_zero.1 h
  unfold tableauCount
  rw [Fintype.card_eq_one_iff]
  have hfun : ∀ t : Fin lam.card → {z : ℕ × ℕ // z ∈ lam.cells}, t = fun i => (h ▸ i).elim0 := by
    intro t; funext i; exact (h ▸ i).elim0
  refine ⟨⟨fun i => (h ▸ i).elim0, ?_⟩, ?_⟩
  · refine ⟨fun i => (h ▸ i).elim0, ?_, fun i => (h ▸ i).elim0, fun i => (h ▸ i).elim0⟩
    rw [hcells]
    apply Finset.eq_empty_of_forall_notMem
    intro z hz
    obtain ⟨i, -, -⟩ := Finset.mem_image.1 hz
    exact (h ▸ i).elim0
  · intro t
    apply Subtype.ext
    exact hfun t.1

end X6N26H

open X6N26H WeldedPath.YoungCounts in
theorem WeldedPath.YoungCounts.hookLengthFormula (lam : YoungDiagram) :
    (tableauCount lam : ℚ) = (lam.card.factorial : ℚ) / hookProduct lam := by
  induction hN : lam.card using Nat.strong_induction_on generalizing lam with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have hcells : lam.cells = ∅ := Finset.card_eq_zero.1 hN
    rw [empty_count lam hN]
    simp [hookProduct, hcells]
  · have hne : lam.cells.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have : lam.card = 0 := by simp [YoungDiagram.card, h]
      omega
    rw [tableauBranching lam hne, Nat.cast_sum, ← hN]
    rw [(hookBranching lam hne).1]
    refine Finset.sum_congr rfl fun mu hmu => ?_
    have hc := pred_card lam mu hmu
    rw [ih mu.card (by omega) mu rfl]
    rw [show lam.card - 1 = mu.card by omega]
end

namespace WeldedPath.YoungSpechtDimension
open OAI.PartialPermutation.YoungTabloid

theorem specht_finrank_hookFormula (mu : YoungDiagram) :
    (Module.finrank ℂ (spechtSub mu).toSubmodule : ℚ) =
      (mu.card.factorial : ℚ) / YoungCounts.hookProduct mu := by
  rw [← standardCount_eq_specht_finrank, ← YoungCounts.tableauCount_eq_standardCount]
  exact YoungCounts.hookLengthFormula mu

end WeldedPath.YoungSpechtDimension


end

-- Solutions.CompressedPermutationPrimitive
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb
open scoped BigOperators ComplexConjugate

theorem ketBra_eq_rankOne {X Y : Type*} [Fintype X] [Fintype Y]
    (u : Hil Y) (v : Hil X) : ketBra u v = InnerProductSpace.rankOne ℂ u v := rfl

theorem ket_inner {X : Type*} [Fintype X] [DecidableEq X] (x y : X) :
    inner ℂ (ket x) (ket y) = if x = y then 1 else 0 := by
  simp [ket, EuclideanSpace.inner_single_left, PiLp.single_apply]

theorem pCF_apply {X : Type*} [Fintype X] (u v w : Hil X) :
    pCF u v w = w - inner ℂ u w • u - inner ℂ v w • v +
      inner ℂ v w • u + inner ℂ u w • v := by
  rfl

theorem pCF_adjoint {X : Type*} [Fintype X] (u v : Hil X) :
    ContinuousLinearMap.adjoint (pCF u v) = pCF u v := by
  simp only [pCF, ketBra_eq_rankOne, map_add, map_sub,
    ContinuousLinearMap.adjoint_one, InnerProductSpace.adjoint_rankOne]
  abel

theorem pCF_involutive {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0) :
    (pCF u v).comp (pCF u v) = 1 := by
  have hvu : inner ℂ v u = 0 := by rw [← inner_conj_symm, huv]; simp
  have hleft (w : Hil X) : inner ℂ u (pCF u v w) = inner ℂ v w := by
    rw [pCF_apply]
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hu, huv]
    ring
  have hright (w : Hil X) : inner ℂ v (pCF u v w) = inner ℂ u w := by
    rw [pCF_apply]
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hv, hvu]
    ring
  apply ContinuousLinearMap.ext
  intro w
  change pCF u v (pCF u v w) = w
  rw [pCF_apply, hleft, hright, pCF_apply]
  module

theorem pCF_norm_map {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0)
    (w : Hil X) : ‖pCF u v w‖ = ‖w‖ := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (pCF u v)).mpr
  rw [pCF_adjoint, pCF_involutive u v hu hv huv]

theorem addPair_apply_self {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) : I.addPair x y x = some y := by
  simp [InjDb.addPair, hx, hy]

theorem addPair_injective {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    Set.InjOn (I.addPair x) {y | I.symm y = none} := by
  intro y hy z hz h
  have hh := congrArg (fun J : InjDb s => J x) h
  rw [addPair_apply_self I x y hx hy, addPair_apply_self I x z hx hz] at hh
  exact Option.some.inj hh

theorem addPair_ne {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) : I.addPair x y ≠ I := by
  intro h
  have hh := congrArg (fun J : InjDb s => J x) h
  rw [addPair_apply_self I x y hx hy, hx] at hh
  cases hh

theorem size_symm {s : ℕ} (I : InjDb s) : InjDb.size I.symm = I.size := by
  have hex (x : Fin s) (hx : x ∈ Finset.univ.filter fun x => (I x).isSome) :
      ∃ y, I x = some y := by
    cases h : I x with
    | none => simp [h] at hx
    | some y => exact ⟨y, rfl⟩
  let f (x : Fin s) (hx : x ∈ Finset.univ.filter fun x => (I x).isSome) :=
    (hex x hx).choose
  have hf x hx : I x = some (f x hx) := (hex x hx).choose_spec
  symm
  apply Finset.card_bij f
  · intro x hx
    have h := (I.inv x (f x hx)).mpr (hf x hx)
    change I.symm (f x hx) = some x at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h]
    rfl
  · intro x hx y hy hxy
    have h := (I.inv x (f x hx)).mpr (hf x hx)
    have h' := (I.inv y (f y hy)).mpr (hf y hy)
    rw [hxy, h'] at h
    exact (Option.some.inj h).symm
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    cases h : I.symm y with
    | none => simp [h] at hy'
    | some x =>
      have hx : I x = some y := (I.inv x y).mp h
      have hxmem : x ∈ Finset.univ.filter fun x => (I x).isSome := by simp [hx]
      refine ⟨x, hxmem, ?_⟩
      exact Option.some.inj ((hf x hxmem).symm.trans hx)

theorem unused_card {s : ℕ} (I : InjDb s) :
    (Finset.univ.filter fun y => I.symm y = none).card = s - I.size := by
  have hh := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun y : Fin s => (I.symm y).isSome)
  have hf : (Finset.univ.filter fun y : Fin s => ¬ (I.symm y).isSome) =
      (Finset.univ.filter fun y => I.symm y = none) := by
    ext y
    cases h : I.symm y <;> simp [h]
  rw [hf, Finset.card_univ, Fintype.card_fin] at hh
  change InjDb.size I.symm + _ = s at hh
  rw [size_symm] at hh
  omega

theorem size_lt_of_unset {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    I.size < s := by
  have hh := Finset.card_lt_card (Finset.filter_ssubset.mpr
    (show ∃ y ∈ (Finset.univ : Finset (Fin s)), ¬ (I y).isSome from
      ⟨x, Finset.mem_univ _, by simp [hx]⟩))
  simpa only [InjDb.size, Finset.card_univ, Fintype.card_fin] using hh

theorem plus_sum_inner_self {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y))
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y)) =
        ((s - I.size : ℕ) : ℂ) := by
  let D := Finset.univ.filter fun y => I.symm y = none
  have hsum : inner ℂ (∑ y ∈ D, ket (I.addPair x y))
      (∑ y ∈ D, ket (I.addPair x y)) = (D.card : ℂ) := by
    rw [sum_inner]
    calc
      _ = ∑ y ∈ D, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [inner_sum]
        simp only [ket_inner]
        rw [Finset.sum_eq_single y]
        · simp
        · intro z hz hzy
          apply if_neg
          intro heq
          exact hzy ((addPair_injective I x hx
            (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 heq).symm)
        · intro hnot
          exact (hnot hy).elim
      _ = _ := by simp
  simpa only [D, unused_card] using hsum

theorem plusState_inner_self {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ (plusState I x) (plusState I x) = 1 := by
  have hm : 0 < ((s - I.size : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (size_lt_of_unset I x hx)
  have hs : Real.sqrt ((s - I.size : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  have hscalar : (Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ ^ 2 *
      ((s - I.size : ℕ) : ℝ) = 1 := by
    field_simp
    exact (Real.sq_sqrt hm.le).symm
  unfold plusState
  rw [inner_smul_left, inner_smul_right, plus_sum_inner_self I x hx]
  push_cast
  have hh : ((Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ)⁻¹) ^ 2 *
      ((s - I.size : ℕ) : ℂ) = 1 := by exact_mod_cast hscalar
  convert hh using 1
  simp only [map_inv₀, Complex.conj_ofReal]
  ring

theorem ket_inner_plusState {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ (ket I) (plusState I x) = 0 := by
  unfold plusState
  rw [inner_smul_right, inner_sum]
  have hh : (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      inner ℂ (ket I) (ket (I.addPair x y))) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [ket_inner, if_neg]
    exact (addPair_ne I x y hx (Finset.mem_filter.mp hy).2).symm
  rw [hh, mul_zero]

theorem compressionPrimitive_norm {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none)
    (ψ : Hil (InjDb s)) : ‖pCF (plusState I x) (ket I) ψ‖ = ‖ψ‖ := by
  apply pCF_norm_map
  · exact plusState_inner_self I x hx
  · simp only [ket_inner, if_true]
  · rw [← inner_conj_symm, ket_inner_plusState I x hx]
    simp

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathHilbertSupport
section

namespace WeldedPath.HilbertSupport

open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

theorem ketBra_apply (u : Hil Y) (v ψ : Hil X) :
    ketBra u v ψ = inner ℂ v ψ • u := rfl

theorem inner_ket [DecidableEq X] (x : X) (ψ : Hil X) :
    inner ℂ (ket x) ψ = ψ x := by
  simp [ket, EuclideanSpace.inner_single_left]

theorem ket_apply [DecidableEq X] (x y : X) :
    ket x y = if y = x then 1 else 0 := by
  simp [ket, PiLp.single_apply]

theorem ketTensor_apply (u : Hil A) (v : Hil X) (a : A) (x : X) :
    ketTensor u v (a, x) = u a * v x := rfl

theorem sum_basis [DecidableEq X] (ψ : Hil X) :
    (∑ x, ψ x • ket x) = ψ := by
  ext y
  simp [ket_apply]

theorem diagProj_apply [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) (x : X) :
    diagProj P ψ x = if P x then ψ x else 0 := by
  simp [diagProj, ketBra_apply, inner_ket, ket_apply]

theorem diagProj_zero_iff [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) : diagProj P ψ = 0 ↔ ∀ x, P x → ψ x = 0 := by
  constructor
  · intro h x hx
    have he := congrArg (fun v : Hil X => v x) h
    simpa [diagProj_apply, hx] using he
  · intro h
    ext x
    by_cases hx : P x <;> simp [diagProj_apply, hx, h]

theorem diagProj_norm_le [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) : ‖diagProj P ψ‖ ≤ ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : P x
  · simp [diagProj_apply, hx]
  · simp [diagProj_apply, hx]

theorem diagProj_ket [DecidableEq X] (P : X → Prop) [DecidablePred P] (x : X) :
    diagProj P (ket x) = if P x then ket x else 0 := by
  ext y
  by_cases hx : P x <;> by_cases hy : y = x <;>
    simp_all [diagProj_apply, ket_apply]

theorem opTensor_ket [DecidableEq A] [DecidableEq X]
    {B : Type*} [Fintype B] (S : Hil A →L[ℂ] Hil B) (T : Hil X →L[ℂ] Hil Y)
    (a : A) (x : X) :
    opTensor S T (ket (a, x)) = ketTensor (S (ket a)) (T (ket x)) := by
  simp [opTensor, ketBra_apply, inner_ket, ket_apply]

theorem tensor_ket_eq [DecidableEq A] [DecidableEq X] (a : A) (x : X) :
    ketTensor (ket a) (ket x) = ket (a, x) := by
  ext p
  obtain ⟨b, y⟩ := p
  by_cases ha : b = a <;> by_cases hx : y = x <;>
    simp [ketTensor_apply, ket_apply, ha, hx, Prod.mk.injEq]

theorem diagProj_tensor_zero [DecidableEq A] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (u : Hil A) (v : Hil X)
    (hv : ∀ x, P x → v x = 0) :
    diagProj (fun p : A × X => P p.2) (ketTensor u v) = 0 := by
  apply (diagProj_zero_iff _ _).mpr
  rintro ⟨a, x⟩ hx
  simp [ketTensor_apply, hv x hx]

theorem tensor_projector_annihilates [DecidableEq A] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (K : Submodule ℂ (Hil X))
    (hK : ∀ v ∈ K, ∀ x, P x → v x = 0) :
    (diagProj (fun p : A × X => P p.2)).comp
      (opTensor (1 : Hil A →L[ℂ] Hil A) K.starProjection) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, smul_zero, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro p _
  rw [opTensor_ket]
  have hz := diagProj_tensor_zero P (ket p.1) (K.starProjection (ket p.2))
    (hK _ (K.starProjection_apply_mem _) )
  simpa using congrArg (fun v => ψ p • v) hz

end WeldedPath.HilbertSupport

end

-- Solutions.WeldedPathCompletionLevels
section

namespace WeldedPath.CompletionLevels

open Classical InjDb
open scoped BigOperators

variable {s : ℕ}

theorem size_le (I : InjDb s) : I.size ≤ s := by
  simpa only [InjDb.size, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card (Finset.filter_subset (fun x => (I x).isSome) Finset.univ))

theorem exists_unset (I : InjDb s) (hI : I.size < s) : ∃ x, I x = none := by
  by_contra! hn
  have hall : ∀ x, (I x).isSome := by
    intro x
    cases h : I x with
    | none => exact (hn x h).elim
    | some y => rfl
  have heq : I.size = s := by simp [InjDb.size, hall]
  omega

theorem size_addPair (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) :
    (I.addPair x y).size = I.size + 1 := by
  have hset : (Finset.univ.filter fun u => ((I.addPair x y) u).isSome) =
      insert x (Finset.univ.filter fun u => (I u).isSome) := by
    ext u
    by_cases hu : u = x
    · subst u
      simp [InjDb.addPair, hx, hy]
    · simp [InjDb.addPair, hx, hy, hu]
  have hnot : x ∉ Finset.univ.filter (fun u => (I u).isSome) := by simp [hx]
  exact (congrArg Finset.card hset).trans (Finset.card_insert_of_notMem hnot)

theorem unused_of_extends (I : InjDb s) (x : Fin s) (hx : I x = none)
    (φ : Equiv.Perm (Fin s)) (hφ : Extends φ I) : I.symm (φ x) = none := by
  cases h : I.symm (φ x) with
  | none => rfl
  | some z =>
    have hz : I z = some (φ x) := (I.inv z (φ x)).mp h
    have heq : z = x := φ.injective (hφ z (φ x) hz)
    subst z
    rw [hx] at hz
    cases hz

theorem extends_addPair_iff (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) (φ : Equiv.Perm (Fin s)) :
    Extends φ (I.addPair x y) ↔ Extends φ I ∧ φ x = y := by
  constructor
  · intro h
    refine ⟨?_, h x y (CompressedPrimitive.addPair_apply_self I x y hx hy)⟩
    intro u v huv
    have hux : u ≠ x := by
      intro heq
      subst u
      rw [hx] at huv
      cases huv
    exact h u v (by simp [InjDb.addPair, hx, hy, hux, huv])
  · rintro ⟨h, heq⟩ u v huv
    by_cases hux : u = x
    · subst u
      have hv : y = v := by simpa [InjDb.addPair, hx, hy] using huv
      exact heq.trans hv
    · exact h u v (by simpa [InjDb.addPair, hx, hy, hux] using huv)

noncomputable def rawCompletion (I : InjDb s) : Hil (Equiv.Perm (Fin s)) :=
  ∑ φ ∈ Finset.univ.filter (fun φ : Equiv.Perm (Fin s) => Extends φ I), ket φ

theorem rawCompletion_apply (I : InjDb s) (φ : Equiv.Perm (Fin s)) :
    rawCompletion I φ = if Extends φ I then 1 else 0 := by
  simp [rawCompletion, HilbertSupport.ket_apply]

theorem completion_mem_iff (M : Submodule ℂ (Hil (Equiv.Perm (Fin s))))
    (I : InjDb s) : completion I ∈ M ↔ rawCompletion I ∈ M := by
  have hpos : 0 < Real.sqrt (((s - I.size).factorial : ℕ) : ℝ) := by positivity
  have hnz : (((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (ne_of_gt hpos)
  apply M.smul_mem_iff
  simpa only [Complex.ofReal_inv] using hnz

theorem rawCompletion_extension (I : InjDb s) (x : Fin s) (hx : I x = none) :
    rawCompletion I = ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      rawCompletion (I.addPair x y) := by
  ext φ
  simp only [WithLp.ofLp_sum, Finset.sum_apply, rawCompletion_apply]
  by_cases hφ : Extends φ I
  · rw [if_pos hφ]
    symm
    rw [Finset.sum_eq_single (φ x)]
    · rw [if_pos ((extends_addPair_iff I x (φ x) hx
        (unused_of_extends I x hx φ hφ) φ).mpr ⟨hφ, rfl⟩)]
    · intro y hy hne
      apply if_neg
      intro he
      exact hne (((extends_addPair_iff I x y hx (Finset.mem_filter.mp hy).2 φ).mp he).2.symm)
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        unused_of_extends I x hx φ hφ⟩)).elim
  · rw [if_neg hφ]
    symm
    apply Finset.sum_eq_zero
    intro y hy
    apply if_neg
    intro he
    exact hφ (((extends_addPair_iff I x y hx (Finset.mem_filter.mp hy).2 φ).mp he).1)

theorem Hle_succ (r : ℕ) (hr : r < s) : Hle s r ≤ Hle s (r + 1) := by
  apply Submodule.span_le.mpr
  rintro v ⟨I, hI, rfl⟩
  obtain ⟨x, hx⟩ := exists_unset I (by omega)
  apply (completion_mem_iff _ I).mpr
  rw [rawCompletion_extension I x hx]
  apply Submodule.sum_mem
  intro y hy
  apply (completion_mem_iff _ _).mp
  apply Submodule.subset_span
  refine ⟨I.addPair x y, ?_, rfl⟩
  rw [size_addPair I x y hx (Finset.mem_filter.mp hy).2, hI]

theorem Hle_mono {r t : ℕ} (hrt : r ≤ t) (ht : t ≤ s) : Hle s r ≤ Hle s t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrt
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega) (by omega)).trans (by simpa [Nat.add_assoc] using
      (Hle_succ (s := s) (r + d) (by omega)))

theorem Hle_eq_bot {r : ℕ} (hr : s < r) : Hle s r = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro v ⟨I, hI, _⟩
  have := size_le I
  omega

theorem Hlevel_le (r : ℕ) : Hlevel s r ≤ Hle s r := by
  cases r with
  | zero => exact le_rfl
  | succ r => exact inf_le_left

theorem Hlevel_pairwise_orthogonal (r t : ℕ) (hrt : r ≠ t)
    (u v : Hil (Equiv.Perm (Fin s))) (hu : u ∈ Hlevel s r) (hv : v ∈ Hlevel s t) :
    inner ℂ u v = 0 := by
  have hlt : ∀ {a b : ℕ}, a < b → ∀ x ∈ Hlevel s a, ∀ y ∈ Hlevel s b,
      inner ℂ x y = 0 := by
    intro a b hab x hx y hy
    by_cases hb : b ≤ s
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
      have hx' : x ∈ Hle s b := Hle_mono (by omega) (by omega) (Hlevel_le a hx)
      exact ((Hle s b).mem_orthogonal y).mp hy.2 x hx'
    · have hy' : y ∈ (⊥ : Submodule ℂ (Hil (Equiv.Perm (Fin s)))) := by
        simpa only [Hle_eq_bot (by omega : s < b)] using Hlevel_le b hy
      have : y = 0 := hy'
      simp [this]
  rcases lt_or_gt_of_ne hrt with h | h
  · exact hlt h u hu v hv
  · rw [← inner_conj_symm, hlt h v hv u hu]
    simp

end WeldedPath.CompletionLevels

end

-- Solutions.CompressedPermutationUnitary
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb
open scoped BigOperators ComplexConjugate

theorem addPair_apply_other {s : ℕ} (I : InjDb s) (x y u : Fin s)
    (hx : I x = none) (hy : I.symm y = none) (hu : u ≠ x) :
    I.addPair x y u = I u := by
  simp [InjDb.addPair, hx, hy, hu]

theorem addPair_eq_original {s : ℕ} (I J : InjDb s) (x y z : Fin s)
    (hIx : I x = none) (hIy : I.symm y = none)
    (hJx : J x = none) (hJz : J.symm z = none)
    (h : I.addPair x y = J.addPair x z) : I = J := by
  apply PEquiv.ext
  intro u
  by_cases hu : u = x
  · simp only [hu, hIx, hJx]
  · have hh := congrArg (fun K : InjDb s => K u) h
    simpa only [addPair_apply_other I x y u hIx hIy hu,
      addPair_apply_other J x z u hJx hJz hu] using hh

theorem ket_inner_plus_other {s : ℕ} (I J : InjDb s) (x : Fin s)
    (hIx : I x = none) (hJx : J x = none) :
    inner ℂ (ket I) (plusState J x) = 0 := by
  unfold plusState
  rw [inner_smul_right, inner_sum]
  have hh : (∑ y ∈ Finset.univ.filter (fun y => J.symm y = none),
      inner ℂ (ket I) (ket (J.addPair x y))) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [ket_inner, if_neg]
    intro heq
    have hh := congrArg (fun K : InjDb s => K x) heq
    rw [hIx, addPair_apply_self J x y hJx (Finset.mem_filter.mp hy).2] at hh
    cases hh
  rw [hh, mul_zero]

theorem plus_inner_plus_other {s : ℕ} (I J : InjDb s) (x : Fin s)
    (hIx : I x = none) (hJx : J x = none) (hIJ : I ≠ J) :
    inner ℂ (plusState I x) (plusState J x) = 0 := by
  have hsum : inner ℂ
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y))
      (∑ z ∈ Finset.univ.filter (fun z => J.symm z = none), ket (J.addPair x z)) = 0 := by
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro y hy
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro z hz
    rw [ket_inner, if_neg]
    exact fun h => hIJ (addPair_eq_original I J x y z hIx
      (Finset.mem_filter.mp hy).2 hJx (Finset.mem_filter.mp hz).2 h)
  simp only [plusState, inner_smul_left, inner_smul_right, hsum, mul_zero]

theorem pCF_delta (X : Type*) [Fintype X] (u v : Hil X) :
    pCF u v - 1 = -ketBra u u - ketBra v v + ketBra u v + ketBra v u := by
  unfold pCF
  abel

theorem pCF_delta_mul_zero {X : Type*} [Fintype X] (u v a b : Hil X)
    (hua : inner ℂ u a = 0) (hub : inner ℂ u b = 0)
    (hva : inner ℂ v a = 0) (hvb : inner ℂ v b = 0) :
    (pCF u v - 1) * (pCF a b - 1) = 0 := by
  rw [pCF_delta, pCF_delta]
  simp only [add_mul, sub_mul, neg_mul, mul_add, mul_sub, mul_neg,
    ketBra_eq_rankOne, ContinuousLinearMap.mul_def, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
    InnerProductSpace.rankOne_comp_rankOne,
    hua, hub, hva, hvb, zero_smul, neg_zero, sub_zero, add_zero]

theorem pCF_delta_square {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0) :
    (pCF u v - 1) * (pCF u v - 1) = -((pCF u v - 1) + (pCF u v - 1)) := by
  have hh : pCF u v * pCF u v = 1 := pCF_involutive u v hu hv huv
  simp only [sub_mul, mul_sub, one_mul, mul_one, hh]
  abel

theorem compression_family_norm {X ι : Type*} [Fintype X] (S : Finset ι)
    (u v : ι → Hil X)
    (hu : ∀ i ∈ S, inner ℂ (u i) (u i) = 1)
    (hv : ∀ i ∈ S, inner ℂ (v i) (v i) = 1)
    (huv : ∀ i ∈ S, inner ℂ (u i) (v i) = 0)
    (hoff : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      inner ℂ (u i) (u j) = 0 ∧ inner ℂ (u i) (v j) = 0 ∧
      inner ℂ (v i) (u j) = 0 ∧ inner ℂ (v i) (v j) = 0)
    (ψ : Hil X) :
    ‖(1 + ∑ i ∈ S, (pCF (u i) (v i) - 1)) ψ‖ = ‖ψ‖ := by
  let Δ := fun i => pCF (u i) (v i) - 1
  have hdiag i (hi : i ∈ S) : Δ i * Δ i = -(Δ i + Δ i) :=
    pCF_delta_square (u i) (v i) (hu i hi) (hv i hi) (huv i hi)
  have hneq i (hi : i ∈ S) j (hj : j ∈ S) (hij : i ≠ j) : Δ i * Δ j = 0 := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hoff i hi j hj hij
    exact pCF_delta_mul_zero _ _ _ _ h₁ h₂ h₃ h₄
  have hsquare : (∑ i ∈ S, Δ i) * (∑ i ∈ S, Δ i) =
      -((∑ i ∈ S, Δ i) + (∑ i ∈ S, Δ i)) := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ i ∈ S, Δ i * Δ i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_eq_single i
        · intro j hj hji
          exact hneq i hi j hj hji.symm
        · intro hnot
          exact (hnot hi).elim
      _ = ∑ i ∈ S, -(Δ i + Δ i) := Finset.sum_congr rfl hdiag
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hinv : (1 + ∑ i ∈ S, Δ i) * (1 + ∑ i ∈ S, Δ i) = 1 := by
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hsquare]
    abel
  have hadj : ContinuousLinearMap.adjoint (1 + ∑ i ∈ S, Δ i) =
      1 + ∑ i ∈ S, Δ i := by
    simp only [Δ, map_add, map_sum, map_sub, pCF_adjoint, ContinuousLinearMap.adjoint_one]
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    (1 + ∑ i ∈ S, Δ i)).mpr
  rw [hadj]
  exact hinv

theorem pC_norm_map (s : ℕ) (x : Fin s) (ψ : Hil (InjDb s)) : ‖pC s x ψ‖ = ‖ψ‖ := by
  unfold pC
  apply compression_family_norm
  · intro I hI
    exact plusState_inner_self I x (Finset.mem_filter.mp hI).2
  · intro I _
    simp only [ket_inner, if_true]
  · intro I hI
    rw [← inner_conj_symm, ket_inner_plusState I x (Finset.mem_filter.mp hI).2]
    simp
  · intro I hI J hJ hIJ
    have hIx := (Finset.mem_filter.mp hI).2
    have hJx := (Finset.mem_filter.mp hJ).2
    refine ⟨plus_inner_plus_other I J x hIx hJx hIJ, ?_,
      ket_inner_plus_other I J x hIx hJx, ?_⟩
    · rw [← inner_conj_symm, ket_inner_plus_other J I x hJx hIx]
      simp
    · simp only [ket_inner, hIJ, if_false]

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathEncodedOracleUnitary
section

namespace WeldedPath.EncodedOracleUnitary

open Classical QAlgorithms HilbertSupport CompressedPrimitive Supplement
open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

theorem basisMap_apply_equiv [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (ψ : Hil X) (x : X) : basisMap e ψ (e x) = ψ x := by
  simp [basisMap, ketBra_apply, inner_ket, ket_apply, e.injective.eq_iff]

theorem basisMap_equiv_norm [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (ψ : Hil X) : ‖basisMap e ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  rw [← Equiv.sum_comp e (fun y => ‖basisMap e ψ y‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro x _
  rw [basisMap_apply_equiv]

theorem basisMap_involutive_norm [DecidableEq X]
    (f : X → X) (hf : Function.Involutive f) (ψ : Hil X) :
    ‖basisMap f ψ‖ = ‖ψ‖ :=
  basisMap_equiv_norm (hf.toPerm f) ψ

noncomputable def slice (ψ : Hil (A × X)) (a : A) : Hil X :=
  WithLp.toLp 2 (fun x => ψ (a, x))

theorem opTensor_one_apply [DecidableEq A] [DecidableEq X]
    (T : Hil X →L[ℂ] Hil Y) (ψ : Hil (A × X)) (a : A) (y : Y) :
    opTensor (1 : Hil A →L[ℂ] Hil A) T ψ (a, y) = T (slice ψ a) y := by
  conv_rhs => rw [← sum_basis (slice ψ a)]
  simp [opTensor, ketBra_apply, inner_ket, ketTensor_apply,
    Fintype.sum_prod_type, ket_apply, slice]

theorem sum_slice_norm_sq (ψ : Hil (A × X)) :
    (∑ a, ‖slice ψ a‖ ^ 2) = ‖ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, slice,
    PiLp.toLp_apply]

theorem opTensor_one_norm [DecidableEq A] [DecidableEq X]
    (T : Hil X →L[ℂ] Hil Y) (hT : ∀ ψ, ‖T ψ‖ = ‖ψ‖) (ψ : Hil (A × X)) :
    ‖opTensor (1 : Hil A →L[ℂ] Hil A) T ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← sum_slice_norm_sq, ← sum_slice_norm_sq]
  apply Finset.sum_congr rfl
  intro a _
  have hs : slice (opTensor (1 : Hil A →L[ℂ] Hil A) T ψ) a = T (slice ψ a) := by
    ext y
    exact opTensor_one_apply T ψ a y
  rw [hs, hT]

theorem adjoint_norm_of_norm (U : Hil X →L[ℂ] Hil X)
    (hU : ∀ ψ, ‖U ψ‖ = ‖ψ‖) (ψ : Hil X) :
    ‖ContinuousLinearMap.adjoint U ψ‖ = ‖ψ‖ := by
  have he : (ContinuousLinearMap.adjoint U).comp U = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mp hU
  have hi : Function.LeftInverse (ContinuousLinearMap.adjoint U) U := by
    intro v
    exact congrArg (fun T : Hil X →L[ℂ] Hil X => T v) he
  have hsurj : Function.Surjective U :=
    LinearMap.surjective_of_injective (f := U.toLinearMap) hi.injective
  obtain ⟨v, rfl⟩ := hsurj ψ
  rw [hi v, hU v]

theorem qubits_add_cancel {d : ℕ} (a b : Qubits d) : a + b + b = a := by
  funext i
  change a i + b i + b i = a i
  cases a i <;> cases b i <;> rfl

theorem stdQueryE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × Equiv.Perm (Fin s))) :
    ‖stdQueryE enc x inv ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  rintro ⟨a, π⟩
  exact Prod.ext (qubits_add_cancel a _) rfl

theorem purifiedXorE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (ψ : Hil (Qubits d × InjDb s)) :
    ‖purifiedXorE enc x ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  rintro ⟨a, I⟩
  cases h : I x with
  | none => simp only [h]
  | some y => simp only [h, qubits_add_cancel]

theorem flipDb_norm (s : ℕ) (ψ : Hil (InjDb s)) : ‖flipDb s ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  exact PEquiv.symm_symm

theorem cpOE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖cpOE enc x inv ψ‖ = ‖ψ‖ := by
  let pc := opTensor (1 : Hil (Qubits d) →L[ℂ] Hil (Qubits d)) (pC s x)
  let fl := opTensor (1 : Hil (Qubits d) →L[ℂ] Hil (Qubits d)) (flipDb s)
  have hpc : ∀ v, ‖pc v‖ = ‖v‖ := opTensor_one_norm (pC s x) (pC_norm_map s x)
  have hfl : ∀ v, ‖fl v‖ = ‖v‖ := opTensor_one_norm (flipDb s) (flipDb_norm s)
  have hpc' : ∀ v, ‖ContinuousLinearMap.adjoint pc v‖ = ‖v‖ :=
    adjoint_norm_of_norm pc hpc
  have hfl' : ∀ v, ‖ContinuousLinearMap.adjoint fl v‖ = ‖v‖ :=
    adjoint_norm_of_norm fl hfl
  change ‖(if inv then fl.comp
    ((pc.comp ((purifiedXorE enc x).comp (ContinuousLinearMap.adjoint pc))).comp
      (ContinuousLinearMap.adjoint fl))
    else pc.comp ((purifiedXorE enc x).comp (ContinuousLinearMap.adjoint pc))) ψ‖ = _
  cases inv <;> simp only [Bool.false_eq_true, if_false, if_true,
    ContinuousLinearMap.comp_apply, hpc, hfl, purifiedXorE_norm, hpc', hfl']

theorem cpOE_adjoint_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖ContinuousLinearMap.adjoint (cpOE enc x inv) ψ‖ = ‖ψ‖ :=
  adjoint_norm_of_norm _ (cpOE_norm enc x inv) ψ

theorem cpOE_norm_le {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖cpOE enc x inv ψ‖ ≤ ‖ψ‖ := (cpOE_norm enc x inv ψ).le

end WeldedPath.EncodedOracleUnitary

end

-- Solutions.WeldedPathOperatorPolar
section

namespace WeldedPath.OperatorPolar

open scoped BigOperators
open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma inv_sqrt_scalar (x : ℝ) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = (Real.sqrt x)⁻¹ := by
  by_cases hx : x ≤ 0
  · simp [Real.sqrt_eq_zero_of_nonpos hx]
  · have hx' : 0 < x := lt_of_not_ge hx
    have hh : (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ * x = 1 := by
      rw [← mul_inv, ← pow_two, Real.sq_sqrt hx'.le, inv_mul_cancel₀ (ne_of_gt hx')]
    rw [hh, one_mul]

noncomputable def invSqrt (A : Hil X →L[ℂ] Hil X) : Hil X →L[ℂ] Hil X :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A

lemma invSqrt_adjoint (A : Hil X →L[ℂ] Hil X) :
    ContinuousLinearMap.adjoint (invSqrt A) = invSqrt A := by
  change star (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A) = _
  rw [← cfc_star]
  simp only [star_trivial]
  rfl

lemma invSqrt_sandwich (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    invSqrt A * invSqrt A * A * invSqrt A = invSqrt A := by
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  by_cases hf : ContinuousOn f (spectrum ℝ A)
  · have hff := cfc_mul f f A hf hf
    have hffi := cfc_mul (fun x => f x * f x) (fun x : ℝ => x) A
      (hf.mul hf) continuousOn_id
    have hffif := cfc_mul (fun x => f x * f x * x) f A
      ((hf.mul hf).mul continuousOn_id) hf
    calc
      _ = cfc (fun x => f x * f x * x * f x) A := by
        rw [hffif, hffi, hff, cfc_id' ℝ A hA]
        rfl
      _ = _ := cfc_congr (fun x _ => inv_sqrt_scalar x)
  · have hz : invSqrt A = 0 := cfc_apply_of_not_continuousOn A hf
    simp only [hz, zero_mul, mul_zero]

lemma invSqrt_commute (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    Commute (invSqrt A) A := by
  have h := cfc_commute_cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => x) A
  rwa [cfc_id' ℝ A hA] at h

lemma invSqrt_range_factor (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    invSqrt A = A * invSqrt A * invSqrt A * invSqrt A := by
  have hc := (invSqrt_commute A hA).eq
  calc
    _ = invSqrt A * invSqrt A * A * invSqrt A := (invSqrt_sandwich A hA).symm
    _ = invSqrt A * (invSqrt A * A) * invSqrt A := by simp only [mul_assoc]
    _ = invSqrt A * (A * invSqrt A) * invSqrt A := by rw [hc]
    _ = (invSqrt A * A) * invSqrt A * invSqrt A := by simp only [mul_assoc]
    _ = _ := by rw [hc]

lemma invSqrt_mapsTo (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A)
    (K : Submodule ℂ (Hil X)) (hK : ∀ ψ, A ψ ∈ K) (ψ : Hil X) :
    invSqrt A ψ ∈ K := by
  rw [invSqrt_range_factor A hA]
  exact hK _

noncomputable def polarMap (T : Hil X →L[ℂ] Hil Y) : Hil Y →L[ℂ] Hil X :=
  (ContinuousLinearMap.adjoint T).comp (invSqrt (T.comp (ContinuousLinearMap.adjoint T)))

lemma gram_selfadjoint (T : Hil X →L[ℂ] Hil Y) :
    IsSelfAdjoint (T.comp (ContinuousLinearMap.adjoint T)) := by
  change ContinuousLinearMap.adjoint (T.comp (ContinuousLinearMap.adjoint T)) = _
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem polarMap_partial (T : Hil X →L[ℂ] Hil Y) :
    ((polarMap T).comp (ContinuousLinearMap.adjoint (polarMap T))).comp (polarMap T) =
      polarMap T := by
  let B := invSqrt (T.comp (ContinuousLinearMap.adjoint T))
  have hB : ((B.comp B).comp (T.comp (ContinuousLinearMap.adjoint T))).comp B = B := by
    exact invSqrt_sandwich _ (gram_selfadjoint T)
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change (((ContinuousLinearMap.adjoint T).comp B).comp
    (B.comp T)).comp ((ContinuousLinearMap.adjoint T).comp B) =
      (ContinuousLinearMap.adjoint T).comp B
  calc
    _ = (ContinuousLinearMap.adjoint T).comp
        (((B.comp B).comp (T.comp (ContinuousLinearMap.adjoint T))).comp B) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [hB]

end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathIntertwinerPartial
section

namespace WeldedPath.IntertwinerPartial

open Classical OperatorPolar HilbertSupport
open scoped BigOperators

lemma Gam_range (s r : ℕ) (ψ : Hil (InjDb s)) : Gam s r ψ ∈ Hlevel s r := by
  unfold Gam
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  apply Submodule.sum_mem
  intro I hI
  exact Submodule.smul_mem _ _ ((Hlevel s r).starProjection_apply_mem (completion I))

lemma Gam_ket (s r : ℕ) (I : InjDb s) :
    Gam s r (ket I) = if I.size = r then projLevel s r (completion I) else 0 := by
  simp [Gam, ketBra_apply, inner_ket, ket_apply]

lemma Gam_adjoint_support (s r : ℕ) (ψ : Hil (Equiv.Perm (Fin s)))
    (I : InjDb s) (hI : I.size ≠ r) : ContinuousLinearMap.adjoint (Gam s r) ψ I = 0 := by
  rw [← inner_ket I, ContinuousLinearMap.adjoint_inner_right, Gam_ket,
    if_neg hI, inner_zero_left]

lemma Gam_comp_adjoint_zero (s r t : ℕ) (hrt : r ≠ t) :
    (Gam s r).comp (ContinuousLinearMap.adjoint (Gam s t)) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  change Gam s r (ContinuousLinearMap.adjoint (Gam s t) ψ) = 0
  rw [← sum_basis (ContinuousLinearMap.adjoint (Gam s t) ψ)]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro I _
  by_cases hI : I.size = r
  · rw [Gam_adjoint_support s t ψ I (by omega), zero_smul]
  · rw [Gam_ket, if_neg hI, smul_zero]

lemma GramInvSqrt_eq (s r : ℕ) : GramInvSqrt s r = invSqrt (Gram s r) := rfl

lemma Gram_selfadjoint (s r : ℕ) : IsSelfAdjoint (Gram s r) := gram_selfadjoint (Gam s r)

lemma GramInvSqrt_range (s r : ℕ) (ψ : Hil (Equiv.Perm (Fin s))) :
    GramInvSqrt s r ψ ∈ Hlevel s r :=
  invSqrt_mapsTo _ (Gram_selfadjoint s r) (Hlevel s r)
    (fun v => Gam_range s r (ContinuousLinearMap.adjoint (Gam s r) v)) ψ

lemma GramInvSqrt_adjoint (s r : ℕ) :
    ContinuousLinearMap.adjoint (GramInvSqrt s r) = GramInvSqrt s r :=
  invSqrt_adjoint _

lemma GramInvSqrt_comp_zero (s r t : ℕ) (hrt : r ≠ t) :
    (GramInvSqrt s r).comp (GramInvSqrt s t) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply ext_inner_left ℂ
  intro η
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, inner_zero_right]
  have he := ContinuousLinearMap.adjoint_inner_right (GramInvSqrt s r) η
    (GramInvSqrt s t ψ)
  rw [GramInvSqrt_adjoint] at he
  rw [he]
  exact CompletionLevels.Hlevel_pairwise_orthogonal r t hrt _ _
    (GramInvSqrt_range s r η) (GramInvSqrt_range s t ψ)

lemma polar_Gam_cross_final (s r t : ℕ) (hrt : r ≠ t) :
    (polarMap (Gam s r)).comp (ContinuousLinearMap.adjoint (polarMap (Gam s t))) = 0 := by
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change ((ContinuousLinearMap.adjoint (Gam s r)).comp (GramInvSqrt s r)).comp
    ((GramInvSqrt s t).comp (Gam s t)) = 0
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (GramInvSqrt s r) (GramInvSqrt s t) (Gam s t), GramInvSqrt_comp_zero s r t hrt]
  simp

lemma polar_Gam_cross_initial (s r t : ℕ) (hrt : r ≠ t) :
    (ContinuousLinearMap.adjoint (polarMap (Gam s r))).comp (polarMap (Gam s t)) = 0 := by
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change ((GramInvSqrt s r).comp (Gam s r)).comp
    ((ContinuousLinearMap.adjoint (Gam s t)).comp (GramInvSqrt s t)) = 0
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (Gam s r) (ContinuousLinearMap.adjoint (Gam s t)) (GramInvSqrt s t),
    Gam_comp_adjoint_zero s r t hrt]
  simp

theorem sum_partial {X Y ι : Type*} [Fintype X] [Fintype Y]
    (S : Finset ι) (V : ι → Hil X →L[ℂ] Hil Y)
    (hp : ∀ i ∈ S, ((V i).comp (ContinuousLinearMap.adjoint (V i))).comp (V i) = V i)
    (hf : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (V i).comp (ContinuousLinearMap.adjoint (V j)) = 0)
    (hi : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (ContinuousLinearMap.adjoint (V i)).comp (V j) = 0) :
    (((∑ i ∈ S, V i).comp (ContinuousLinearMap.adjoint (∑ i ∈ S, V i))).comp
      (∑ i ∈ S, V i)) = ∑ i ∈ S, V i := by
  classical
  simp only [map_sum, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  apply Finset.sum_congr rfl
  intro i hiS
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · exact hp i hiS
    · intro j hj hji
      rw [hf j hj i hiS hji]
      simp
    · exact fun h => (h hiS).elim
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro k hk
    rw [ContinuousLinearMap.comp_assoc, hi j hj i hiS hji]
    simp
  · exact fun h => (h hiS).elim

theorem intertwiner_partial (s : ℕ) :
    ((intertwiner s).comp (ContinuousLinearMap.adjoint (intertwiner s))).comp
      (intertwiner s) = intertwiner s := by
  change (((∑ r ∈ Finset.range s, polarMap (Gam s r)).comp
    (ContinuousLinearMap.adjoint (∑ r ∈ Finset.range s, polarMap (Gam s r)))).comp
      (∑ r ∈ Finset.range s, polarMap (Gam s r))) =
        ∑ r ∈ Finset.range s, polarMap (Gam s r)
  exact sum_partial _ _ (fun r _ => polarMap_partial (Gam s r))
    (fun r _ t _ hrt => polar_Gam_cross_final s r t hrt)
    (fun r _ t _ hrt => polar_Gam_cross_initial s r t hrt)

end WeldedPath.IntertwinerPartial

end

-- Solutions.WeldedPathCompletionFrame
section

namespace WeldedPath.CompletionFrame

open Classical InjDb HilbertSupport CompletionLevels
open scoped BigOperators

variable {s : ℕ}

noncomputable def domain (I : InjDb s) : Finset (Fin s) :=
  Finset.univ.filter fun x => (I x).isSome

lemma mem_domain (I : InjDb s) (x : Fin s) : x ∈ domain I ↔ (I x).isSome := by
  simp only [domain, Finset.mem_filter, Finset.mem_univ, true_and]

lemma card_domain (I : InjDb s) : (domain I).card = I.size := rfl

noncomputable def restrict (φ : Equiv.Perm (Fin s)) (D : Finset (Fin s)) : InjDb s :=
  (PEquiv.ofSet (D : Set (Fin s))).trans φ.toPEquiv

lemma restrict_apply (φ : Equiv.Perm (Fin s)) (D : Finset (Fin s)) (x : Fin s) :
    restrict φ D x = if x ∈ D then some (φ x) else none := by
  change ((if x ∈ D then some x else none).bind (fun u => some (φ u))) = _
  split_ifs <;> rfl

lemma restrict_domain (φ : Equiv.Perm (Fin s)) (D : Finset (Fin s)) :
    domain (restrict φ D) = D := by
  ext x
  simp only [mem_domain, restrict_apply]
  split_ifs <;> simp_all

lemma restrict_size (φ : Equiv.Perm (Fin s)) (D : Finset (Fin s)) :
    (restrict φ D).size = D.card := by
  rw [← card_domain, restrict_domain]

lemma extends_restrict_iff (φ ψ : Equiv.Perm (Fin s)) (D : Finset (Fin s)) :
    Extends ψ (restrict φ D) ↔ ∀ x ∈ D, ψ x = φ x := by
  constructor
  · intro h x hx
    exact h x (φ x) (by rw [restrict_apply, if_pos hx])
  · intro h x y hxy
    rw [restrict_apply] at hxy
    split_ifs at hxy with hx
    · exact (h x hx).trans (Option.some.inj hxy)

lemma restrict_domain_eq (φ : Equiv.Perm (Fin s)) (I : InjDb s) (hI : Extends φ I) :
    restrict φ (domain I) = I := by
  apply PEquiv.ext
  intro x
  rw [restrict_apply]
  cases hx : I x with
  | none => simp [mem_domain, hx]
  | some y => simp [mem_domain, hx, hI x y hx]

noncomputable def agreement (φ ψ : Equiv.Perm (Fin s)) : Finset (Fin s) :=
  Finset.univ.filter fun x => φ x = ψ x

noncomputable def commonDatabaseEquiv (φ ψ : Equiv.Perm (Fin s)) (r : ℕ) :
    {I : InjDb s // I.size = r ∧ Extends φ I ∧ Extends ψ I} ≃
      ↥((agreement φ ψ).powersetCard r) where
  toFun I := ⟨domain I.1, Finset.mem_powersetCard.mpr ⟨by
    intro x hx
    cases hxy : I.1 x with
    | none => simp [mem_domain, hxy] at hx
    | some y =>
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (I.2.2.1 x y hxy).trans (I.2.2.2 x y hxy).symm⟩,
    (card_domain I.1).trans I.2.1⟩⟩
  invFun D := ⟨restrict φ D.1, by
    refine ⟨(restrict_size φ D.1).trans (Finset.mem_powersetCard.mp D.2).2, ?_, ?_⟩
    · exact (extends_restrict_iff φ φ D.1).mpr (fun _ _ => rfl)
    · apply (extends_restrict_iff φ ψ D.1).mpr
      intro x hx
      exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp D.2).1 hx)).2.symm⟩
  left_inv I := Subtype.ext (restrict_domain_eq φ I.1 I.2.2.1)
  right_inv D := Subtype.ext (restrict_domain φ D.1)

theorem common_database_count (φ ψ : Equiv.Perm (Fin s)) (r : ℕ) :
    (Finset.univ.filter fun I : InjDb s =>
      I.size = r ∧ Extends φ I ∧ Extends ψ I).card = (agreement φ ψ).card.choose r := by
  rw [← Fintype.card_coe]
  calc
    _ = Fintype.card {I : InjDb s // I.size = r ∧ Extends φ I ∧ Extends ψ I} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun I => by simp)
    _ = Fintype.card ↥((agreement φ ψ).powersetCard r) :=
      Fintype.card_congr (commonDatabaseEquiv φ ψ r)
    _ = _ := by rw [Fintype.card_coe, Finset.card_powersetCard]

lemma completion_apply (I : InjDb s) (φ : Equiv.Perm (Fin s)) :
    completion I φ = if Extends φ I then (Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ else 0 := by
  change (((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℂ) • rawCompletion I) φ = _
  simp only [PiLp.smul_apply, smul_eq_mul, rawCompletion_apply]
  split_ifs <;> simp

lemma inner_completion_ket (I : InjDb s) (φ : Equiv.Perm (Fin s)) :
    inner ℂ (completion I) (ket φ) =
      if Extends φ I then (Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ else 0 := by
  rw [← inner_conj_symm, inner_ket, completion_apply]
  split_ifs <;> simp

/-- The normalized completion frame before selecting a representation level. -/
noncomputable def frame (s r : ℕ) :
    Hil (Equiv.Perm (Fin s)) →L[ℂ] Hil (Equiv.Perm (Fin s)) :=
  ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I.size = r),
    ketBra (completion I) (completion I)

lemma frame_term (I : InjDb s) (φ ψ : Equiv.Perm (Fin s)) :
    ketBra (completion I) (completion I) (ket ψ) φ =
      if Extends φ I ∧ Extends ψ I then (((s - I.size).factorial : ℝ)⁻¹ : ℂ) else 0 := by
  rw [ketBra_apply, inner_completion_ket]
  simp only [PiLp.smul_apply, smul_eq_mul, completion_apply]
  have hsq : (Real.sqrt ((s - I.size).factorial : ℝ)) ^ 2 = (s - I.size).factorial :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hc : ((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℂ) =
      (((s - I.size).factorial : ℝ)⁻¹ : ℂ) := by
    rw [← mul_inv, ← pow_two]
    simpa only [Complex.ofReal_pow] using congrArg (fun z : ℝ => (z⁻¹ : ℂ)) hsq
  split_ifs <;> simp_all

/-- The exact normalized frame kernel is a binomial polynomial in the
number of positions on which the two permutations agree. -/
theorem frame_kernel (r : ℕ) (φ ψ : Equiv.Perm (Fin s)) :
    frame s r (ket ψ) φ =
      (((agreement φ ψ).card.choose r : ℝ) / ((s - r).factorial : ℝ) : ℂ) := by
  simp only [frame, ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    Finset.sum_filter]
  have hterm (I : InjDb s) :
      ((if I.size = r then ketBra (completion I) (completion I) else 0) (ket ψ)) φ =
        if I.size = r then
          if Extends φ I ∧ Extends ψ I then (((s - I.size).factorial : ℝ)⁻¹ : ℂ) else 0
        else 0 := by
    by_cases hi : I.size = r <;> simp [hi, frame_term]
  simp_rw [hterm]
  have ht (I : InjDb s) :
      (if I.size = r then
        if Extends φ I ∧ Extends ψ I then (((s - I.size).factorial : ℝ)⁻¹ : ℂ) else 0
      else 0) =
      if I.size = r ∧ Extends φ I ∧ Extends ψ I then (((s - r).factorial : ℝ)⁻¹ : ℂ) else 0 := by
    split_ifs <;> simp_all
  simp_rw [ht]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, common_database_count]
  push_cast
  rfl

lemma agreement_left (a φ ψ : Equiv.Perm (Fin s)) : agreement (a * φ) (a * ψ) = agreement φ ψ := by
  ext x
  simp [agreement]

lemma agreement_right_card (a φ ψ : Equiv.Perm (Fin s)) :
    (agreement (φ * a) (ψ * a)).card = (agreement φ ψ).card := by
  have he : (agreement (φ * a) (ψ * a)).image a = agreement φ ψ := by
    ext x
    simp only [agreement, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
      simpa using hx
  rw [← Finset.card_image_of_injective _ a.injective, he]

theorem frame_kernel_left_invariant (r : ℕ) (a φ ψ : Equiv.Perm (Fin s)) :
    frame s r (ket (a * ψ)) (a * φ) = frame s r (ket ψ) φ := by
  simp only [frame_kernel, agreement_left]

theorem frame_kernel_right_invariant (r : ℕ) (a φ ψ : Equiv.Perm (Fin s)) :
    frame s r (ket (ψ * a)) (φ * a) = frame s r (ket ψ) φ := by
  simp only [frame_kernel, agreement_right_card]

noncomputable def centralKernel (s r : ℕ) (g : Equiv.Perm (Fin s)) : ℂ :=
  frame s r (ket 1) g

theorem centralKernel_comm (r : ℕ) (g h : Equiv.Perm (Fin s)) :
    centralKernel s r (g * h) = centralKernel s r (h * g) := by
  calc
    _ = frame s r (ket h⁻¹) g := by
      simpa only [centralKernel, inv_mul_cancel] using
        frame_kernel_right_invariant r h g h⁻¹
    _ = _ := by
      symm
      simpa only [centralKernel, mul_inv_cancel] using
        frame_kernel_left_invariant r h g h⁻¹

theorem frame_kernel_eq_centralKernel (r : ℕ) (φ ψ : Equiv.Perm (Fin s)) :
    frame s r (ket ψ) φ = centralKernel s r (φ * ψ⁻¹) := by
  symm
  simpa only [centralKernel, mul_inv_cancel] using
    frame_kernel_right_invariant r ψ⁻¹ φ ψ

theorem frame_apply_convolution (r : ℕ) (v : Hil (Equiv.Perm (Fin s)))
    (φ : Equiv.Perm (Fin s)) :
    frame s r v φ = ∑ ψ, v ψ * centralKernel s r (φ * ψ⁻¹) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, frame_kernel_eq_centralKernel]

lemma Gam_apply (r : ℕ) (v : Hil (InjDb s)) :
    Gam s r v = ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I.size = r),
      v I • projLevel s r (completion I) := by
  simp only [Gam, ContinuousLinearMap.sum_apply, ketBra_apply, inner_ket]

lemma Gam_adjoint_apply (r : ℕ) (v : Hil (Equiv.Perm (Fin s))) (I : InjDb s) :
    ContinuousLinearMap.adjoint (Gam s r) v I =
      if I.size = r then inner ℂ (projLevel s r (completion I)) v else 0 := by
  rw [← inner_ket I, ContinuousLinearMap.adjoint_inner_right, IntertwinerPartial.Gam_ket]
  split_ifs <;> simp

/-- The canonical Gram operator is precisely the level compression of the
explicit agreement-count frame; no representation-theoretic premise is used. -/
theorem Gram_eq_proj_frame_proj (s r : ℕ) :
    Gram s r = (projLevel s r).comp ((frame s r).comp (projLevel s r)) := by
  apply ContinuousLinearMap.ext
  intro v
  change Gam s r (ContinuousLinearMap.adjoint (Gam s r) v) =
    projLevel s r (frame s r (projLevel s r v))
  rw [Gam_apply]
  simp only [frame, ContinuousLinearMap.sum_apply, ketBra_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Gam_adjoint_apply, if_pos (Finset.mem_filter.mp hI).2]
  congr 1
  exact (Hlevel s r).starProjection_isSymmetric (completion I) v

end WeldedPath.CompletionFrame

end

-- Solutions.WeldedPathCompletionFrameInvariant
section

namespace WeldedPath.CompletionFrame

open Classical InjDb HilbertSupport CompletionLevels
open scoped BigOperators

variable {s : ℕ}

noncomputable def permuteOutputs (a : Equiv.Perm (Fin s)) (I : InjDb s) : InjDb s :=
  I.trans a.toPEquiv

lemma permuteOutputs_apply (a : Equiv.Perm (Fin s)) (I : InjDb s) (x : Fin s) :
    permuteOutputs a I x = (I x).map a := by
  change (I x).bind (fun y => some (a y)) = _
  cases I x <;> rfl

lemma permuteOutputs_size (a : Equiv.Perm (Fin s)) (I : InjDb s) :
    (permuteOutputs a I).size = I.size := by
  unfold InjDb.size
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, permuteOutputs_apply]
  cases I x <;> rfl

lemma extends_permuteOutputs_iff (a φ : Equiv.Perm (Fin s)) (I : InjDb s) :
    Extends φ (permuteOutputs a I) ↔ Extends (a⁻¹ * φ) I := by
  constructor
  · intro h x y hxy
    have he := h x (a y) (by rw [permuteOutputs_apply, hxy]; rfl)
    change a.symm (φ x) = y
    rw [he, Equiv.symm_apply_apply]
  · intro h x y hxy
    rw [permuteOutputs_apply, Option.map_eq_some_iff] at hxy
    obtain ⟨z, hz, rfl⟩ := hxy
    have he := congrArg a (h x z hz)
    change a (a.symm (φ x)) = a z at he
    simpa only [Equiv.apply_symm_apply] using he

noncomputable def translate (a : Equiv.Perm (Fin s)) :
    Hil (Equiv.Perm (Fin s)) →ₗ[ℂ] Hil (Equiv.Perm (Fin s)) where
  toFun v := WithLp.toLp 2 (fun φ => v (a⁻¹ * φ))
  map_add' v w := by ext φ; rfl
  map_smul' c v := by ext φ; rfl

lemma translate_apply (a : Equiv.Perm (Fin s)) (v : Hil (Equiv.Perm (Fin s)))
    (φ : Equiv.Perm (Fin s)) : translate a v φ = v (a⁻¹ * φ) := rfl

lemma translate_completion (a : Equiv.Perm (Fin s)) (I : InjDb s) :
    translate a (completion I) = completion (permuteOutputs a I) := by
  ext φ
  simp only [translate_apply, completion_apply, permuteOutputs_size,
    extends_permuteOutputs_iff]

theorem translate_mem_Hle (a : Equiv.Perm (Fin s)) (r : ℕ)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hle s r) : translate a v ∈ Hle s r := by
  change v ∈ Submodule.span ℂ {v | ∃ I : InjDb s, I.size = r ∧ v = completion I} at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨I, hI, rfl⟩ := hv
    rw [translate_completion]
    exact Submodule.subset_span ⟨permuteOutputs a I, (permuteOutputs_size a I).trans hI, rfl⟩
  | zero => simpa only [map_zero] using (Hle s r).zero_mem
  | add v w hv hw ihv ihw => simpa only [map_add] using (Hle s r).add_mem ihv ihw
  | smul c v hv ih => simpa only [map_smul] using (Hle s r).smul_mem c ih

theorem frame_eq_sum_translate (r : ℕ) (v : Hil (Equiv.Perm (Fin s))) :
    frame s r v = ∑ a, centralKernel s r a • translate a v := by
  ext φ
  rw [frame_apply_convolution]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, translate_apply]
  apply Fintype.sum_equiv ((Equiv.inv (Equiv.Perm (Fin s))).trans (Equiv.mulLeft φ))
  intro ψ
  change v ψ * centralKernel s r (φ * ψ⁻¹) =
    centralKernel s r (φ * ψ⁻¹) * v ((φ * ψ⁻¹)⁻¹ * φ)
  simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  exact mul_comm _ _

theorem frame_mem_Hle (r t : ℕ) (v : Hil (Equiv.Perm (Fin s)))
    (hv : v ∈ Hle s t) : frame s r v ∈ Hle s t := by
  rw [frame_eq_sum_translate]
  exact Submodule.sum_mem _ (fun a _ =>
    (Hle s t).smul_mem _ (translate_mem_Hle a t v hv))

lemma frame_adjoint (s r : ℕ) : ContinuousLinearMap.adjoint (frame s r) = frame s r := by
  have hk (u v : Hil (Equiv.Perm (Fin s))) :
      ketBra u v = InnerProductSpace.rankOne ℂ u v := by
    ext x
    rfl
  simp only [frame, hk, map_sum, InnerProductSpace.adjoint_rankOne]

lemma frame_symmetric (r : ℕ) (v w : Hil (Equiv.Perm (Fin s))) :
    inner ℂ (frame s r v) w = inner ℂ v (frame s r w) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, frame_adjoint]

theorem frame_mem_Hlevel (r t : ℕ) (v : Hil (Equiv.Perm (Fin s)))
    (hv : v ∈ Hlevel s t) : frame s r v ∈ Hlevel s t := by
  cases t with
  | zero => exact frame_mem_Hle r 0 v hv
  | succ t =>
    refine ⟨frame_mem_Hle r (t + 1) v hv.1, ?_⟩
    apply ((Hle s t).mem_orthogonal _).mpr
    intro w hw
    rw [← frame_symmetric]
    exact ((Hle s t).mem_orthogonal v).mp hv.2 _ (frame_mem_Hle r t w hw)

theorem projLevel_frame_projLevel (s r t : ℕ) :
    (projLevel s t).comp ((frame s r).comp (projLevel s t)) =
      (frame s r).comp (projLevel s t) := by
  apply ContinuousLinearMap.ext
  intro v
  exact (Hlevel s t).starProjection_eq_self_iff.mpr
    (frame_mem_Hlevel r t _ ((Hlevel s t).starProjection_apply_mem v))

theorem frame_projLevel_commute (s r t : ℕ) :
    (projLevel s t).comp (frame s r) = (frame s r).comp (projLevel s t) := by
  have ha : ContinuousLinearMap.adjoint (projLevel s t) = projLevel s t :=
    isSelfAdjoint_starProjection (Hlevel s t)
  have hh := congrArg ContinuousLinearMap.adjoint (projLevel_frame_projLevel s r t)
  simp only [ContinuousLinearMap.adjoint_comp, frame_adjoint, ha] at hh
  rw [ContinuousLinearMap.comp_assoc, projLevel_frame_projLevel] at hh
  exact hh.symm

theorem Gram_eq_frame_projLevel (s r : ℕ) :
    Gram s r = (frame s r).comp (projLevel s r) := by
  rw [Gram_eq_proj_frame_proj, projLevel_frame_projLevel]

/-- The unprojected synthesis map on databases with exactly r records. -/
noncomputable def synthesis (s r : ℕ) :
    Hil (InjDb s) →L[ℂ] Hil (Equiv.Perm (Fin s)) :=
  ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I.size = r),
    ketBra (completion I) (ket I)

lemma synthesis_apply (r : ℕ) (v : Hil (InjDb s)) :
    synthesis s r v = ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I.size = r),
      v I • completion I := by
  simp only [synthesis, ContinuousLinearMap.sum_apply, ketBra_apply, inner_ket]

theorem Gam_eq_projLevel_synthesis (s r : ℕ) :
    Gam s r = (projLevel s r).comp (synthesis s r) := by
  apply ContinuousLinearMap.ext
  intro v
  change Gam s r v = projLevel s r (synthesis s r v)
  simp only [Gam_apply, synthesis_apply, map_sum, map_smul]

theorem synthesis_adjoint_Gam (s r : ℕ) :
    (synthesis s r).comp (ContinuousLinearMap.adjoint (Gam s r)) = Gram s r := by
  rw [Gram_eq_frame_projLevel]
  apply ContinuousLinearMap.ext
  intro v
  change synthesis s r (ContinuousLinearMap.adjoint (Gam s r) v) = frame s r (projLevel s r v)
  rw [synthesis_apply]
  simp only [frame, ContinuousLinearMap.sum_apply, ketBra_apply]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Gam_adjoint_apply, if_pos (Finset.mem_filter.mp hI).2]
  congr 1
  exact (Hlevel s r).starProjection_isSymmetric (completion I) v

theorem synthesis_mem_Hlevel_of_mem_adjoint_range (r : ℕ) (v : Hil (InjDb s))
    (hv : v ∈ (ContinuousLinearMap.adjoint (Gam s r)).range) :
    synthesis s r v ∈ Hlevel s r := by
  obtain ⟨w, rfl⟩ := hv
  have he := congrArg (fun T : Hil (Equiv.Perm (Fin s)) →L[ℂ] Hil (Equiv.Perm (Fin s)) => T w)
    (synthesis_adjoint_Gam s r)
  change synthesis s r (ContinuousLinearMap.adjoint (Gam s r) w) = Gram s r w at he
  have hh : Gram s r w ∈ Hlevel s r := IntertwinerPartial.Gam_range s r _
  exact he.symm ▸ hh

theorem Gam_eq_synthesis_of_mem_adjoint_range (r : ℕ) (v : Hil (InjDb s))
    (hv : v ∈ (ContinuousLinearMap.adjoint (Gam s r)).range) :
    Gam s r v = synthesis s r v := by
  rw [Gam_eq_projLevel_synthesis]
  exact (Hlevel s r).starProjection_eq_self_iff.mpr
    (synthesis_mem_Hlevel_of_mem_adjoint_range r v hv)

end WeldedPath.CompletionFrame

end

-- Solutions.WeldedPathCompletionFrameAverage
section

namespace WeldedPath.CompletionFrame

open Classical
open scoped BigOperators

variable {s : ℕ}

def fixing (D : Finset (Fin s)) : Subgroup (Equiv.Perm (Fin s)) where
  carrier := {g | ∀ x ∈ D, g x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by intro g h hg hh x hx; change g (h x) = x; rw [hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    exact g.injective (by simpa using (hg x hx).symm)

noncomputable def fixingEquiv (D : Finset (Fin s)) :
    Equiv.Perm {x : Fin s // x ∉ D} ≃ fixing D :=
  (Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin s => x ∉ D)).trans
    (Equiv.subtypeEquivRight (fun g => by simp only [not_not]; rfl))

theorem fixing_card (D : Finset (Fin s)) :
    Fintype.card (fixing D) = (s-D.card).factorial := by
  rw [← Fintype.card_congr (fixingEquiv D), Fintype.card_perm,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

theorem centralKernel_eq_sum_fixing (r : ℕ) (g : Equiv.Perm (Fin s)) :
    centralKernel s r g = ∑ D ∈ (Finset.univ : Finset (Fin s)).powersetCard r,
      if g ∈ fixing D then ((s-r).factorial : ℂ)⁻¹ else 0 := by
  have hfilter : ((Finset.univ : Finset (Fin s)).powersetCard r).filter
      (fun D => g ∈ fixing D) = (agreement g 1).powersetCard r := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    change D.card = r ∧ (∀ x ∈ D, g x = x) ↔ D ⊆ agreement g 1 ∧ D.card = r
    have he : D ⊆ agreement g 1 ↔ ∀ x ∈ D, g x = x := by
      constructor
      · intro hh x hx
        exact (Finset.mem_filter.mp (hh hx)).2
      · intro hh x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh x hx⟩
    rw [he, and_comm]
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_powersetCard]
  simp only [centralKernel, frame_kernel, Complex.ofReal_div, Complex.ofReal_natCast,
    div_eq_mul_inv, nsmul_eq_mul]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

noncomputable def subgroupAverage (ρ : Representation ℂ (Equiv.Perm (Fin s)) V)
    (D : Finset (Fin s)) : V →ₗ[ℂ] V :=
  (Fintype.card (fixing D) : ℂ)⁻¹ • ∑ g : fixing D, ρ g.val

theorem subgroupAverage_isProj (ρ : Representation ℂ (Equiv.Perm (Fin s)) V)
    (D : Finset (Fin s)) :
    LinearMap.IsProj (Representation.invariants (ρ.comp (fixing D).subtype)) (subgroupAverage ρ D) := by
  letI : Invertible (Fintype.card (fixing D) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  convert Representation.isProj_averageMap (ρ.comp (fixing D).subtype) using 1
  simp [subgroupAverage, Representation.averageMap, GroupAlgebra.average, map_sum]

theorem subgroupAverage_trace [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V) (D : Finset (Fin s)) :
    LinearMap.trace ℂ V (subgroupAverage ρ D) =
      (Module.finrank ℂ (Representation.invariants (ρ.comp (fixing D).subtype)) : ℂ) :=
  (subgroupAverage_isProj ρ D).trace

theorem subgroupAverage_eq_sum (ρ : Representation ℂ (Equiv.Perm (Fin s)) V)
    (D : Finset (Fin s)) :
    subgroupAverage ρ D = ∑ g : Equiv.Perm (Fin s),
      (if g ∈ fixing D then ((s-D.card).factorial : ℂ)⁻¹ else 0) • ρ g := by
  simp only [subgroupAverage, fixing_card, Finset.smul_sum, ite_smul, zero_smul]
  rw [← Finset.sum_filter]
  simpa using
    (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Equiv.Perm (Fin s))))
      (p := fun g => g ∈ fixing D) (f := fun g => ((s-D.card).factorial : ℂ)⁻¹ • ρ g))

theorem kernelRepresentation_eq_sum_subgroupAverage
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V) (r : ℕ) :
    (∑ g, centralKernel s r g • ρ g) =
      ∑ D ∈ (Finset.univ : Finset (Fin s)).powersetCard r, subgroupAverage ρ D := by
  simp_rw [centralKernel_eq_sum_fixing, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [subgroupAverage_eq_sum, (Finset.mem_powersetCard.mp hD).2]

theorem kernelRepresentation_trace [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V) (r : ℕ) :
    LinearMap.trace ℂ V (∑ g, centralKernel s r g • ρ g) =
      ∑ D ∈ (Finset.univ : Finset (Fin s)).powersetCard r,
        (Module.finrank ℂ (Representation.invariants (ρ.comp (fixing D).subtype)) : ℂ) := by
  rw [kernelRepresentation_eq_sum_subgroupAverage, map_sum]
  apply Finset.sum_congr rfl
  intro D _
  exact subgroupAverage_trace ρ D

end WeldedPath.CompletionFrame


namespace WeldedPath.CompletionFrame

open Classical
open scoped BigOperators

section General
variable {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module ℂ V]

noncomputable def conjugateInvariants (ρ : Representation ℂ Γ V)
    (H K : Subgroup Γ) (g : Γ)
    (hconj : ∀ h, h ∈ K ↔ g⁻¹*h*g ∈ H) :
    (Representation.invariants (ρ.comp H.subtype)) ≃ₗ[ℂ] (Representation.invariants (ρ.comp K.subtype)) where
  toFun v := ⟨ρ g v.1, by
    intro h
    have hv := v.2 ⟨g⁻¹*h.val*g,(hconj h.val).mp h.2⟩
    change ρ (g⁻¹*h.val*g) v.1 = v.1 at hv
    change ρ h.val (ρ g v.1) = ρ g v.1
    calc
      _ = ρ g (ρ (g⁻¹*h.val*g) v.1) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 1
        group
      _ = _ := congrArg (ρ g) hv⟩
  invFun v := ⟨ρ g⁻¹ v.1, by
    intro h
    have hh : g*h.val*g⁻¹ ∈ K := (hconj _).mpr (by simpa [mul_assoc] using h.2)
    have hv := v.2 ⟨g*h.val*g⁻¹,hh⟩
    change ρ (g*h.val*g⁻¹) v.1 = v.1 at hv
    change ρ h.val (ρ g⁻¹ v.1) = ρ g⁻¹ v.1
    calc
      _ = ρ g⁻¹ (ρ (g*h.val*g⁻¹) v.1) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 1
        group
      _ = _ := congrArg (ρ g⁻¹) hv⟩
  left_inv v := by
    apply Subtype.ext
    change ρ g⁻¹ (ρ g v.1) = v.1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    apply Subtype.ext
    change ρ g (ρ g⁻¹ v.1) = v.1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' v w := by apply Subtype.ext; exact map_add (ρ g) v.1 w.1
  map_smul' c v := by apply Subtype.ext; exact map_smul (ρ g) c v.1
end General

variable {s : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem fixing_conjugacy (D E : Finset (Fin s)) (g : Equiv.Perm (Fin s))
    (hmap : D.map g.toEmbedding = E) (h : Equiv.Perm (Fin s)) :
    h ∈ fixing E ↔ g⁻¹*h*g ∈ fixing D := by
  constructor
  · intro hh x hx
    have hE : g x ∈ E := hmap ▸ Finset.mem_map.mpr ⟨x,hx,rfl⟩
    change g.symm (h (g x)) = x
    rw [hh (g x) hE, g.symm_apply_apply]
  · intro hh y hy
    rw [← hmap] at hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
    change h (g x) = g x
    have hp := congrArg g (hh x hx)
    change g (g.symm (h (g x))) = g x at hp
    simpa only [g.apply_symm_apply] using hp

theorem finrank_fixing_eq_of_card [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V)
    (D E : Finset (Fin s)) (hc : D.card = E.card) :
    Module.finrank ℂ (Representation.invariants (ρ.comp (fixing D).subtype)) =
      Module.finrank ℂ (Representation.invariants (ρ.comp (fixing E).subtype)) := by
  obtain ⟨g,hg⟩ := Equiv.Perm.exists_map_finset_eq D E hc
  exact (conjugateInvariants ρ (fixing D) (fixing E) g (fixing_conjugacy D E g hg)).finrank_eq

theorem kernelRepresentation_trace_eq [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V)
    (r : ℕ) (D : Finset (Fin s)) (hD : D.card = r) :
    LinearMap.trace ℂ V (∑ g, centralKernel s r g • ρ g) =
      (s.choose r : ℂ) * (Module.finrank ℂ (Representation.invariants (ρ.comp (fixing D).subtype)) : ℂ) := by
  rw [kernelRepresentation_trace]
  have he : ∀ E ∈ (Finset.univ : Finset (Fin s)).powersetCard r,
      (Module.finrank ℂ (Representation.invariants (ρ.comp (fixing E).subtype)) : ℂ) =
        Module.finrank ℂ (Representation.invariants (ρ.comp (fixing D).subtype)) := by
    intro E hE
    exact_mod_cast finrank_fixing_eq_of_card ρ E D ((Finset.mem_powersetCard.mp hE).2.trans hD.symm)
  rw [Finset.sum_congr rfl he, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

noncomputable def prefixComplement {m : ℕ} (h : m ≤ s) : Finset (Fin s) :=
  (Finset.univ.map (Fin.castLEEmb h))ᶜ

theorem prefixComplement_card {m : ℕ} (h : m ≤ s) :
    (prefixComplement h).card = s-m := by
  simp only [prefixComplement, Finset.card_compl, Fintype.card_fin,
    Finset.card_map, Finset.card_univ]

theorem viaEmbedding_mem_fixing_prefix {m : ℕ} (h : m ≤ s) (g : Equiv.Perm (Fin m)) :
    g.viaEmbedding (Fin.castLEEmb h) ∈ fixing (prefixComplement h) := by
  intro x hx
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨y,hy⟩
  exact (Finset.mem_compl.mp hx) (Finset.mem_map.mpr ⟨y, Finset.mem_univ _, hy⟩)

theorem prefix_invariants {m : ℕ} (h : m ≤ s)
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V) :
    (Representation.invariants (ρ.comp (fixing (prefixComplement h)).subtype)) =
      (Representation.invariants (ρ.comp (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h)))) := by
  let f : Equiv.Perm (Fin m) → fixing (prefixComplement h) :=
    fun g => ⟨g.viaEmbedding (Fin.castLEEmb h), viaEmbedding_mem_fixing_prefix h g⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb h) (congrArg Subtype.val hab)
  have hc : Fintype.card (Equiv.Perm (Fin m)) = Fintype.card (fixing (prefixComplement h)) := by
    rw [Fintype.card_perm, Fintype.card_fin, fixing_card, prefixComplement_card, Nat.sub_sub_self h]
  have hsurj : Function.Surjective f := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩).2
  ext v
  constructor
  · intro hv g
    exact hv (f g)
  · intro hv g
    obtain ⟨a,rfl⟩ := hsurj g
    exact hv a

theorem kernelRepresentation_trace_prefix [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V) (r : ℕ) (hr : r ≤ s) :
    LinearMap.trace ℂ V (∑ g, centralKernel s r g • ρ g) =
      (s.choose r : ℂ) *
        (Module.finrank ℂ (Representation.invariants (ρ.comp (Equiv.Perm.viaEmbeddingHom
          (Fin.castLEEmb (Nat.sub_le s r))))) : ℂ) := by
  rw [← prefix_invariants]
  apply kernelRepresentation_trace_eq
  rw [prefixComplement_card, Nat.sub_sub_self hr]

end WeldedPath.CompletionFrame

end

-- Solutions.WeldedPathCompletionFrameSpectral
section

namespace WeldedPath.CompletionFrame

open Classical OAI.PartialPermutation
open scoped BigOperators

variable {s : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [Nontrivial V]

/-- The Fourier eigenvalue of the actual completion frame on any irreducible
representation is the fixed-space dimension ratio, with its exact binomial factor. -/
theorem kernelRepresentation_scalar
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V) [Representation.IsIrreducible ρ]
    (r : ℕ) (hr : r ≤ s) :
    (∑ g, centralKernel s r g • ρ g) =
      (((s.choose r : ℂ) *
        (Module.finrank ℂ (Representation.invariants (ρ.comp
          (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (Nat.sub_le s r))))) : ℂ)) /
        (Module.finrank ℂ V : ℂ)) • (1 : Module.End ℂ V) := by
  obtain ⟨c,hc⟩ := centralFourier_scalar ρ (centralKernel s r) (centralKernel_comm r)
  have htrace := kernelRepresentation_trace_prefix ρ r hr
  change LinearMap.trace ℂ V (complexFourier ρ (centralKernel s r)) = _ at htrace
  rw [hc, map_smul, LinearMap.trace_one] at htrace
  have hn : (Module.finrank ℂ V : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
  have hval : c = ((s.choose r : ℂ) *
        (Module.finrank ℂ (Representation.invariants (ρ.comp
          (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (Nat.sub_le s r))))) : ℂ)) /
        (Module.finrank ℂ V : ℂ) := by
    apply (eq_div_iff hn).mpr
    exact htrace
  change complexFourier ρ (centralKernel s r) = _
  rw [hc, hval]

end WeldedPath.CompletionFrame

end

-- Solutions.YoungFrameConditioningComplete
section

-- MODULE YoungFrameRatio
section

namespace WeldedPath.YoungCounts

noncomputable section
open Classical
open scoped BigOperators

lemma prependRow_rowLen_succ (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) (i : ℕ) :
    (prependRow m ν hm).rowLen (i+1) = ν.rowLen i := by
  rw [← rowTail_rowLen, rowTail_prependRow]

lemma prependRow_colLen (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m)
    (j : ℕ) (hj : j < m) : (prependRow m ν hm).colLen j = ν.colLen j + 1 := by
  apply eq_of_forall_lt_iff
  intro i
  rw [← YoungDiagram.mem_iff_lt_colLen, mem_prependRow]
  simp only [Prod.fst, Prod.snd, YoungDiagram.mem_iff_lt_colLen]
  omega

lemma hook_prepend_top (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m)
    (j : ℕ) (hj : j < m) : hook (prependRow m ν hm) (0,j) = m-j+ν.colLen j := by
  rw [X7hk_hook, prependRow_rowLen, prependRow_colLen m ν hm j hj]
  omega

lemma hook_prepend_lower (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m)
    (z : Cell) (hz : z ∈ ν.cells) :
    hook (prependRow m ν hm) (rowShift z) = hook ν z := by
  have hj : z.2 < m :=
    (ν.mem_iff_lt_rowLen.mp hz).trans_le ((ν.rowLen_anti 0 z.1 (Nat.zero_le _)).trans hm)
  change hook (prependRow m ν hm) (z.1+1,z.2) = hook ν (z.1,z.2)
  rw [X7hk_hook, X7hk_hook, prependRow_rowLen_succ, prependRow_colLen m ν hm z.2 hj]
  omega

lemma hookProduct_pos (ν : YoungDiagram) : 0 < hookProduct ν := by
  apply Finset.prod_pos
  intro z hz
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (X7hk_hook_ge ν z))

theorem hookProduct_prependRow (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) :
    hookProduct (prependRow m ν hm) =
      (∏ j ∈ Finset.range m, ((m-j+ν.colLen j : ℕ) : ℚ)) * hookProduct ν := by
  unfold hookProduct
  change (∏ z ∈ ({0} ×ˢ Finset.range m) ∪ ν.cells.map rowShift,
    (hook (prependRow m ν hm) z : ℚ)) = _
  rw [Finset.prod_union]
  · rw [Finset.prod_product, Finset.prod_singleton, Finset.prod_map]
    congr 1
    · apply Finset.prod_congr rfl
      intro j hj
      rw [hook_prepend_top m ν hm j (Finset.mem_range.mp hj)]
    · apply Finset.prod_congr rfl
      intro z hz
      rw [hook_prepend_lower m ν hm z hz]
  · apply Finset.disjoint_left.mpr
    intro z hz hz'
    have hz0 : z.1=0 := Finset.mem_singleton.mp (Finset.mem_product.mp hz).1
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hz'
    simpa [rowShift] using hz0

lemma descending_product (m : ℕ) :
    (∏ j ∈ Finset.range m, (m-j : ℕ)) = m.factorial := by
  rw [← Finset.prod_range_add_one_eq_factorial]
  calc
    _ = ∏ j ∈ Finset.range m, (m-1-j+1) := by
      apply Finset.prod_congr rfl
      intro j hj
      have := Finset.mem_range.mp hj
      omega
    _ = _ := Finset.prod_range_reflect (fun j => j+1) m

theorem frame_ratio_eq_product (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) :
    (((m+ν.card).choose ν.card : ℕ) : ℚ) * (tableauCount ν : ℚ) /
      (tableauCount (prependRow m ν hm) : ℚ) =
      ∏ j ∈ Finset.range m, (1 + (ν.colLen j : ℚ) / (m-j : ℕ)) := by
  have hp := hookProduct_prependRow m ν hm
  have hν := ne_of_gt (hookProduct_pos ν)
  have hf : ((m+ν.card).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hmfac : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hc : (((m+ν.card).choose ν.card : ℕ) : ℚ) * (ν.card.factorial : ℚ) *
      (m.factorial : ℚ) = ((m+ν.card).factorial : ℚ) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left ν.card m)
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right, Nat.cast_mul] using
      congrArg (fun k : ℕ => (k : ℚ)) hnat
  have hP : (∏ j ∈ Finset.range m, ((m-j+ν.colLen j : ℕ) : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hj' : j < m := Finset.mem_range.mp hj
    exact_mod_cast (by omega : m-j+ν.colLen j ≠ 0)
  rw [hookLengthFormula, hookLengthFormula, prependRow_card, hp]
  calc
    _ = (∏ j ∈ Finset.range m, ((m-j+ν.colLen j : ℕ) : ℚ)) / (m.factorial : ℚ) := by
      field_simp [hν, hf, hmfac, hP]
      nlinarith [hc]
    _ = ∏ j ∈ Finset.range m, (((m-j+ν.colLen j : ℕ) : ℚ) / (m-j : ℕ)) := by
      rw [Finset.prod_div_distrib]
      congr 1
      exact_mod_cast (descending_product m).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj' : j < m := Finset.mem_range.mp hj
      have hd : ((m-j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : m-j≠0)
      push_cast
      field_simp

end
end WeldedPath.YoungCounts

namespace WeldedPath.YoungSpechtDimension
noncomputable section
open OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open YoungCounts
open scoped BigOperators

theorem specht_frame_ratio_eq_product (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) :
    (((m+ν.card).choose ν.card : ℕ) : ℚ) *
      (Module.finrank ℂ (spechtSub ν).toSubmodule : ℚ) /
      (Module.finrank ℂ (spechtSub (prependRow m ν hm)).toSubmodule : ℚ) =
      ∏ j ∈ Finset.range m, (1 + (ν.colLen j : ℚ) / (m-j : ℕ)) := by
  rw [← standardCount_eq_specht_finrank, ← standardCount_eq_specht_finrank,
    ← tableauCount_eq_standardCount, ← tableauCount_eq_standardCount]
  exact frame_ratio_eq_product m ν hm

end
end WeldedPath.YoungSpechtDimension
end

-- MODULE YoungFrameBounds
section

namespace WeldedPath.YoungCounts

noncomputable section
open Classical
open scoped BigOperators

lemma sum_colLen (ν : YoungDiagram) (m : ℕ) (hm : ν.rowLen 0 ≤ m) :
    (∑ j ∈ Finset.range m, ν.colLen j) = ν.card := by
  symm
  have h := Finset.card_eq_sum_card_fiberwise
    (f := Prod.snd) (s := ν.cells) (t := Finset.range m) (by
      intro z hz
      apply Finset.mem_range.mpr
      exact (ν.mem_iff_lt_rowLen.mp hz).trans_le
        ((ν.rowLen_anti 0 z.1 (Nat.zero_le _)).trans hm))
  simpa only [YoungDiagram.card, YoungDiagram.colLen_eq_card, YoungDiagram.col] using h

lemma colLen_eq_zero_of_rowLen_le (ν : YoungDiagram) (j : ℕ) (hj : ν.rowLen 0 ≤ j) :
    ν.colLen j = 0 := by
  by_contra hn
  have hc : (0,j) ∈ ν := ν.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero hn)
  have hr := ν.mem_iff_lt_rowLen.mp hc
  omega

def frameProduct (m : ℕ) (ν : YoungDiagram) : ℝ :=
  ∏ j ∈ Finset.range m, (1 + (ν.colLen j : ℝ) / (m-j : ℕ))

theorem frameProduct_one_le (m : ℕ) (ν : YoungDiagram) : 1 ≤ frameProduct m ν := by
  apply Finset.one_le_prod
  intro j hj
  have hp : (0 : ℝ) ≤ (ν.colLen j : ℝ) / (m-j : ℕ) := by positivity
  linarith

lemma frame_exponent_le (m : ℕ) (ν : YoungDiagram) (hm : ν.card ≤ m) :
    (∑ j ∈ Finset.range m, (ν.colLen j : ℝ) / (m-j : ℕ)) ≤
      (ν.card : ℝ) / (m-ν.card+1 : ℕ) := by
  have hrow : ν.rowLen 0 ≤ ν.card := OAI.PartialPermutation.DiagramCounting.rowLen_le_card ν 0
  have hd : (0 : ℝ) < (m-ν.card+1 : ℕ) := by positivity
  calc
    _ ≤ ∑ j ∈ Finset.range m, (ν.colLen j : ℝ) / (m-ν.card+1 : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hz : ν.colLen j = 0
      · simp only [hz, Nat.cast_zero, zero_div, le_refl]
      · have hjr : j < ν.card := by
          by_contra hjr
          exact hz (colLen_eq_zero_of_rowLen_le ν j (hrow.trans (Nat.le_of_not_gt hjr)))
        have hden : (m-ν.card+1 : ℕ) ≤ m-j := by omega
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (by exact_mod_cast hden)
    _ = _ := by
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast sum_colLen ν m (hrow.trans hm)

theorem frameProduct_le_exp (m : ℕ) (ν : YoungDiagram) (hm : ν.card ≤ m) :
    frameProduct m ν ≤ Real.exp ((ν.card : ℝ) / (m-ν.card+1 : ℕ)) := by
  exact (Real.prod_one_add_le_exp_sum (Finset.range m) (fun j => by positivity)).trans
    (Real.exp_le_exp.mpr (frame_exponent_le m ν hm))

theorem frameProduct_le_two (m : ℕ) (ν : YoungDiagram) (hm : 3*ν.card ≤ m) :
    frameProduct m ν ≤ 2 := by
  have hmc : ν.card ≤ m := by omega
  have hd : (0 : ℝ) < (m-ν.card+1 : ℕ) := by positivity
  have hhalf : (ν.card : ℝ) / (m-ν.card+1 : ℕ) ≤ 1/2 := by
    apply (div_le_iff₀ hd).mpr
    have hb : 2*ν.card ≤ m-ν.card+1 := by omega
    have hb' : 2*(ν.card : ℝ) ≤ (m-ν.card+1 : ℕ) := by exact_mod_cast hb
    linarith
  have he : Real.exp (1/2 : ℝ) ≤ 2 := by
    convert Real.exp_bound_div_one_sub_of_interval (x := (1/2 : ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  exact (frameProduct_le_exp m ν hmc).trans ((Real.exp_le_exp.mpr hhalf).trans he)

end
end WeldedPath.YoungCounts

namespace WeldedPath.YoungSpechtDimension
noncomputable section
open OAI.PartialPermutation.YoungTabloid
open YoungCounts

theorem specht_frame_ratio_real (m : ℕ) (ν : YoungDiagram) (hm : ν.rowLen 0 ≤ m) :
    (((m+ν.card).choose ν.card : ℕ) : ℝ) *
      (Module.finrank ℂ (spechtSub ν).toSubmodule : ℝ) /
      (Module.finrank ℂ (spechtSub (prependRow m ν hm)).toSubmodule : ℝ) =
      frameProduct m ν := by
  have he := congrArg (fun q : ℚ => (q : ℝ)) (specht_frame_ratio_eq_product m ν hm)
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_prod,
    Rat.cast_add, Rat.cast_one, frameProduct] using he

theorem specht_frame_ratio_bounds (m : ℕ) (ν : YoungDiagram) (hm : 3*ν.card ≤ m) :
    let hrow : ν.rowLen 0 ≤ m :=
      (OAI.PartialPermutation.DiagramCounting.rowLen_le_card ν 0).trans (by change ν.card ≤ m; omega)
    let ratio := (((m+ν.card).choose ν.card : ℕ) : ℝ) *
      (Module.finrank ℂ (spechtSub ν).toSubmodule : ℝ) /
      (Module.finrank ℂ (spechtSub (prependRow m ν hrow)).toSubmodule : ℝ)
    1 ≤ ratio ∧ ratio ≤ 2 := by
  dsimp only
  rw [specht_frame_ratio_real]
  exact ⟨frameProduct_one_le m ν, frameProduct_le_two m ν hm⟩

end
end WeldedPath.YoungSpechtDimension
end

-- MODULE YoungFrameSpectral
section

namespace WeldedPath.CompletionFrame

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open YoungCounts YoungBranching
open scoped BigOperators

theorem centralKernel_specht_scalar {s : ℕ} (μ : DiagramCounting.Shape s)
    (r : ℕ) (hr : r ≤ s) (hrow : μ.1.rowLen 0 = s-r) :
    (∑ g, centralKernel s r g • SpechtActual.rep μ g) =
      (frameProduct (s-r) (rowTail μ.1) : ℂ) •
        (1 : Module.End ℂ (spechtSub μ.1).toSubmodule) := by
  haveI : Nontrivial (spechtSub μ.1).toSubmodule := by
    refine ⟨⟨⟨polytabloid μ.1,polytabloid_mem_specht μ.1⟩,0,?_⟩⟩
    intro he
    exact polytabloid_ne_zero μ.1 (congrArg Subtype.val he)
  have hd := initial_invariants_dimension_firstRow μ (Nat.sub_le s r) hrow
  have ht : (rowTail μ.1).card = r := by
    have hc := rowTail_card μ.1
    have hsize : μ.1.card = s := μ.2
    omega
  have he := YoungSpechtDimension.specht_frame_ratio_real
    (μ.1.rowLen 0) (rowTail μ.1) (rowTail_rowLen_le μ.1)
  rw [prependRow_rowTail, ht, hrow, Nat.sub_add_cancel hr] at he
  have hec : ((s.choose r : ℂ) *
      (Module.finrank ℂ (spechtSub (rowTail μ.1)).toSubmodule : ℂ)) /
      (Module.finrank ℂ (spechtSub μ.1).toSubmodule : ℂ) =
      (frameProduct (s-r) (rowTail μ.1) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] using
      congrArg Complex.ofReal he
  rw [kernelRepresentation_scalar (SpechtActual.rep μ) r hr]
  change (_ * (Module.finrank ℂ (initialRep μ (Nat.sub_le s r)).invariants : ℂ) / _) • _ = _
  rw [hd, hec]

theorem centralKernel_specht_conditioned {s : ℕ} (μ : DiagramCounting.Shape s)
    (r : ℕ) (hsmall : 4*r ≤ s) (hrow : μ.1.rowLen 0 = s-r) :
    ∃ c : ℝ, 1 ≤ c ∧ c ≤ 2 ∧
      (∑ g, centralKernel s r g • SpechtActual.rep μ g) =
        (c : ℂ) • (1 : Module.End ℂ (spechtSub μ.1).toSubmodule) := by
  have hr : r ≤ s := by omega
  have ht : (rowTail μ.1).card = r := by
    have hc := rowTail_card μ.1
    have hsize : μ.1.card = s := μ.2
    omega
  refine ⟨frameProduct (s-r) (rowTail μ.1), frameProduct_one_le _ _, ?_,
    centralKernel_specht_scalar μ r hr hrow⟩
  apply frameProduct_le_two
  rw [ht]
  omega

end
end WeldedPath.CompletionFrame
end




end

-- Solutions.CompressedPermutationAction
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb HilbertSupport
open scoped BigOperators ComplexConjugate

variable {s : ℕ}

theorem plus_inner_ket_added (I J : InjDb s) (x y : Fin s)
    (hI : I x = none) (hJ : J x = none) (hy : J.symm y = none) :
    inner ℂ (plusState I x) (ket (J.addPair x y)) =
      if I = J then ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) else 0 := by
  unfold plusState
  rw [inner_smul_left, sum_inner]
  by_cases hij : I = J
  · subst J
    rw [if_pos rfl]
    have hs : (∑ z ∈ Finset.univ.filter (fun z => I.symm z = none),
        inner ℂ (ket (I.addPair x z)) (ket (I.addPair x y))) = 1 := by
      rw [Finset.sum_eq_single y]
      · rw [ket_inner, if_pos rfl]
      · intro z hz hzy
        rw [ket_inner, if_neg]
        exact fun he => hzy (addPair_injective I x hI
          (Finset.mem_filter.mp hz).2 hy he)
      · intro hn
        exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)).elim
    rw [hs]
    simp
  · rw [if_neg hij]
    have hs : (∑ z ∈ Finset.univ.filter (fun z => I.symm z = none),
        inner ℂ (ket (I.addPair x z)) (ket (J.addPair x y))) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      rw [ket_inner, if_neg]
      exact fun he => hij (addPair_eq_original I J x z y hI
        (Finset.mem_filter.mp hz).2 hJ hy he)
    rw [hs, mul_zero]

theorem ket_inner_added (I J : InjDb s) (x y : Fin s)
    (hI : I x = none) (hJ : J x = none) (hy : J.symm y = none) :
    inner ℂ (ket I) (ket (J.addPair x y)) = 0 := by
  rw [ket_inner, if_neg]
  intro he
  have hh := congrArg (fun K : InjDb s => K x) he
  rw [hI, addPair_apply_self J x y hJ hy] at hh
  cases hh

theorem pC_ket_unset (I : InjDb s) (x : Fin s) (hx : I x = none) :
    pC s x (ket I) = plusState I x := by
  have hterm (J : InjDb s) (hJ : J x = none) :
      (pCF (plusState J x) (ket J) - 1) (ket I) =
        if J = I then plusState I x - ket I else 0 := by
    have hp : inner ℂ (plusState J x) (ket I) = 0 := by
      rw [← inner_conj_symm, ket_inner_plus_other I J x hx hJ]
      simp
    change pCF _ _ _ - ket I = _
    rw [pCF_apply, hp, ket_inner]
    by_cases hji : J = I
    · subst J
      simp
    · simp [hji]
  unfold pC
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.sum_apply]
  have hs : (∑ J ∈ Finset.univ.filter (fun J : InjDb s => J x = none),
      (pCF (plusState J x) (ket J) - 1) (ket I)) = plusState I x - ket I := by
    rw [Finset.sum_eq_single I]
    · simpa only [ite_true] using hterm I hx
    · intro J hJ hji
      rw [hterm J (Finset.mem_filter.mp hJ).2, if_neg hji]
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)).elim
  rw [hs]
  abel

theorem pC_ket_added (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) :
    pC s x (ket (I.addPair x y)) = ket (I.addPair x y) +
      ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) • (ket I - plusState I x) := by
  have hterm (J : InjDb s) (hJ : J x = none) :
      (pCF (plusState J x) (ket J) - 1) (ket (I.addPair x y)) =
        if J = I then ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) •
          (ket I - plusState I x) else 0 := by
    change pCF _ _ _ - ket (I.addPair x y) = _
    rw [pCF_apply, ket_inner_added J I x y hJ hx hy,
      plus_inner_ket_added J I x y hJ hx hy]
    by_cases hji : J = I
    · subst J
      simp only [ite_true, zero_smul, sub_zero, add_zero]
      module
    · simp [hji]
  unfold pC
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.sum_apply]
  congr 1
  rw [Finset.sum_eq_single I]
  · simpa only [ite_true] using hterm I hx
  · intro J hJ hji
    rw [hterm J (Finset.mem_filter.mp hJ).2, if_neg hji]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)).elim

theorem pC_added_error_sq (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) :
    ‖(pC s x - 1) (ket (I.addPair x y))‖ ^ 2 =
      2 / ((s - I.size : ℕ) : ℝ) := by
  have hket : ‖ket I‖ ^ 2 = 1 := by
    calc
      _ = (inner ℂ (ket I) (ket I)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = 1 := by rw [ket_inner, if_pos rfl]; rfl
  have hplus : ‖plusState I x‖ ^ 2 = 1 := by
    calc
      _ = (inner ℂ (plusState I x) (plusState I x)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = 1 := by rw [plusState_inner_self I x hx]; rfl
  have hdiff : ‖ket I - plusState I x‖ ^ 2 = 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), ket_inner_plusState I x hx, hket, hplus]
    norm_num
  have he : (pC s x - 1) (ket (I.addPair x y)) =
      ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) • (ket I - plusState I x) := by
    change pC s x _ - ket (I.addPair x y) = _
    rw [pC_ket_added I x y hx hy]
    abel
  rw [he, norm_smul, mul_pow, hdiff, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathCoefficientStability
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem norm_sum_sq_le_card_sum {ι : Type*} [Fintype ι] (v : ι → E) :
    ‖∑ i, v i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
  have hs := norm_sum_le (Finset.univ : Finset ι) v
  have hsq : ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr hs
  exact hsq.trans (by simpa using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖v i‖)))

/-- Components lying in the discarded kernel have zero inner product with a minimal
representative. Removing those components cannot decrease the norm of its collision projection. -/
theorem collision_remove_kernel (K C : Submodule ℂ E) (f k r : E)
    (hf : f ∈ Kᗮ) (hk : k ∈ K) (hkC : k ∈ C)
    (hdec : C.starProjection f = k + r) :
    ‖C.starProjection f‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  have horth : inner ℂ (C.starProjection f) k = 0 := by
    rw [C.inner_starProjection_left_eq_right,
      C.starProjection_eq_self_iff.mpr hkC]
    exact (K.mem_orthogonal' f).mp hf k hk
  have hneg : inner ℂ (C.starProjection f) (-k) = 0 := by
    simp only [inner_neg_right, horth, neg_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (C.starProjection f) (-k) hneg
  have he : C.starProjection f + -k = r := by rw [hdec]; abel
  rw [he, norm_neg] at hpy
  nlinarith [sq_nonneg ‖k‖]

/-- The collision estimate on arbitrary coefficient combinations. Fixed collision
parts lie in the discarded kernel; free parts are bounded separately, and their
energy is controlled by the orthogonal coefficient decomposition. -/
theorem collision_from_decomposition {ι : Type*} [Fintype ι]
    (K C : Submodule ℂ E) (f : E) (hf : f ∈ Kᗮ)
    (v k r : ι → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hdec : C.starProjection f = (∑ i, k i) + ∑ i, r i)
    (hk : ∀ i, k i ∈ K) (hkC : ∀ i, k i ∈ C)
    (hr : ∀ i, ‖r i‖ ^ 2 ≤ ε * ‖v i‖ ^ 2)
    (henergy : (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖C.starProjection f‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖∑ i, r i‖ ^ 2 := collision_remove_kernel K C f _ _ hf
      (K.sum_mem fun i _ => hk i) (C.sum_mem fun i _ => hkC i) hdec
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, ‖r i‖ ^ 2 := norm_sum_sq_le_card_sum r
    _ ≤ (Fintype.card ι : ℝ) * (ε * ∑ i, ‖v i‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hr i
    _ ≤ (Fintype.card ι : ℝ) * (ε * ‖f‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy hε) (by positivity)
    _ = _ := by ring

theorem projection_injective_on_minimal (S R : Submodule ℂ E) {f g : E}
    (hfS : f ∈ S) (hgS : g ∈ S)
    (hf : f ∈ (S ⊓ Rᗮ)ᗮ) (hg : g ∈ (S ⊓ Rᗮ)ᗮ)
    (he : R.starProjection f = R.starProjection g) : f = g := by
  have hzero : R.starProjection (f - g) = 0 := by rw [map_sub, he, sub_self]
  have hker : f - g ∈ S ⊓ Rᗮ :=
    ⟨S.sub_mem hfS hgS, R.starProjection_apply_eq_zero_iff.mp hzero⟩
  have horth : f - g ∈ (S ⊓ Rᗮ)ᗮ := (S ⊓ Rᗮ)ᗮ.sub_mem hf hg
  have heq : f - g = 0 := inner_self_eq_zero.mp
    (((S ⊓ Rᗮ).mem_orthogonal (f - g)).mp horth (f - g) hker)
  exact sub_eq_zero.mp heq

/-- The stable coefficient representative: remove the kernel of the injectivity
projection, then use the collision estimate to bound the representative's energy. -/
theorem stable_representative (S R : Submodule ℂ E)
    (hsmall : ∀ f ∈ S, f ∈ (S ⊓ Rᗮ)ᗮ →
      ‖Rᗮ.starProjection f‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖f‖ ^ 2)
    (f₀ : E) (hf₀ : f₀ ∈ S) :
    ∃! f : E, f ∈ S ∧ f ∈ (S ⊓ Rᗮ)ᗮ ∧
      R.starProjection f = R.starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖R.starProjection f₀‖ ^ 2 := by
  let K : Submodule ℂ E := S ⊓ Rᗮ
  let f := f₀ - K.starProjection f₀
  have hk : K.starProjection f₀ ∈ K := K.starProjection_apply_mem _
  have hfS : f ∈ S := S.sub_mem hf₀ hk.1
  have hfK : f ∈ Kᗮ := K.sub_starProjection_mem_orthogonal f₀
  have hRf : R.starProjection f = R.starProjection f₀ := by
    dsimp [f]
    rw [map_sub, R.starProjection_apply_eq_zero_iff.mpr hk.2, sub_zero]
  have hbound : ‖f‖ ^ 2 ≤ 2 * ‖R.starProjection f₀‖ ^ 2 := by
    have hp := R.norm_sq_eq_add_norm_sq_starProjection f
    have hs := hsmall f hfS hfK
    rw [hRf] at hp
    linarith
  refine ⟨f, ⟨hfS, hfK, hRf, hbound⟩, ?_⟩
  intro g hg
  exact projection_injective_on_minimal S R hg.1 hfS hg.2.1 hfK (hg.2.2.1.trans hRf.symm)

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathOrthogonalCollision
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι]

theorem norm_sum_sq_orthogonal (v : ι → E)
    (horth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  have aux (s : Finset ι) : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hz : inner ℂ (v i) (∑ j ∈ s, v j) = 0 := by
        rw [inner_sum]
        exact Finset.sum_eq_zero (fun j hj => horth i j (fun he => hi (he ▸ hj)))
      have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v i) (∑j∈s,v j) hz
      simpa only [← pow_two, ih] using hp
  exact aux Finset.univ

/-- In a collision-orthogonal decomposition, fixed collision pieces vanish
individually by minimality. The remaining estimates add without a term-count
loss, which is essential for collisions between distinct graph components. -/
theorem orthogonal_collision_bound (K C : Submodule ℂ E)
    (f : E) (hf : f ∈ Kᗮ) (v : ι → E) (hdec : (∑ i, v i) = f)
    (horth : ∀ i j, i ≠ j →
      inner ℂ (C.starProjection (v i)) (C.starProjection (v j)) = 0)
    (fixed : ι → Prop)
    (hfixed : ∀ i, fixed i → C.starProjection (v i) ∈ K)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hfree : ∀ i, ¬fixed i → ‖C.starProjection (v i)‖ ^ 2 ≤ ε * ‖v i‖ ^ 2)
    (henergy : (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖C.starProjection f‖ ^ 2 ≤ ε * ‖f‖ ^ 2 := by
  classical
  have hzero (i : ι) (hi : fixed i) : C.starProjection (v i) = 0 := by
    have hz : inner ℂ (C.starProjection f) (C.starProjection (v i)) = 0 := by
      rw [C.inner_starProjection_left_eq_right,
        C.starProjection_eq_self_iff.mpr (C.starProjection_apply_mem _)]
      exact (K.mem_orthogonal' f).mp hf _ (hfixed i hi)
    rw [← hdec, map_sum, sum_inner] at hz
    have he : (∑ j, inner ℂ (C.starProjection (v j)) (C.starProjection (v i))) =
        inner ℂ (C.starProjection (v i)) (C.starProjection (v i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact horth j i hji
      · simp
    rw [he] at hz
    exact inner_self_eq_zero.mp hz
  calc
    ‖C.starProjection f‖ ^ 2 = ∑ i, ‖C.starProjection (v i)‖ ^ 2 := by
      rw [← hdec, map_sum]
      exact norm_sum_sq_orthogonal _ horth
    _ ≤ ∑ i, ε * ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : fixed i
      · rw [hzero i hi, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        exact mul_nonneg hε (sq_nonneg _)
      · exact hfree i hi
    _ = ε * ∑ i, ‖v i‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ε * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left henergy hε

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathControlledOperators
section

namespace WeldedPath.ControlledOperators

open Classical HilbertSupport EncodedOracleUnitary
open scoped BigOperators

variable {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq X]

theorem controlled_apply (T : C → Hil X →L[ℂ] Hil Y)
    (ψ : Hil (C × X)) (c : C) (y : Y) :
    controlled T ψ (c, y) = T c (slice ψ c) y := by
  conv_rhs => rw [← sum_basis (slice ψ c)]
  simp [controlled, opTensor, ketBra_apply, inner_ket, ketTensor_apply,
    Fintype.sum_prod_type, ket_apply, slice, apply_ite, ite_apply]

theorem controlled_norm_le (T : C → Hil X →L[ℂ] Hil Y)
    (hT : ∀ c ψ, ‖T c ψ‖ ≤ ‖ψ‖) (ψ : Hil (C × X)) :
    ‖controlled T ψ‖ ≤ ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← sum_slice_norm_sq, ← sum_slice_norm_sq]
  apply Finset.sum_le_sum
  intro c _
  have hs : slice (controlled T ψ) c = T c (slice ψ c) := by
    ext y
    exact controlled_apply T ψ c y
  rw [hs]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hT c _)

theorem controlled_opNorm_le (T : C → Hil X →L[ℂ] Hil Y)
    (hT : ∀ c ψ, ‖T c ψ‖ ≤ ‖ψ‖) : ‖controlled T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using controlled_norm_le T hT ψ

end WeldedPath.ControlledOperators

end

-- Solutions.CompressedPermutationRetained
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb HilbertSupport CoefficientStability
open scoped BigOperators ComplexConjugate

variable {s : ℕ}

noncomputable def eraseAt (I : InjDb s) (x : Fin s) : InjDb s :=
  (PEquiv.ofSet {u : Fin s | u ≠ x}).trans I

theorem eraseAt_apply (I : InjDb s) (x u : Fin s) :
    eraseAt I x u = if u = x then none else I u := by
  by_cases h : u = x <;> simp [eraseAt, PEquiv.trans, PEquiv.ofSet, h]

theorem eraseAt_self (I : InjDb s) (x : Fin s) : eraseAt I x x = none := by
  rw [eraseAt_apply, if_pos rfl]

theorem eraseAt_unused (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    (eraseAt I x).symm y = none := by
  cases hh : (eraseAt I x).symm y with
  | none => rfl
  | some u =>
    have hu := ((eraseAt I x).inv u y).mp hh
    change eraseAt I x u = some y at hu
    rw [eraseAt_apply] at hu
    by_cases hux : u = x
    · rw [if_pos hux] at hu
      cases hu
    · rw [if_neg hux] at hu
      have he := (I.inv u y).mpr hu
      rw [(I.inv x y).mpr hxy] at he
      exact (hux (Option.some.inj he).symm).elim

theorem eraseAt_add (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    (eraseAt I x).addPair x y = I := by
  apply PEquiv.ext
  intro u
  by_cases hu : u = x
  · subst u
    rw [addPair_apply_self _ _ _ (eraseAt_self I x) (eraseAt_unused I x y hxy), hxy]
  · rw [addPair_apply_other _ _ _ _ (eraseAt_self I x) (eraseAt_unused I x y hxy) hu,
      eraseAt_apply, if_neg hu]

theorem eraseAt_size (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    (eraseAt I x).size + 1 = I.size := by
  rw [← CompletionLevels.size_addPair (eraseAt I x) x y (eraseAt_self I x)
    (eraseAt_unused I x y hxy), eraseAt_add I x y hxy]

theorem pC_known_error (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    (pC s x - 1) (ket I) =
      ((Real.sqrt ((s - (eraseAt I x).size : ℕ) : ℝ))⁻¹ : ℂ) •
        (ket (eraseAt I x) - plusState (eraseAt I x) x) := by
  have he := pC_ket_added (eraseAt I x) x y (eraseAt_self I x) (eraseAt_unused I x y hxy)
  rw [eraseAt_add I x y hxy] at he
  change pC s x (ket I) - ket I = _
  rw [he]
  abel

theorem pC_known_error_sq (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    ‖(pC s x - 1) (ket I)‖ ^ 2 = 2 / ((s - I.size + 1 : ℕ) : ℝ) := by
  have he := pC_added_error_sq (eraseAt I x) x y (eraseAt_self I x)
    (eraseAt_unused I x y hxy)
  rw [eraseAt_add I x y hxy] at he
  have hsize := eraseAt_size I x y hxy
  have hle := CompletionLevels.size_le I
  have harith : s - (eraseAt I x).size = s - I.size + 1 := by omega
  simpa only [harith] using he

theorem pC_known_error_orthogonal (I J : InjDb s) (x y : Fin s)
    (hI : I x = some y) (hJ : J x = some y) (hIJ : I ≠ J) :
    inner ℂ ((pC s x - 1) (ket I)) ((pC s x - 1) (ket J)) = 0 := by
  have hb : eraseAt I x ≠ eraseAt J x := by
    intro he
    have hh := congrArg (fun K : InjDb s => K.addPair x y) he
    rw [eraseAt_add I x y hI, eraseAt_add J x y hJ] at hh
    exact hIJ hh
  have hp : inner ℂ (plusState (eraseAt I x) x) (ket (eraseAt J x)) = 0 := by
    rw [← inner_conj_symm,
      ket_inner_plus_other _ _ x (eraseAt_self J x) (eraseAt_self I x)]
    simp
  rw [pC_known_error I x y hI, pC_known_error J x y hJ,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    inner_sub_right, ket_inner, if_neg hb,
    ket_inner_plus_other _ _ x (eraseAt_self I x) (eraseAt_self J x), hp,
    plus_inner_plus_other _ _ x (eraseAt_self I x) (eraseAt_self J x) hb]
  simp

/-- Keeping the answer y distinguishes the otherwise overlapping compression
errors, giving a bound uniform over coherent superpositions of databases. -/
theorem pC_retained_slice_bound (x y : Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (InjDb s))
    (hψ : ∀ I, ψ I ≠ 0 → I x = some y ∧ I.size ≤ r) :
    ‖(pC s x - 1) ψ‖ ^ 2 ≤
      (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ ^ 2 := by
  let T := pC s x - 1
  have ho : ∀ I J : InjDb s, I ≠ J →
      inner ℂ (ψ I • T (ket I)) (ψ J • T (ket J)) = 0 := by
    intro I J hIJ
    by_cases hi : ψ I = 0
    · simp [hi]
    by_cases hj : ψ J = 0
    · simp [hj]
    rw [inner_smul_left, inner_smul_right,
      pC_known_error_orthogonal I J x y (hψ I hi).1 (hψ J hj).1 hIJ]
    simp
  have he : T ψ = ∑ I, ψ I • T (ket I) := by
    conv_lhs => rw [← sum_basis ψ]
    simp only [map_sum, map_smul]
  change ‖T ψ‖ ^ 2 ≤ _
  rw [he, norm_sum_sq_orthogonal _ ho, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  by_cases hi : ψ I = 0
  · simp [hi]
  obtain ⟨hxy, hsize⟩ := hψ I hi
  rw [norm_smul, mul_pow, pC_known_error_sq I x y hxy]
  have hd : (s - r + 1 : ℕ) ≤ s - I.size + 1 := by omega
  have hb : (2 : ℝ) / ((s - I.size + 1 : ℕ) : ℝ) ≤
      2 / ((s - r + 1 : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast hd
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (sq_nonneg ‖ψ I‖)

theorem pC_retained_bound (x : Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (Fin s × InjDb s))
    (hψ : ∀ y I, ψ (y, I) ≠ 0 → I x = some y ∧ I.size ≤ r) :
    ‖opTensor (1 : Hil (Fin s) →L[ℂ] Hil (Fin s)) (pC s x - 1) ψ‖ ^ 2 ≤
      (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ ^ 2 := by
  have hs (y : Fin s) :
      EncodedOracleUnitary.slice (opTensor 1 (pC s x - 1) ψ) y =
        (pC s x - 1) (EncodedOracleUnitary.slice ψ y) := by
    ext I
    exact EncodedOracleUnitary.opTensor_one_apply _ ψ y I
  calc
    _ = ∑ y, ‖(pC s x - 1) (EncodedOracleUnitary.slice ψ y)‖ ^ 2 := by
      rw [← EncodedOracleUnitary.sum_slice_norm_sq]
      exact Finset.sum_congr rfl (fun y _ => congrArg (fun v => ‖v‖ ^ 2) (hs y))
    _ ≤ ∑ y, (2 / ((s - r + 1 : ℕ) : ℝ)) *
        ‖EncodedOracleUnitary.slice ψ y‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      exact pC_retained_slice_bound x y r hr _ (hψ y)
    _ = _ := by rw [← Finset.mul_sum, EncodedOracleUnitary.sum_slice_norm_sq]

theorem pC_retained_norm_bound (x : Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (Fin s × InjDb s))
    (hψ : ∀ y I, ψ (y, I) ≠ 0 → I x = some y ∧ I.size ≤ r) :
    ‖opTensor (1 : Hil (Fin s) →L[ℂ] Hil (Fin s)) (pC s x - 1) ψ‖ ≤
      Real.sqrt (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact pC_retained_bound x r hr ψ hψ

theorem pC_retained_control_bound {C : Type*} [Fintype C] [DecidableEq C]
    (x y : C → Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (C × InjDb s))
    (hψ : ∀ c I, ψ (c, I) ≠ 0 → I (x c) = some (y c) ∧ I.size ≤ r) :
    ‖controlled (fun c => pC s (x c) - 1) ψ‖ ^ 2 ≤
      (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ ^ 2 := by
  have hs (c : C) :
      EncodedOracleUnitary.slice (controlled (fun c => pC s (x c) - 1) ψ) c =
        (pC s (x c) - 1) (EncodedOracleUnitary.slice ψ c) := by
    ext I
    exact ControlledOperators.controlled_apply _ ψ c I
  calc
    _ = ∑ c, ‖(pC s (x c) - 1) (EncodedOracleUnitary.slice ψ c)‖ ^ 2 := by
      rw [← EncodedOracleUnitary.sum_slice_norm_sq]
      exact Finset.sum_congr rfl (fun c _ => congrArg (fun v => ‖v‖ ^ 2) (hs c))
    _ ≤ ∑ c, (2 / ((s - r + 1 : ℕ) : ℝ)) *
        ‖EncodedOracleUnitary.slice ψ c‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      exact pC_retained_slice_bound (x c) (y c) r hr _ (hψ c)
    _ = _ := by rw [← Finset.mul_sum, EncodedOracleUnitary.sum_slice_norm_sq]

theorem pC_retained_control_norm_bound {C : Type*} [Fintype C] [DecidableEq C]
    (x y : C → Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (C × InjDb s))
    (hψ : ∀ c I, ψ (c, I) ≠ 0 → I (x c) = some (y c) ∧ I.size ≤ r) :
    ‖controlled (fun c => pC s (x c) - 1) ψ‖ ≤
      Real.sqrt (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact pC_retained_control_bound x y r hr ψ hψ

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathCompletionRange
section

namespace WeldedPath.CompletionLevels

open Classical InjDb HilbertSupport IntertwinerPartial CompressedPrimitive
open scoped BigOperators

variable {s : ℕ}

theorem Gam_range_eq (s r : ℕ) : (Gam s r).range = Hlevel s r := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    exact Gam_range s r u
  · intro v hv
    have hp (w : Hil (Equiv.Perm (Fin s))) (hw : w ∈ Hle s r) :
        projLevel s r w ∈ (Gam s r).range := by
      change w ∈ Submodule.span ℂ {v | ∃ I : InjDb s, I.size = r ∧ v = completion I} at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨I, hI, rfl⟩ := hw
        refine ⟨ket I, ?_⟩
        change Gam s r (ket I) = projLevel s r (completion I)
        rw [Gam_ket, if_pos hI]
      | zero => simp
      | add u w hu hw ihu ihw =>
        rw [map_add]
        exact (Gam s r).range.add_mem ihu ihw
      | smul c w hw ihw =>
        rw [map_smul]
        exact (Gam s r).range.smul_mem c ihw
    have he : projLevel s r v = v := (Hlevel s r).starProjection_eq_self_iff.mpr hv
    simpa only [he] using hp v (Hlevel_le r hv)

theorem Gram_range_eq (s r : ℕ) : (Gram s r).range = Hlevel s r := by
  have he := (Gam s r).toLinearMap.range_self_comp_adjoint
  rw [ContinuousLinearMap.adjoint_toLinearMap] at he
  change (Gram s r).range = (Gam s r).range at he
  exact he.trans (Gam_range_eq s r)

theorem permutation_eq_of_except (φ ψ : Equiv.Perm (Fin s)) (x : Fin s)
    (h : ∀ u, u ≠ x → ψ u = φ u) : ψ = φ := by
  apply Equiv.ext
  intro u
  by_cases hu : u = x
  · subst u
    by_cases hv : φ.symm (ψ x) = x
    · have he := congrArg φ hv
      simpa only [Equiv.apply_symm_apply] using he
    · have he := h (φ.symm (ψ x)) hv
      rw [Equiv.apply_symm_apply] at he
      exact (hv (ψ.injective he)).elim
  · exact h u hu

theorem erased_permutation_extends_iff (φ ψ : Equiv.Perm (Fin s)) (x : Fin s) :
    Extends ψ (eraseAt φ.toPEquiv x) ↔ ψ = φ := by
  constructor
  · intro h
    apply permutation_eq_of_except φ ψ x
    intro u hu
    apply h u (φ u)
    rw [eraseAt_apply, if_neg hu]
    rfl
  · rintro rfl u y h
    rw [eraseAt_apply] at h
    by_cases hu : u = x
    · rw [if_pos hu] at h
      cases h
    · rw [if_neg hu] at h
      exact Option.some.inj h

theorem erased_permutation_rawCompletion (φ : Equiv.Perm (Fin s)) (x : Fin s) :
    rawCompletion (eraseAt φ.toPEquiv x) = ket φ := by
  ext ψ
  simp only [rawCompletion_apply, erased_permutation_extends_iff, ket_apply]

theorem Hle_pred_eq_top (hs : 0 < s) : Hle s (s - 1) = ⊤ := by
  apply eq_top_iff.mpr
  intro v _
  rw [← sum_basis v]
  apply Submodule.sum_mem
  intro φ _
  apply Submodule.smul_mem
  let x : Fin s := ⟨0, hs⟩
  rw [← erased_permutation_rawCompletion φ x]
  apply (completion_mem_iff _ _).mp
  apply Submodule.subset_span
  refine ⟨eraseAt φ.toPEquiv x, ?_, rfl⟩
  have he := eraseAt_size φ.toPEquiv x (φ x) rfl
  have hsize : InjDb.size φ.toPEquiv = s := by simp [InjDb.size]
  omega

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathFrameLevelSpectrum
section

namespace WeldedPath.CompletionFrame

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open CompletionLevels HilbertSupport YoungBranching
open scoped BigOperators MonoidAlgebra

variable {s : ℕ}

lemma frame_eq_fourier (s r : ℕ) :
    (frame s r).toLinearMap = complexFourier (regularRep (Equiv.Perm (Fin s)))
      (centralKernel s r) := by
  apply LinearMap.ext
  intro v
  change frame s r v = complexFourier _ _ v
  rw [frame_eq_sum_translate]
  simp only [complexFourier, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

lemma frame_range_le (s r : ℕ) : (frame s r).range ≤ Hle s r := by
  rintro v ⟨w,rfl⟩
  change frame s r w ∈ Hle s r
  unfold frame
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  apply Submodule.sum_mem
  intro I hI
  exact (Hle s r).smul_mem _ (Submodule.subset_span ⟨I, (Finset.mem_filter.mp hI).2, rfl⟩)

lemma frame_zero_of_orthogonal (r : ℕ) (v : Hil (Equiv.Perm (Fin s)))
    (hv : v ∈ (Hle s r)ᗮ) : frame s r v = 0 := by
  apply ext_inner_left ℂ
  intro w
  rw [inner_zero_right, ← frame_symmetric]
  exact ((Hle s r).mem_orthogonal v).mp hv _ (frame_range_le s r ⟨w,rfl⟩)

lemma frame_ne_zero_on_level (r : ℕ) (v : Hil (Equiv.Perm (Fin s)))
    (hv : v ∈ Hlevel s r) (hne : v ≠ 0) : frame s r v ≠ 0 := by
  intro hz
  have hg : Gram s r v = 0 := by
    rw [Gram_eq_frame_projLevel]
    change frame s r ((Hlevel s r).starProjection v) = 0
    rw [(Hlevel s r).starProjection_eq_self_iff.mpr hv, hz]
  have hsym : (Gram s r).toLinearMap.IsSymmetric := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (IntertwinerPartial.Gram_selfadjoint s r)
  have hk : v ∈ (Gram s r).rangeᗮ := by
    rw [hsym.orthogonal_range]
    exact hg
  rw [Gram_range_eq] at hk
  exact hne (inner_self_eq_zero.mp (((Hlevel s r).mem_orthogonal v).mp hk v hv))

section Abstract
variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W]

lemma fourier_equiv (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (e : Representation.Equiv ρ τ) (a : G → ℂ) (v : V) :
    e (complexFourier ρ a v) = complexFourier τ a (e v) := by
  simp only [complexFourier, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact LinearMap.congr_fun (e.isIntertwining' g) v

def centralEigenspace (ρ : Representation ℂ G V) (a : G → ℂ)
    (ha : ∀ g h, a (g*h) = a (h*g)) (c : ℂ) : Subrepresentation ρ where
  toSubmodule := Module.End.eigenspace (complexFourier ρ a) c
  apply_mem_toSubmodule g v hv := by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have he := LinearMap.congr_fun (centralFourier_commute ρ a ha g) v
    change complexFourier ρ a (ρ g v) = ρ g (complexFourier ρ a v) at he
    rw [he, hv, map_smul]

lemma exists_irreducible_below (ρ : Representation ℂ G V)
    (E : Subrepresentation ρ) (v : V) (hv : v ∈ E) (hne : v ≠ 0) :
    ∃ σ : Subrepresentation ρ, Representation.IsIrreducible σ.toRepresentation ∧ σ ≤ E := by
  have hbot : E.asSubmodule ≠ ⊥ := by
    intro he
    have hm : v ∈ E.asSubmodule := hv
    rw [he] at hm
    exact hne hm
  obtain ⟨S,hS,hSE⟩ := (eq_bot_or_exists_atom_le E.asSubmodule).resolve_left hbot
  refine ⟨Subrepresentation.ofSubmodule' S, ?_, hSE⟩
  apply (subrep_irreducible_iff ρ _).mpr
  exact (isSimpleModule_iff_isAtom).mpr hS

lemma fourier_scalar_of_below (ρ : Representation ℂ G V)
    (σ : Subrepresentation ρ) (a : G → ℂ) (c : ℂ)
    (h : ∀ v ∈ σ, complexFourier ρ a v = c • v) :
    complexFourier σ.toRepresentation a = c • (1 : Module.End ℂ σ.toSubmodule) := by
  ext v
  rw [complexFourier_subrep]
  exact h v v.property

end Abstract

lemma exists_specht_equiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin s)) V)
    [Representation.IsIrreducible ρ] :
    ∃ μ : DiagramCounting.Shape s, Nonempty (Representation.Equiv (SpechtActual.rep μ) ρ) := by
  obtain ⟨c,⟨e⟩,_⟩ := irreducibleRep_complete ρ
  obtain ⟨μ,hμ⟩ := (SpechtActual.index_bijective s).surjective c
  obtain ⟨f⟩ := SpechtActual.index_spec μ
  subst c
  exact ⟨μ, ⟨f.symm.trans e⟩⟩

lemma scalar_transfer {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin s)) V)
    (τ : Representation ℂ (Equiv.Perm (Fin s)) W)
    (e : Representation.Equiv ρ τ) (a : Equiv.Perm (Fin s) → ℂ) (c : ℂ)
    (h : complexFourier τ a = c • (1 : Module.End ℂ W)) :
    complexFourier ρ a = c • (1 : Module.End ℂ V) := by
  ext v
  apply e.injective
  change e (complexFourier ρ a v) = e ((c • (1 : Module.End ℂ V)) v)
  rw [fourier_equiv, h]
  simp

lemma joint_frame_eigenvalue_specht (r t : ℕ) (c d : ℂ)
    (v : Hil (Equiv.Perm (Fin s))) (hne : v ≠ 0)
    (hr : frame s r v = c • v) (ht : frame s t v = d • v) :
    ∃ μ : DiagramCounting.Shape s,
      complexFourier (SpechtActual.rep μ) (centralKernel s r) = c • 1 ∧
      complexFourier (SpechtActual.rep μ) (centralKernel s t) = d • 1 := by
  let ρ := regularRep (Equiv.Perm (Fin s))
  let E := centralEigenspace ρ (centralKernel s r) (centralKernel_comm r) c ⊓
    centralEigenspace ρ (centralKernel s t) (centralKernel_comm t) d
  have hv : v ∈ E := by
    constructor
    · change v ∈ Module.End.eigenspace (complexFourier ρ (centralKernel s r)) c
      rw [Module.End.mem_eigenspace_iff, ← frame_eq_fourier]
      exact hr
    · change v ∈ Module.End.eigenspace (complexFourier ρ (centralKernel s t)) d
      rw [Module.End.mem_eigenspace_iff, ← frame_eq_fourier]
      exact ht
  obtain ⟨σ,hσ,hσE⟩ := exists_irreducible_below ρ E v hv hne
  letI := hσ
  obtain ⟨μ,⟨e⟩⟩ := exists_specht_equiv σ.toRepresentation
  refine ⟨μ, ?_, ?_⟩
  · apply scalar_transfer (SpechtActual.rep μ) σ.toRepresentation e
    apply fourier_scalar_of_below
    intro w hw
    exact Module.End.mem_eigenspace_iff.mp (hσE hw).1
  · apply scalar_transfer (SpechtActual.rep μ) σ.toRepresentation e
    apply fourier_scalar_of_below
    intro w hw
    exact Module.End.mem_eigenspace_iff.mp (hσE hw).2

lemma specht_frame_scalar_ne_zero_iff (μ : DiagramCounting.Shape s)
    (r : ℕ) (hr : r ≤ s) (c : ℂ)
    (hc : complexFourier (SpechtActual.rep μ) (centralKernel s r) = c • 1) :
    c ≠ 0 ↔ s-r ≤ μ.1.rowLen 0 := by
  haveI : Nontrivial (spechtSub μ.1).toSubmodule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Equiv.Perm (Fin s)))
      (Representation.asModule (SpechtActual.rep μ))
  have hval := kernelRepresentation_scalar (SpechtActual.rep μ) r hr
  change complexFourier (SpechtActual.rep μ) (centralKernel s r) = _ at hval
  rw [hc] at hval
  have he := smul_left_injective ℂ (one_ne_zero : (1 : Module.End ℂ
    (spechtSub μ.1).toSubmodule) ≠ 0) hval
  rw [he]
  have hdim : (Module.finrank ℂ (spechtSub μ.1).toSubmodule : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
  have hchoose : (s.choose r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
  rw [div_ne_zero_iff, and_iff_left hdim, mul_ne_zero_iff, and_iff_right hchoose,
    Nat.cast_ne_zero]
  change Module.finrank ℂ (initialRep μ (Nat.sub_le s r)).invariants ≠ 0 ↔ _
  rw [← Nat.pos_iff_ne_zero]
  exact initial_invariants_pos_iff μ (Nat.sub_le s r)

theorem frame_level_eigenvalue_shape (r : ℕ) (hr : r ≤ s) (c : ℂ)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hlevel s r) (hne : v ≠ 0)
    (he : frame s r v = c • v) :
    ∃ μ : DiagramCounting.Shape s, μ.1.rowLen 0 = s-r ∧
      complexFourier (SpechtActual.rep μ) (centralKernel s r) = c • 1 := by
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at he
    exact frame_ne_zero_on_level r v hv hne he
  cases r with
  | zero =>
    obtain ⟨μ,hμ,_⟩ := joint_frame_eigenvalue_specht 0 0 c c v hne he he
    have hlo := (specht_frame_scalar_ne_zero_iff μ 0 hr c hμ).mp hc
    have hhi : μ.1.rowLen 0 ≤ s := by
      simpa only [μ.2] using DiagramCounting.rowLen_le_card μ.1 0
    exact ⟨μ, by omega, hμ⟩
  | succ r =>
    have hp : frame s r v = (0 : ℂ) • v := by
      rw [zero_smul]
      exact frame_zero_of_orthogonal r v hv.2
    obtain ⟨μ,hμ,hpμ⟩ := joint_frame_eigenvalue_specht (r+1) r c 0 v hne he hp
    have hlo := (specht_frame_scalar_ne_zero_iff μ (r+1) hr c hμ).mp hc
    have hhi : ¬ s-r ≤ μ.1.rowLen 0 := by
      intro h
      exact (specht_frame_scalar_ne_zero_iff μ r (by omega) 0 hpμ).mpr h rfl
    exact ⟨μ, by omega, hμ⟩

end
end WeldedPath.CompletionFrame

end

-- Solutions.WeldedPathPolarSupport
section

namespace WeldedPath.OperatorPolar

open Classical

set_option maxHeartbeats 1000000

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def endAlgEquiv :
    (Hil X →L[ℂ] Hil X) ≃ₐ[ℂ] Module.End ℂ (Hil X) :=
  (AlgEquiv.ofLinearEquiv
    (LinearMap.toContinuousLinearMap : Module.End ℂ (Hil X) ≃ₗ[ℂ] (Hil X →L[ℂ] Hil X))
    rfl (fun _ _ => rfl)).symm

theorem finite_complex_spectrum (A : Hil X →L[ℂ] Hil X) : (spectrum ℂ A).Finite := by
  rw [← AlgEquiv.spectrum_eq endAlgEquiv A]
  exact Module.End.finite_spectrum _

theorem finite_real_spectrum (A : Hil X →L[ℂ] Hil X) : (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (finite_complex_spectrum A).preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

theorem gram_invSqrt_sandwich (A : Hil X →L[ℂ] Hil X) (hA : A.IsPositive) :
    A * invSqrt A * invSqrt A * A = A := by
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  have hf : ContinuousOn f (spectrum ℝ A) := (finite_real_spectrum A).continuousOn f
  have hnonneg : 0 ≤ A := by simpa only [ContinuousLinearMap.le_def, sub_zero] using hA
  have hi : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA.isSelfAdjoint
  have he₁ := cfc_mul (fun x : ℝ => x) f A continuousOn_id hf
  have he₂ := cfc_mul (fun x => x * f x) f A (continuousOn_id.mul hf) hf
  have he₃ := cfc_mul (fun x => x * f x * f x) (fun x : ℝ => x) A
    ((continuousOn_id.mul hf).mul hf) continuousOn_id
  calc
    _ = cfc (fun x => x * f x * f x * x) A := by
      rw [he₃, he₂, he₁, hi]
      rfl
    _ = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x hx
      have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hnonneg hx
      by_cases hz : x = 0
      · simp [hz, f]
      · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hx₀ (Ne.symm hz)))
        dsimp [f]
        field_simp [hs]
        nlinarith [Real.sq_sqrt hx₀]
    _ = A := hi

theorem rectangular_gram_identity (T : Hil X →L[ℂ] Hil Y) (B : Hil Y →L[ℂ] Hil Y)
    (hB : ContinuousLinearMap.adjoint B = B)
    (hc : B.comp (T.comp (ContinuousLinearMap.adjoint T)) =
      (T.comp (ContinuousLinearMap.adjoint T)).comp B)
    (hs : ((((T.comp (ContinuousLinearMap.adjoint T)).comp B).comp B).comp
      (T.comp (ContinuousLinearMap.adjoint T))) = T.comp (ContinuousLinearMap.adjoint T)) :
    ((ContinuousLinearMap.adjoint ((ContinuousLinearMap.adjoint T).comp B)).comp
      ((ContinuousLinearMap.adjoint T).comp B)).comp
      (T.comp (ContinuousLinearMap.adjoint T)) = T.comp (ContinuousLinearMap.adjoint T) := by
  rw [ContinuousLinearMap.adjoint_comp, hB, ContinuousLinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun Q : Hil Y →L[ℂ] Hil Y => Q v) hs
  have hcv := congrArg (fun Q : Hil Y →L[ℂ] Hil Y =>
    Q (B (T (ContinuousLinearMap.adjoint T v)))) hc
  exact hcv.trans hv

theorem polar_gram_fixed (T : Hil X →L[ℂ] Hil Y) :
    ((ContinuousLinearMap.adjoint (polarMap T)).comp (polarMap T)).comp
      (T.comp (ContinuousLinearMap.adjoint T)) = T.comp (ContinuousLinearMap.adjoint T) :=
  rectangular_gram_identity T _ (invSqrt_adjoint _)
    (invSqrt_commute _ (gram_selfadjoint T)).eq
    (gram_invSqrt_sandwich _ T.isPositive_self_comp_adjoint)

end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathPolarProjection
section

namespace WeldedPath.OperatorPolar

open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem polar_initial_projection (T : Hil X →L[ℂ] Hil Y) :
    (ContinuousLinearMap.adjoint (polarMap T)).comp (polarMap T) = T.range.starProjection := by
  let A := T.comp (ContinuousLinearMap.adjoint T)
  let P := (ContinuousLinearMap.adjoint (polarMap T)).comp (polarMap T)
  have hR : A.range = T.range := by
    have he := T.toLinearMap.range_self_comp_adjoint
    rw [ContinuousLinearMap.adjoint_toLinearMap] at he
    exact he
  have hpadj : ContinuousLinearMap.adjoint P = P := by
    simp only [P, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hfix (v : Hil Y) (hv : v ∈ T.range) : P v = v := by
    rw [← hR] at hv
    obtain ⟨u, rfl⟩ := hv
    exact congrArg (fun Q : Hil Y →L[ℂ] Hil Y => Q u) (polar_gram_fixed T)
  have hmem (v : Hil Y) : P v ∈ T.range := by
    simp only [P, polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]
    apply invSqrt_mapsTo A (gram_selfadjoint T) T.range
    intro w
    exact ⟨ContinuousLinearMap.adjoint T w, rfl⟩
  apply ContinuousLinearMap.ext
  intro v
  symm
  apply T.range.eq_starProjection_of_mem_of_inner_eq_zero (hmem v)
  intro w hw
  rw [inner_sub_left]
  have he := ContinuousLinearMap.adjoint_inner_left P w v
  rw [hpadj, hfix w hw] at he
  exact sub_eq_zero.mpr he.symm

end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathGramConditioning
section

namespace WeldedPath.CompletionFrame

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open CompletionLevels IntertwinerPartial OperatorPolar
open scoped BigOperators

variable {s : ℕ}

theorem frame_level_eigenvalue_bounds (r : ℕ) (hsmall : 4*r ≤ s) (c : ℂ)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hlevel s r) (hne : v ≠ 0)
    (he : frame s r v = c • v) :
    ∃ d : ℝ, 1 ≤ d ∧ d ≤ 2 ∧ c = (d : ℂ) := by
  obtain ⟨μ,hrow,hμ⟩ := frame_level_eigenvalue_shape r (by omega) c v hv hne he
  obtain ⟨d,hd₁,hd₂,hd⟩ := centralKernel_specht_conditioned μ r hsmall hrow
  haveI : Nontrivial (spechtSub μ.1).toSubmodule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Equiv.Perm (Fin s)))
      (Representation.asModule (SpechtActual.rep μ))
  refine ⟨d,hd₁,hd₂,?_⟩
  apply smul_left_injective ℂ (one_ne_zero : (1 : Module.End ℂ
    (spechtSub μ.1).toSubmodule) ≠ 0)
  exact hμ.symm.trans hd

theorem Gram_spectrum_bounds (s r : ℕ) (hsmall : 4*r ≤ s)
    (x : ℝ) (hx : x ∈ spectrum ℝ (Gram s r)) : x = 0 ∨ (1 ≤ x ∧ x ≤ 2) := by
  by_cases hx₀ : x = 0
  · exact Or.inl hx₀
  right
  have hxc : (x : ℂ) ∈ spectrum ℂ (Gram s r) := by
    rwa [← spectrum.preimage_algebraMap ℂ] at hx
  have hxe : (x : ℂ) ∈ spectrum ℂ (Gram s r).toLinearMap := by
    rwa [← AlgEquiv.spectrum_eq endAlgEquiv (Gram s r)] at hxc
  obtain ⟨v,hv,hne⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hxe).exists_hasEigenvector
  have he : Gram s r v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.mp hv
  have hxc₀ : (x : ℂ) ≠ 0 := by exact_mod_cast hx₀
  have hrange : v ∈ (Gram s r).range := by
    refine ⟨(x : ℂ)⁻¹ • v, ?_⟩
    change Gram s r ((x : ℂ)⁻¹ • v) = v
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hxc₀, one_smul]
  have hvlevel : v ∈ Hlevel s r := by rwa [← Gram_range_eq]
  have hframe : frame s r v = (x : ℂ) • v := by
    rw [Gram_eq_frame_projLevel] at he
    change frame s r ((Hlevel s r).starProjection v) = _ at he
    rwa [(Hlevel s r).starProjection_eq_self_iff.mpr hvlevel] at he
  obtain ⟨d,hd₁,hd₂,hd⟩ := frame_level_eigenvalue_bounds r hsmall x v hvlevel hne hframe
  have hxd : x = d := Complex.ofReal_injective hd
  simpa only [hxd] using And.intro hd₁ hd₂

theorem Gram_norm_le_two (s r : ℕ) (hsmall : 4*r ≤ s) : ‖Gram s r‖ ≤ 2 := by
  nth_rw 1 [← cfc_id' ℝ (Gram s r) (Gram_selfadjoint s r)]
  apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 2)
  intro x hx
  rcases Gram_spectrum_bounds s r hsmall x hx with rfl | ⟨hlo,hhi⟩
  · norm_num
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)] using hhi

theorem GramInvSqrt_norm_le_one (s r : ℕ) (hsmall : 4*r ≤ s) :
    ‖GramInvSqrt s r‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 1)
  intro x hx
  rcases Gram_spectrum_bounds s r hsmall x hx with rfl | ⟨hlo,_⟩
  · norm_num
  · have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hlo
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg x))]
    exact inv_le_one_of_one_le₀ hs

lemma support_scalar (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = if x = 0 then 0 else 1 := by
  by_cases hx₀ : x = 0
  · simp [hx₀]
  · have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hx (Ne.symm hx₀))).ne'
    rw [if_neg hx₀]
    calc
      _ = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ := by
        rw [Real.mul_self_sqrt hx]
      _ = 1 := by field_simp

theorem projLevel_eq_cfc_support (s r : ℕ) :
    projLevel s r = cfc (fun x : ℝ => if x = 0 then 0 else 1) (Gram s r) := by
  have hp := polar_initial_projection (Gam s r)
  have hp := hp.trans (congrArg (fun K : Submodule ℂ (Hil (Equiv.Perm (Fin s))) =>
    K.starProjection) (Gam_range_eq s r))
  have hp' : GramInvSqrt s r * Gram s r * GramInvSqrt s r = projLevel s r := by
    change ((invSqrt ((Gam s r).comp (ContinuousLinearMap.adjoint (Gam s r)))).comp
      ((Gam s r).comp (ContinuousLinearMap.adjoint (Gam s r)))).comp
      (invSqrt ((Gam s r).comp (ContinuousLinearMap.adjoint (Gam s r)))) = _
    simpa only [projLevel, polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc] using hp
  rw [← hp']
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  have hf : ContinuousOn f (spectrum ℝ (Gram s r)) := (finite_real_spectrum _).continuousOn f
  have he : Gram s r = cfc (fun x : ℝ => x) (Gram s r) :=
    (cfc_id' ℝ _ (Gram_selfadjoint s r)).symm
  change cfc f (Gram s r) * Gram s r * cfc f (Gram s r) = _
  nth_rw 2 [he]
  rw [← cfc_mul f (fun x : ℝ => x) (Gram s r) hf continuousOn_id,
    ← cfc_mul (fun x => f x * x) f (Gram s r) (hf.mul continuousOn_id) hf]
  apply cfc_congr
  intro x hx
  apply support_scalar
  have hpos : 0 ≤ Gram s r := by
    simpa only [ContinuousLinearMap.le_def, sub_zero, Gram] using
      (Gam s r).isPositive_self_comp_adjoint
  exact spectrum_nonneg_of_nonneg hpos hx

theorem projLevel_le_Gram (s r : ℕ) (hsmall : 4*r ≤ s) :
    projLevel s r ≤ Gram s r := by
  calc
    projLevel s r = cfc (fun x : ℝ => if x = 0 then 0 else 1) (Gram s r) :=
      projLevel_eq_cfc_support s r
    _ ≤ cfc (fun x : ℝ => x) (Gram s r) := by
      apply cfc_mono (a := Gram s r) _ ((finite_real_spectrum (Gram s r)).continuousOn _) continuousOn_id
      intro x hx
      rcases Gram_spectrum_bounds s r hsmall x hx with rfl | ⟨hlo,_⟩
      · simp
      · rw [if_neg (by linarith : x ≠ 0)]
        exact hlo
    _ = Gram s r := cfc_id' ℝ _ (Gram_selfadjoint s r)

theorem Gram_le_two_projLevel (s r : ℕ) (hsmall : 4*r ≤ s) :
    Gram s r ≤ (2 : ℝ) • projLevel s r := by
  calc
    Gram s r = cfc (fun x : ℝ => x) (Gram s r) :=
      (cfc_id' ℝ _ (Gram_selfadjoint s r)).symm
    _ ≤ cfc (fun x : ℝ => 2 * (if x = 0 then 0 else 1)) (Gram s r) := by
      apply cfc_mono (a := Gram s r) _ continuousOn_id ((finite_real_spectrum (Gram s r)).continuousOn _)
      intro x hx
      rcases Gram_spectrum_bounds s r hsmall x hx with rfl | ⟨hlo,hhi⟩
      · simp
      · simpa only [id_eq, if_neg (by linarith : x ≠ 0), mul_one] using hhi
    _ = (2 : ℝ) • projLevel s r := by
      rw [cfc_const_mul 2 _ (Gram s r) ((finite_real_spectrum (Gram s r)).continuousOn _),
        ← projLevel_eq_cfc_support]

end
end WeldedPath.CompletionFrame

end

open Classical WeldedPath

theorem solution (s r : ℕ) (hsmall : 4*r ≤ s) :
    projLevel s r ≤ Gram s r ∧
    Gram s r ≤ (2 : ℝ) • projLevel s r ∧
    ‖Gram s r‖ ≤ 2 ∧ ‖GramInvSqrt s r‖ ≤ 1 := by
  exact ⟨CompletionFrame.projLevel_le_Gram s r hsmall,
    CompletionFrame.Gram_le_two_projLevel s r hsmall,
    CompletionFrame.Gram_norm_le_two s r hsmall,
    CompletionFrame.GramInvSqrt_norm_le_one s r hsmall⟩
