-- Prove2me | solution 1 for WeldedPath.incidence_gap
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-18T16:49:13.495793+00:00
-- url     : https://prove2.me/submissions/1349fa0c-c800-4799-8a3c-3b205db3d543

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection
import Mathlib
import Mathlib.RepresentationTheory.Character
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtModules
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.GroupTheory.Perm.ViaEmbedding
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
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_WeldedPath_exactCpO
import Definitions.Def_WeldedPath_cpO
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_WeldedPath_InjDb
import Definitions.Def_WeldedPath_Supplement_exactCpWT
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Trace
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option autoImplicit false

-- Solutions.DiagonalAnticommutator
section

namespace DiagonalAnticommutator

noncomputable section
open Classical
open scoped BigOperators

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]
  {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module 𝕜 (W i)]

def inclusion (E : V ≃ₗ[𝕜] ((i : ι) → W i)) (i : ι) (w : W i) : V :=
  E.symm (Pi.single i w)

lemma sum_inclusion (E : V ≃ₗ[𝕜] ((i : ι) → W i)) (v : V) :
    (∑ i, inclusion E i (E v i))=v := by
  apply E.injective
  simp only [map_sum,inclusion,LinearEquiv.apply_symm_apply]
  ext i
  simp

lemma eigen_inclusion (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i) (i : ι) (w : W i) :
    B (inclusion E i w)=b i • inclusion E i w := by
  apply E.injective
  ext k
  rw [hB,map_smul]
  simp only [inclusion,LinearEquiv.apply_symm_apply,Pi.smul_apply]
  by_cases hki : k=i
  · subst k
    simp
  · simp [Pi.single_eq_of_ne hki]

theorem eigenvalue_eq_sum (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i)
    (T : Module.End 𝕜 V) (hT : T≠0) (c : 𝕜)
    (he : B*T+T*B=c•T) : ∃ i k, c=b i+b k := by
  obtain ⟨v,hv⟩ : ∃ v, T v≠0 := by
    by_contra! hn
    exact hT (LinearMap.ext hn)
  obtain ⟨i,hi⟩ : ∃ i, E (T v) i≠0 := by
    by_contra! hn
    have hz : E (T v)=0 := funext hn
    exact hv (E.injective (by simpa only [map_zero] using hz))
  have hs : E (T v) i=∑ k, E (T (inclusion E k (E v k))) i := by
    conv_lhs => rw [← sum_inclusion E v]
    simp only [map_sum,Finset.sum_apply]
  obtain ⟨k,hk⟩ : ∃ k, E (T (inclusion E k (E v k))) i≠0 := by
    by_contra! hn
    exact hi (by rw [hs]; exact Finset.sum_eq_zero (fun k _ => hn k))
  let w := inclusion E k (E v k)
  have hew := congrArg (fun A : Module.End 𝕜 V => E (A w) i) he
  simp only [LinearMap.add_apply,Module.End.mul_apply,LinearMap.smul_apply,map_add,
    map_smul,Pi.add_apply,Pi.smul_apply,hB] at hew
  rw [show B w=b k • w from eigen_inclusion E B b hB k (E v k),map_smul,map_smul] at hew
  change b i • E (T w) i + b k • E (T w) i = c • E (T w) i at hew
  have hsc : (b i+b k-c) • E (T w) i=0 := by
    rw [sub_smul,add_smul,hew,sub_self]
  have hc : b i+b k-c=0 := (smul_eq_zero.mp hsc).resolve_right hk
  exact ⟨i,k,(sub_eq_zero.mp hc).symm⟩

theorem real_eigenvalue_gap {ι : Type*} [Fintype ι]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (E : V ≃ₗ[ℂ] ((i : ι) → W i)) (B : Module.End ℂ V) (b : ι → ℝ)
    (hB : ∀ v i, E (B v) i=(b i : ℂ) • E v i)
    (δ : ℝ) (hb : ∀ i, 0≤b i ∧ (b i=0 ∨ δ≤b i))
    (T : Module.End ℂ V) (hT : T≠0) (c : ℝ)
    (he : B*T+T*B=(c : ℂ)•T) :
    0≤c ∧ (c=0 ∨ δ≤c) := by
  obtain ⟨i,k,hc⟩ := eigenvalue_eq_sum E B (fun i => (b i : ℂ)) hB T hT (c : ℂ) he
  have hcr : c=b i+b k := by
    simpa only [Complex.add_re,Complex.ofReal_re] using congrArg Complex.re hc
  obtain ⟨hi,hi'⟩ := hb i
  obtain ⟨hk,hk'⟩ := hb k
  constructor
  · linarith
  · rcases hi' with hi' | hi'
    · rcases hk' with hk' | hk'
      · left; linarith
      · right; linarith
    · right; linarith

end
end DiagonalAnticommutator


end

-- Solutions.WeldedPathRootComparisonAdapters
section

namespace DiagonalBlockSpace

noncomputable section
open Classical
open scoped BigOperators

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*}
  {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module 𝕜 (W i)]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

def supported (P : ι → Prop) : Submodule 𝕜 ((i : ι) → W i) where
  carrier := {v | ∀ i, ¬P i → v i=0}
  zero_mem' := by intro i hi; rfl
  add_mem' := by intro v w hv hw i hi; change v i+w i=0; rw [hv i hi,hw i hi,add_zero]
  smul_mem' := by intro c v hv i hi; change c • v i=0; rw [hv i hi,smul_zero]

def restrictEquiv (P : ι → Prop) : supported (𝕜:=𝕜) (W:=W) P ≃ₗ[𝕜] ((i : {i // P i}) → W i.1) where
  toFun v i := v.1 i.1
  invFun v := ⟨fun i => if h:P i then v ⟨i,h⟩ else 0,by intro i hi; simp [hi]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases hi : P i
    · simp [hi]
    · simp [hi,v.2 i hi]
  right_inv v := by funext i; simp [i.2]
  map_add' v w := rfl
  map_smul' c v := rfl

def transportEquiv (E : V ≃ₗ[𝕜] ((i : ι) → W i)) (M : Submodule 𝕜 V)
    (P : ι → Prop) (hM : ∀ v, v∈M ↔ E v∈supported (𝕜:=𝕜) (W:=W) P) :
    M ≃ₗ[𝕜] supported (𝕜:=𝕜) (W:=W) P where
  toFun v := ⟨E v.1,(hM v.1).mp v.2⟩
  invFun v := ⟨E.symm v.1,(hM (E.symm v.1)).mpr (by simpa only [LinearEquiv.apply_symm_apply] using v.2)⟩
  left_inv v := by apply Subtype.ext; exact E.symm_apply_apply v.1
  right_inv v := by apply Subtype.ext; exact E.apply_symm_apply v.1
  map_add' v w := by apply Subtype.ext; exact E.map_add v.1 w.1
  map_smul' c v := by apply Subtype.ext; exact E.map_smul c v.1

def blocksEquiv (E : V ≃ₗ[𝕜] ((i : ι) → W i)) (M : Submodule 𝕜 V)
    (P : ι → Prop) (hM : ∀ v, v∈M ↔ E v∈supported (𝕜:=𝕜) (W:=W) P) :
    M ≃ₗ[𝕜] ((i : {i // P i}) → W i.1) :=
  (transportEquiv E M P hM).trans (restrictEquiv P)

theorem finrank_blocks [Fintype ι] [∀ i, FiniteDimensional 𝕜 (W i)]
    (E : V ≃ₗ[𝕜] ((i : ι) → W i)) (M : Submodule 𝕜 V)
    (P : ι → Prop) (hM : ∀ v, v∈M ↔ E v∈supported (𝕜:=𝕜) (W:=W) P) :
    Module.finrank 𝕜 M=∑ i ∈ Finset.univ.filter P, Module.finrank 𝕜 (W i) := by
  rw [(blocksEquiv E M P hM).finrank_eq,Module.finrank_pi_fintype]
  exact (Finset.sum_subtype (Finset.univ.filter P) (p:=P) (by simp)
    (fun i => Module.finrank 𝕜 (W i))).symm

theorem mem_kernel_iff (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i) (v : V) :
    v∈B.ker ↔ E v∈supported (𝕜:=𝕜) (W:=W) (fun i => b i=0) := by
  constructor
  · intro hv i hi
    have he : E (B v) i=0 := by rw [show B v=0 from hv,map_zero]; rfl
    rw [hB] at he
    exact (smul_eq_zero.mp he).resolve_left hi
  · intro hv
    apply E.injective
    ext i
    rw [hB,map_zero]
    by_cases hi : b i=0
    · simp [hi]
    · simp [hv i hi]

def kernelEquiv (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i) :
    B.ker ≃ₗ[𝕜] ((i : {i // b i=0}) → W i.1) :=
  blocksEquiv E B.ker (fun i => b i=0) (mem_kernel_iff E B b hB)

theorem mem_range_iff (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i) (v : V) :
    v∈B.range ↔ E v∈supported (𝕜:=𝕜) (W:=W) (fun i => b i≠0) := by
  constructor
  · rintro ⟨w,rfl⟩ i hi
    have hi' : b i=0 := not_not.mp hi
    rw [hB,hi',zero_smul]
  · intro hv
    let w := E.symm (fun i => (b i)⁻¹ • E v i)
    refine ⟨w,?_⟩
    apply E.injective
    ext i
    rw [hB]
    change b i • E (E.symm (fun i => (b i)⁻¹ • E v i)) i=E v i
    rw [LinearEquiv.apply_symm_apply,smul_smul]
    by_cases hi : b i=0
    · rw [hv i (not_not.mpr hi),smul_zero]
    · rw [mul_inv_cancel₀ hi,one_smul]

end
end DiagonalBlockSpace


end

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


theorem initial_invariants_pos_iff {m n : ℕ} (μ : DiagramCounting.Shape n) (h : m ≤ n) :
    0 < Module.finrank ℂ (initialRep μ h).invariants ↔ m ≤ μ.1.rowLen 0 := by
  rw [← initialFixed_eq_invariants]
  exact initial_fixed_pos_iff μ h

end
end WeldedPath.YoungBranching
end


end

-- Solutions.YoungPieriCombinatoricsComplete
section

-- MODULE YoungHorizontalStrip
section

namespace WeldedPath.SpechtPieri

noncomputable section
open Classical YoungCounts

lemma horizontalStrip_colLen {ν μ : YoungDiagram} (h : ν ≤ μ) :
    HorizontalStrip ν μ ↔ ∀ j, μ.colLen j ≤ ν.colLen j+1 := by
  constructor
  · intro hs j
    by_contra hn
    have hj : ν.colLen j+1 < μ.colLen j := by omega
    have hx : (ν.colLen j,j) ∈ μ := μ.mem_iff_lt_colLen.mpr (by omega)
    have hy : (ν.colLen j+1,j) ∈ μ := μ.mem_iff_lt_colLen.mpr hj
    have hxn : (ν.colLen j,j) ∉ ν := by simp only [YoungDiagram.mem_iff_lt_colLen, lt_self_iff_false, not_false_eq_true]
    have hyn : (ν.colLen j+1,j) ∉ ν := by simp only [YoungDiagram.mem_iff_lt_colLen]; omega
    have he := hs.2 _ hx hxn _ hy hyn rfl
    have hf := congrArg Prod.fst he
    omega
  · intro hs
    refine ⟨h, ?_⟩
    intro x hx hxn y hy hyn hxy
    have hxu := μ.mem_iff_lt_colLen.mp hx
    have hyu := μ.mem_iff_lt_colLen.mp hy
    have hxl : ν.colLen x.2 ≤ x.1 := by
      exact Nat.le_of_not_gt (fun hh => hxn (ν.mem_iff_lt_colLen.mpr hh))
    have hyl : ν.colLen y.2 ≤ y.1 := by
      exact Nat.le_of_not_gt (fun hh => hyn (ν.mem_iff_lt_colLen.mpr hh))
    have hcap := hs x.2
    apply Prod.ext _ hxy
    rw [← hxy] at hyu hyl
    omega

lemma horizontalStrip_interlacing {ν μ : YoungDiagram} (h : ν ≤ μ) :
    HorizontalStrip ν μ ↔ ∀ i, μ.rowLen (i+1) ≤ ν.rowLen i := by
  constructor
  · intro hs i
    by_contra hn
    have hi : ν.rowLen i < μ.rowLen (i+1) := Nat.lt_of_not_ge hn
    have hx : (i,ν.rowLen i) ∈ μ := μ.mem_iff_lt_rowLen.mpr
      (hi.trans_le (μ.rowLen_anti i (i+1) (by omega)))
    have hy : (i+1,ν.rowLen i) ∈ μ := μ.mem_iff_lt_rowLen.mpr hi
    have hxn : (i,ν.rowLen i) ∉ ν := by simp only [YoungDiagram.mem_iff_lt_rowLen, lt_self_iff_false, not_false_eq_true]
    have hyn : (i+1,ν.rowLen i) ∉ ν := by
      simp only [YoungDiagram.mem_iff_lt_rowLen, not_lt]
      exact ν.rowLen_anti i (i+1) (by omega)
    have he := hs.2 _ hx hxn _ hy hyn rfl
    have hf := congrArg Prod.fst he
    omega
  · intro hs
    refine ⟨h, ?_⟩
    intro x hx hxn y hy hyn hxy
    apply Prod.ext _ hxy
    have hxu := μ.mem_iff_lt_rowLen.mp hx
    have hyu := μ.mem_iff_lt_rowLen.mp hy
    have hxl : ν.rowLen x.1 ≤ x.2 := by
      exact Nat.le_of_not_gt (fun hh => hxn (ν.mem_iff_lt_rowLen.mpr hh))
    have hyl : ν.rowLen y.1 ≤ y.2 := by
      exact Nat.le_of_not_gt (fun hh => hyn (ν.mem_iff_lt_rowLen.mpr hh))
    rcases lt_trichotomy x.1 y.1 with hr | hr | hr
    · have hm := μ.rowLen_anti (x.1+1) y.1 hr
      have hc := hs x.1
      omega
    · exact hr
    · have hm := μ.rowLen_anti (y.1+1) x.1 hr
      have hc := hs y.1
      omega

lemma horizontalStrip_inner {ν η μ : YoungDiagram} (h : HorizontalStrip ν μ)
    (hνη : ν ≤ η) (hημ : η ≤ μ) : HorizontalStrip η μ := by
  refine ⟨hημ, ?_⟩
  intro x hx hxn y hy hyn hxy
  exact h.2 _ hx (fun hxν => hxn (hνη hxν)) _ hy (fun hyν => hyn (hνη hyν)) hxy

lemma horizontalStrip_outer {ν η μ : YoungDiagram} (h : HorizontalStrip ν μ)
    (hνη : ν ≤ η) (hημ : η ≤ μ) : HorizontalStrip ν η := by
  refine ⟨hνη, ?_⟩
  intro x hx hxn y hy hyn hxy
  exact h.2 _ (hημ hx) hxn _ (hημ hy) hyn hxy

lemma horizontalStrip_addable_row {ν μ : YoungDiagram} (h : HorizontalStrip ν μ)
    (i : ℕ) (hi : ν.rowLen i < μ.rowLen i) :
    i=0 ∨ ν.rowLen i < ν.rowLen (i-1) := by
  by_cases hz : i=0
  · exact Or.inl hz
  · right
    have hb := (horizontalStrip_interlacing h.1).mp h (i-1)
    have he : i-1+1=i := by omega
    rw [he] at hb
    exact hi.trans_le hb

lemma horizontalStrip_removable_row {ν μ : YoungDiagram} (h : HorizontalStrip ν μ)
    (i : ℕ) (hi : ν.rowLen i < μ.rowLen i) :
    (i,μ.rowLen i-1) ∈ corners μ := by
  apply corner_iff.mpr
  have hb := (horizontalStrip_interlacing h.1).mp h i
  constructor <;> dsimp only <;> omega

lemma not_horizontalStrip_pair {ν μ : YoungDiagram} (h : ν ≤ μ)
    (hn : ¬ HorizontalStrip ν μ) :
    ∃ x y : Cell, x ∈ μ ∧ x ∉ ν ∧ y ∈ μ ∧ y ∉ ν ∧ x.2=y.2 ∧ x.1<y.1 := by
  have hf : ¬ ∀ x, x ∈ μ → x ∉ ν → ∀ y, y ∈ μ → y ∉ ν → x.2=y.2 → x=y :=
    fun hh => hn ⟨h,hh⟩
  push_neg at hf
  obtain ⟨x,hx,hxn,y,hy,hyn,hxy,hne⟩ := hf
  rcases lt_trichotomy x.1 y.1 with hr | hr | hr
  · exact ⟨x,y,hx,hxn,hy,hyn,hxy,hr⟩
  · exact (hne (Prod.ext hr hxy)).elim
  · exact ⟨y,x,hy,hyn,hx,hxn,hxy.symm,hr⟩

lemma predecessor_vertical_pair {ν ρ μ : YoungDiagram} (hc : Covers ρ μ)
    (hs : HorizontalStrip ν ρ) {x y : Cell}
    (hx : x ∈ μ) (hxn : x ∉ ν) (hy : y ∈ μ) (hyn : y ∉ ν)
    (hxy : x.2=y.2) (hrow : x.1<y.1) :
    x ∈ ρ ∧ y ∉ ρ ∧ ρ.cells=μ.cells.erase y := by
  obtain ⟨c,hcρ,hcμ⟩ := covers_insert hc
  have hxmin : x ≤ y := ⟨hrow.le,hxy.le⟩
  have hxρ : x ∈ ρ := by
    by_contra hxnρ
    have hxc : x=c := (Finset.mem_insert.mp (hcμ ▸ (show x ∈ μ.cells from hx))).resolve_right hxnρ
    rcases Finset.mem_insert.mp (hcμ ▸ (show y ∈ μ.cells from hy)) with hyc | hyρ
    · have he : x=y := hxc.trans hyc.symm
      have := congrArg Prod.fst he
      omega
    · exact hxnρ (ρ.isLowerSet hxmin hyρ)
  have hynρ : y ∉ ρ := by
    intro hyρ
    have he := hs.2 x hxρ hxn y hyρ hyn hxy
    have := congrArg Prod.fst he
    omega
  have hyc : y=c := (Finset.mem_insert.mp (hcμ ▸ (show y ∈ μ.cells from hy))).resolve_right hynρ
  refine ⟨hxρ,hynρ,?_⟩
  rw [hcμ,hyc,Finset.erase_insert hcρ]

lemma successor_vertical_pair {ν η μ : YoungDiagram} (hc : Covers ν η)
    (hs : HorizontalStrip η μ) {x y : Cell}
    (hx : x ∈ μ) (hxn : x ∉ ν) (hy : y ∈ μ) (hyn : y ∉ ν)
    (hxy : x.2=y.2) (hrow : x.1<y.1) :
    x ∈ η ∧ y ∉ η ∧ η.cells=insert x ν.cells := by
  obtain ⟨c,hcν,hcη⟩ := covers_insert hc
  have hxmin : x ≤ y := ⟨hrow.le,hxy.le⟩
  have hynη : y ∉ η := by
    intro hyη
    have hxη := η.isLowerSet hxmin hyη
    have hxc : x=c := (Finset.mem_insert.mp (hcη ▸ hxη)).resolve_right hxn
    have hyc : y=c := (Finset.mem_insert.mp (hcη ▸ hyη)).resolve_right hyn
    have he := congrArg Prod.fst (hxc.trans hyc.symm)
    omega
  have hxη : x ∈ η := by
    by_contra hxnη
    have he := hs.2 x hx hxnη y hy hynη hxy
    have := congrArg Prod.fst he
    omega
  have hxc : x=c := (Finset.mem_insert.mp (hcη ▸ hxη)).resolve_right hxn
  exact ⟨hxη,hynη,by simpa only [← hxc] using hcη⟩

theorem nonhorizontal_predecessor_unique {ν μ ρ σ : YoungDiagram}
    (hn : ¬ HorizontalStrip ν μ)
    (hρ : Covers ρ μ) (hsρ : HorizontalStrip ν ρ)
    (hσ : Covers σ μ) (hsσ : HorizontalStrip ν σ) : ρ=σ := by
  obtain ⟨x,y,hx,hxn,hy,hyn,hxy,hr⟩ := not_horizontalStrip_pair (hsρ.1.trans hρ.1) hn
  have heρ := (predecessor_vertical_pair hρ hsρ hx hxn hy hyn hxy hr).2.2
  have heσ := (predecessor_vertical_pair hσ hsσ hx hxn hy hyn hxy hr).2.2
  apply YoungDiagram.ext
  exact heρ.trans heσ.symm

theorem nonhorizontal_successor_unique {ν μ η θ : YoungDiagram}
    (hn : ¬ HorizontalStrip ν μ)
    (hη : Covers ν η) (hsη : HorizontalStrip η μ)
    (hθ : Covers ν θ) (hsθ : HorizontalStrip θ μ) : η=θ := by
  obtain ⟨x,y,hx,hxn,hy,hyn,hxy,hr⟩ := not_horizontalStrip_pair (hη.1.trans hsη.1) hn
  have heη := (successor_vertical_pair hη hsη hx hxn hy hyn hxy hr).2.2
  have heθ := (successor_vertical_pair hθ hsθ hx hxn hy hyn hxy hr).2.2
  apply YoungDiagram.ext
  exact heη.trans heθ.symm

theorem nonhorizontal_successor_exists {ν μ ρ : YoungDiagram}
    (hn : ¬ HorizontalStrip ν μ) (hc : Covers ρ μ) (hs : HorizontalStrip ν ρ) :
    ∃ η : YoungDiagram, Covers ν η ∧ HorizontalStrip η μ := by
  obtain ⟨x,y,hx,hxn,hy,hyn,hxy,hr⟩ := not_horizontalStrip_pair (hs.1.trans hc.1) hn
  obtain ⟨hxρ,hyρ,hρ⟩ := predecessor_vertical_pair hc hs hx hxn hy hyn hxy hr
  have hlow : IsLowerSet ((insert x ν.cells : Finset Cell) : Set Cell) := by
    intro z a haz hz
    rcases Finset.mem_insert.mp hz with hzx | hzν
    · subst z
      by_cases hax : a=x
      · exact Finset.mem_insert.mpr (Or.inl hax)
      · apply Finset.mem_insert_of_mem
        by_contra hanν
        have haρ : a ∈ ρ := ρ.isLowerSet haz hxρ
        have hcol : a.2≠x.2 := fun he => hax (hs.2 a haρ hanν x hxρ hxn he)
        let b : Cell := (y.1,a.2)
        have hbμ : b ∈ μ := μ.up_left_mem le_rfl (haz.2.trans hxy.le) hy
        have hby : b≠y := by intro he; have hh := congrArg Prod.snd he; exact hcol (hh.trans hxy.symm)
        have hbρ : b ∈ ρ := by
          change b ∈ ρ.cells
          rw [hρ]
          exact Finset.mem_erase.mpr ⟨hby,hbμ⟩
        have hab : a ≤ b := ⟨haz.1.trans hr.le,le_rfl⟩
        have hbnν : b ∉ ν := fun hbν => hanν (ν.isLowerSet hab hbν)
        have he := hs.2 a haρ hanν b hbρ hbnν rfl
        have he1 := congrArg Prod.fst he
        change a.1=y.1 at he1
        have := haz.1
        omega
    · exact Finset.mem_insert_of_mem (ν.isLowerSet haz hzν)
  let η : YoungDiagram := ⟨insert x ν.cells,hlow⟩
  have hcη : Covers ν η := by
    refine ⟨Finset.subset_insert _ _, ?_⟩
    change ν.cells.card+1=(insert x ν.cells).card
    rw [Finset.card_insert_of_notMem hxn]
  refine ⟨η,hcη,?_,?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzν
    · exact hx
    · exact hc.1 (hs.1 hzν)
  · intro a ha han b hb hbn hab
    have hanν : a ∉ ν := fun hh => han (Finset.mem_insert_of_mem hh)
    have hbnν : b ∉ ν := fun hh => hbn (Finset.mem_insert_of_mem hh)
    by_cases hay : a=y
    · subst a
      by_cases hby : b=y
      · exact hby.symm
      · have hbρ : b ∈ ρ := by rw [← YoungDiagram.mem_cells,hρ]; exact Finset.mem_erase.mpr ⟨hby,hb⟩
        have he := hs.2 x hxρ hxn b hbρ hbnν (hxy.trans hab)
        exact (hbn (Finset.mem_insert.mpr (Or.inl he.symm))).elim
    · by_cases hby : b=y
      · subst b
        have haρ : a ∈ ρ := by rw [← YoungDiagram.mem_cells,hρ]; exact Finset.mem_erase.mpr ⟨hay,ha⟩
        have he := hs.2 a haρ hanν x hxρ hxn (hab.trans hxy.symm)
        exact (han (Finset.mem_insert.mpr (Or.inl he))).elim
      · have haρ : a ∈ ρ := by rw [← YoungDiagram.mem_cells,hρ]; exact Finset.mem_erase.mpr ⟨hay,ha⟩
        have hbρ : b ∈ ρ := by rw [← YoungDiagram.mem_cells,hρ]; exact Finset.mem_erase.mpr ⟨hby,hb⟩
        exact hs.2 a haρ hanν b hbρ hbnν hab

theorem nonhorizontal_predecessor_exists {ν μ η : YoungDiagram}
    (hn : ¬ HorizontalStrip ν μ) (hc : Covers ν η) (hs : HorizontalStrip η μ) :
    ∃ ρ : YoungDiagram, Covers ρ μ ∧ HorizontalStrip ν ρ := by
  obtain ⟨x,y,hx,hxn,hy,hyn,hxy,hr⟩ := not_horizontalStrip_pair (hc.1.trans hs.1) hn
  obtain ⟨hxη,hyη,hη⟩ := successor_vertical_pair hc hs hx hxn hy hyn hxy hr
  have hmax : ∀ z, z ∈ μ → y ≤ z → z=y := by
    intro z hz hyz
    have hznη : z ∉ η := fun hzη => hyη (η.isLowerSet hyz hzη)
    by_cases hcol : z.2=y.2
    · exact (hs.2 z hz hznη y hy hyη hcol)
    · let a : Cell := (x.1,z.2)
      have haμ : a ∈ μ := μ.up_left_mem (hr.le.trans hyz.1) le_rfl hz
      have hanη : a ∉ η := by
        intro haη
        rw [← YoungDiagram.mem_cells,hη] at haη
        rcases Finset.mem_insert.mp haη with hax | haν
        · have he := congrArg Prod.snd hax
          exact hcol (he.trans hxy)
        · have hxa : x ≤ a := by
            change x.1 ≤ x.1 ∧ x.2 ≤ z.2
            exact ⟨le_rfl,hxy.le.trans hyz.2⟩
          exact hxn (ν.isLowerSet hxa haν)
      have he := hs.2 a haμ hanη z hz hznη rfl
      have he1 := congrArg Prod.fst he
      change x.1=z.1 at he1
      have := hyz.1
      omega
  let ρ : YoungDiagram := ⟨μ.cells.erase y,by
    intro z a haz hz
    obtain ⟨hzy,hzμ⟩ := Finset.mem_erase.mp hz
    exact Finset.mem_erase.mpr ⟨fun hay => hzy (hmax z hzμ (hay ▸ haz)),μ.isLowerSet haz hzμ⟩⟩
  have hcρ : Covers ρ μ := by
    refine ⟨Finset.erase_subset _ _, ?_⟩
    exact Finset.card_erase_add_one hy
  have hνρ : ν ≤ ρ := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun hzy => hyn (hzy ▸ hz), hs.1 (hc.1 hz)⟩
  refine ⟨ρ,hcρ,hνρ,?_⟩
  intro a ha han b hb hbn hab
  obtain ⟨hay,haμ⟩ := Finset.mem_erase.mp ha
  obtain ⟨hby,hbμ⟩ := Finset.mem_erase.mp hb
  by_cases hax : a=x
  · subst a
    by_cases hbx : b=x
    · exact hbx.symm
    · have hbnη : b ∉ η := by rw [← YoungDiagram.mem_cells,hη]; simpa only [Finset.mem_insert, not_or,YoungDiagram.mem_cells] using And.intro hbx hbn
      have he := hs.2 b hbμ hbnη y hy hyη (hab.symm.trans hxy)
      exact (hby he).elim
  · by_cases hbx : b=x
    · subst b
      have hanη : a ∉ η := by rw [← YoungDiagram.mem_cells,hη]; simpa only [Finset.mem_insert, not_or,YoungDiagram.mem_cells] using And.intro hax han
      have he := hs.2 a haμ hanη y hy hyη (hab.trans hxy)
      exact (hay he).elim
    · have hanη : a ∉ η := by rw [← YoungDiagram.mem_cells,hη]; simpa only [Finset.mem_insert, not_or,YoungDiagram.mem_cells] using And.intro hax han
      have hbnη : b ∉ η := by rw [← YoungDiagram.mem_cells,hη]; simpa only [Finset.mem_insert, not_or,YoungDiagram.mem_cells] using And.intro hbx hbn
      exact hs.2 a haμ hanη b hbμ hbnη hab

def lowerStripIntermediates (ν μ : YoungDiagram) : Finset YoungDiagram :=
  (oneBoxPredecessors μ).filter (HorizontalStrip ν)

def upperStripIntermediates (ν μ : YoungDiagram) : Finset YoungDiagram :=
  (oneBoxSuccessors ν).filter (fun η => HorizontalStrip η μ)

lemma mem_lowerStripIntermediates {ν μ ρ : YoungDiagram} :
    ρ ∈ lowerStripIntermediates ν μ ↔ Covers ρ μ ∧ HorizontalStrip ν ρ := by
  simp only [lowerStripIntermediates,Finset.mem_filter,mem_predecessors]

lemma mem_upperStripIntermediates {ν μ η : YoungDiagram} :
    η ∈ upperStripIntermediates ν μ ↔ Covers ν η ∧ HorizontalStrip η μ := by
  simp only [upperStripIntermediates,Finset.mem_filter,mem_successors]

theorem nonhorizontal_intermediate_card (ν μ : YoungDiagram) (hn : ¬ HorizontalStrip ν μ) :
    (lowerStripIntermediates ν μ).card = (upperStripIntermediates ν μ).card := by
  have hL : (lowerStripIntermediates ν μ).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro ρ hρ σ hσ
    obtain ⟨hcρ,hsρ⟩ := mem_lowerStripIntermediates.mp hρ
    obtain ⟨hcσ,hsσ⟩ := mem_lowerStripIntermediates.mp hσ
    exact nonhorizontal_predecessor_unique hn hcρ hsρ hcσ hsσ
  have hU : (upperStripIntermediates ν μ).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro η hη θ hθ
    obtain ⟨hcη,hsη⟩ := mem_upperStripIntermediates.mp hη
    obtain ⟨hcθ,hsθ⟩ := mem_upperStripIntermediates.mp hθ
    exact nonhorizontal_successor_unique hn hcη hsη hcθ hsθ
  have hne : (lowerStripIntermediates ν μ).Nonempty ↔ (upperStripIntermediates ν μ).Nonempty := by
    constructor
    · rintro ⟨ρ,hρ⟩
      obtain ⟨hcρ,hsρ⟩ := mem_lowerStripIntermediates.mp hρ
      obtain ⟨η,hcη,hsη⟩ := nonhorizontal_successor_exists hn hcρ hsρ
      exact ⟨η,mem_upperStripIntermediates.mpr ⟨hcη,hsη⟩⟩
    · rintro ⟨η,hη⟩
      obtain ⟨hcη,hsη⟩ := mem_upperStripIntermediates.mp hη
      obtain ⟨ρ,hcρ,hsρ⟩ := nonhorizontal_predecessor_exists hn hcη hsη
      exact ⟨ρ,mem_lowerStripIntermediates.mpr ⟨hcρ,hsρ⟩⟩
  rw [← Finset.card_pos,← Finset.card_pos] at hne
  omega

def stripRows (ν μ : YoungDiagram) : Finset ℕ :=
  (Finset.range μ.card).filter (fun i => ν.rowLen i < μ.rowLen i)

lemma mem_stripRows {ν μ : YoungDiagram} {i : ℕ} :
    i ∈ stripRows ν μ ↔ ν.rowLen i < μ.rowLen i := by
  simp only [stripRows,Finset.mem_filter,Finset.mem_range]
  constructor
  · exact And.right
  · intro hi
    have hc : (i,ν.rowLen i) ∈ μ := μ.mem_iff_lt_rowLen.mpr hi
    exact ⟨(cell_bounded μ ⟨_,hc⟩).1,hi⟩

theorem horizontal_upper_card {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    (stripRows ν μ).card=(upperStripIntermediates ν μ).card := by
  apply Finset.card_bij (fun i hi => addRow ν i (horizontalStrip_addable_row hs i (mem_stripRows.mp hi)))
  · intro i hi
    have hrow := mem_stripRows.mp hi
    have hc := covers_addRow ν i (horizontalStrip_addable_row hs i hrow)
    have hle : addRow ν i (horizontalStrip_addable_row hs i hrow) ≤ μ := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzν
      · exact μ.mem_iff_lt_rowLen.mpr hrow
      · exact hs.1 hzν
    exact mem_upperStripIntermediates.mpr ⟨hc,horizontalStrip_inner hs hc.1 hle⟩
  · intro i hi j hj he
    exact addRow_injective ν i j _ _ he
  · intro η hη
    obtain ⟨hc,hstrip⟩ := mem_upperStripIntermediates.mp hη
    obtain ⟨i,hi,rfl⟩ := covers_addRow_eq hc
    have hrow : ν.rowLen i < μ.rowLen i := by
      apply μ.mem_iff_lt_rowLen.mp
      apply hstrip.1
      exact Finset.mem_insert_self _ _
    exact ⟨i,mem_stripRows.mpr hrow,rfl⟩

lemma covers_erase_corner {ρ μ : YoungDiagram} (hc : Covers ρ μ) :
    ∃ c : Cell, ∃ hcorner : c ∈ corners μ, ρ=g61a_er μ c hcorner := by
  obtain ⟨c,hcρ,hcμ⟩ := covers_insert hc
  have hcIn : c ∈ μ := by change c ∈ μ.cells; rw [hcμ]; exact Finset.mem_insert_self _ _
  have hcorner : c ∈ corners μ := by
    apply Finset.mem_filter.mpr
    refine ⟨hcIn,?_,?_⟩
    · intro hd
      have hd' : (c.1+1,c.2) ∈ insert c ρ.cells := hcμ ▸ hd
      rcases Finset.mem_insert.mp hd' with he | he
      · have hh := congrArg Prod.fst he; omega
      · exact hcρ (ρ.up_left_mem (Nat.le_succ _) le_rfl he)
    · intro hd
      have hd' : (c.1,c.2+1) ∈ insert c ρ.cells := hcμ ▸ hd
      rcases Finset.mem_insert.mp hd' with he | he
      · have hh := congrArg Prod.snd he; omega
      · exact hcρ (ρ.up_left_mem le_rfl (Nat.le_succ _) he)
  refine ⟨c,hcorner,?_⟩
  apply YoungDiagram.ext
  rw [g61a_er_cells,hcμ,Finset.erase_insert hcρ]

theorem horizontal_lower_card {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    (stripRows ν μ).card=(lowerStripIntermediates ν μ).card := by
  apply Finset.card_bij (fun i hi => g61a_er μ (i,μ.rowLen i-1)
    (horizontalStrip_removable_row hs i (mem_stripRows.mp hi)))
  · intro i hi
    have hrow := mem_stripRows.mp hi
    have hcorner := horizontalStrip_removable_row hs i hrow
    have hc : Covers (g61a_er μ (i,μ.rowLen i-1) hcorner) μ :=
      ⟨Finset.erase_subset _ _,Finset.card_erase_add_one (g61a_corner_mem hcorner)⟩
    have hle : ν ≤ g61a_er μ (i,μ.rowLen i-1) hcorner := by
      intro z hz
      apply Finset.mem_erase.mpr
      refine ⟨?_,hs.1 hz⟩
      intro he
      rw [he] at hz
      have hh := ν.mem_iff_lt_rowLen.mp hz
      omega
    exact mem_lowerStripIntermediates.mpr ⟨hc,horizontalStrip_outer hs hle hc.1⟩
  · intro i hi j hj he
    have hc := congrArg YoungDiagram.cells he
    simp only [g61a_er_cells] at hc
    have hp := (Finset.erase_inj μ.cells
      (g61a_corner_mem (horizontalStrip_removable_row hs i (mem_stripRows.mp hi)))).mp hc
    exact congrArg Prod.fst hp
  · intro ρ hρ
    obtain ⟨hc,hstrip⟩ := mem_lowerStripIntermediates.mp hρ
    obtain ⟨c,hcorner,rfl⟩ := covers_erase_corner hc
    have hnotν : c ∉ ν := by
      intro hcν
      have hh := hstrip.1 hcν
      exact Finset.notMem_erase c μ.cells hh
    have hclen : c.2+1=μ.rowLen c.1 := (corner_iff.mp hcorner).1
    have hcν : ν.rowLen c.1 ≤ c.2 := by
      exact Nat.le_of_not_gt (fun hh => hnotν (ν.mem_iff_lt_rowLen.mpr hh))
    have hrow : ν.rowLen c.1 < μ.rowLen c.1 := by omega
    refine ⟨c.1,mem_stripRows.mpr hrow,?_⟩
    have he : (c.1,μ.rowLen c.1-1)=c := by
      apply Prod.ext
      · rfl
      · dsimp only
        omega
    apply YoungDiagram.ext
    simp only [g61a_er_cells,he]

/-- Adding a single box commutes with adding a horizontal strip, at the level
of the exact finite intermediate counts. -/
theorem strip_corner_commutation (ν μ : YoungDiagram) :
    (lowerStripIntermediates ν μ).card=(upperStripIntermediates ν μ).card := by
  by_cases hs : HorizontalStrip ν μ
  · exact (horizontal_lower_card hs).symm.trans (horizontal_upper_card hs)
  · exact nonhorizontal_intermediate_card ν μ hs

end
end WeldedPath.SpechtPieri
end

-- MODULE YoungPieriDimensions
section

namespace WeldedPath.SpechtPieri

noncomputable section
open Classical YoungCounts YoungBranching OAI.PartialPermutation
open scoped BigOperators

def stripDimension (j : ℕ) (μ : YoungDiagram) : ℕ :=
  ∑ ν ∈ level j, if HorizontalStrip ν μ then tableauCount ν else 0

theorem stripDimension_succ (j : ℕ) (μ : YoungDiagram) :
    stripDimension (j+1) μ = ∑ ρ ∈ oneBoxPredecessors μ, stripDimension j ρ := by
  calc
    _ = ∑ η ∈ level (j+1), (if HorizontalStrip η μ then 1 else 0) *
        ∑ ν ∈ oneBoxPredecessors η, tableauCount ν := by
      apply Finset.sum_congr rfl
      intro η hη
      have hcard := mem_level.mp hη
      have hne : η.cells.Nonempty := Finset.card_pos.mp (by change 0<η.card; omega)
      rw [← tableauBranching η hne]
      split_ifs <;> simp
    _ = ∑ ν ∈ level j, tableauCount ν *
        ∑ η ∈ oneBoxSuccessors ν, if HorizontalStrip η μ then 1 else 0 :=
      weighted_level_adjacency j tableauCount (fun η => if HorizontalStrip η μ then 1 else 0)
    _ = ∑ ν ∈ level j, tableauCount ν * (upperStripIntermediates ν μ).card := by
      apply Finset.sum_congr rfl
      intro ν hν
      congr 1
      simp only [upperStripIntermediates,Finset.card_eq_sum_ones,Finset.sum_filter]
    _ = ∑ ν ∈ level j, tableauCount ν * (lowerStripIntermediates ν μ).card := by
      apply Finset.sum_congr rfl
      intro ν hν
      rw [strip_corner_commutation]
    _ = ∑ ν ∈ level j, ∑ ρ ∈ oneBoxPredecessors μ,
        if HorizontalStrip ν ρ then tableauCount ν else 0 := by
      apply Finset.sum_congr rfl
      intro ν hν
      simp only [lowerStripIntermediates,Finset.card_eq_sum_ones,Finset.sum_filter,
        Finset.mul_sum,mul_ite,mul_one,mul_zero]
    _ = _ := Finset.sum_comm

lemma horizontalStrip_bot_iff (μ : YoungDiagram) :
    HorizontalStrip ⊥ μ ↔ μ=YoungBranching.rowDiagram μ.card := by
  constructor
  · intro hs
    apply YoungBranching.eq_rowDiagram_of_rows_zero μ
    intro x
    have hx0 : (0,x.1.2) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl x.2
    have he := hs.2 x.1 x.2 (by simp) (0,x.1.2) hx0 (by simp) rfl
    exact congrArg Prod.fst he
  · intro he
    refine ⟨bot_le,?_⟩
    intro x hx hxn y hy hyn hxy
    rw [he,YoungBranching.mem_rowDiagram] at hx hy
    exact Prod.ext (hx.1.trans hy.1.symm) hxy

theorem stripDimension_zero (μ : YoungDiagram) :
    stripDimension 0 μ = if μ=YoungBranching.rowDiagram μ.card then 1 else 0 := by
  rw [stripDimension,level_zero,Finset.sum_singleton]
  have hcount : tableauCount (⊥ : YoungDiagram)=1 := tableauCount_of_card_zero _ rfl
  simp only [hcount,horizontalStrip_bot_iff]

theorem initial_fixed_pieri_dimension (m n : ℕ) (h : m ≤ n) (μ : DiagramCounting.Shape n) :
    Module.finrank ℂ (initialFixed μ h) = stripDimension (n-m) μ.1 := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hmn : m=n
    · subst m
      rw [Nat.sub_self,initial_fixed_dimension_self,stripDimension_zero]
      have he : μ=YoungBranching.rowShape n ↔ μ.1=YoungBranching.rowDiagram μ.1.card := by
        have hc : μ.1.card=n := μ.2
        constructor
        · intro hh
          have hv := congrArg (fun ρ : DiagramCounting.Shape n => ρ.val) hh
          simpa only [hc] using hv
        · intro hh
          apply Subtype.ext
          simpa only [hc] using hh
      simp only [he]
    · have hm : m<n := lt_of_le_of_ne h hmn
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      have hmk : m≤k := by omega
      rw [initial_fixed_dimension_branching μ hmk]
      calc
        _ = ∑ ν : Predecessor μ, stripDimension (k-m) ν.1 := by
          apply Finset.sum_congr rfl
          intro ν hν
          exact ih k (Nat.lt_succ_self _) m hmk (predecessorShape μ ν)
        _ = ∑ ν ∈ oneBoxPredecessors μ.1, stripDimension (k-m) ν := Finset.sum_coe_sort _ _
        _ = _ := by
          have he : k+1-m=k-m+1 := by omega
          rw [he,stripDimension_succ]

end
end WeldedPath.SpechtPieri
end



end

-- Solutions.YoungTranspositionContent
section

namespace WeldedPath.YoungTranspositionContent

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open scoped BigOperators

theorem swap_nontransversal (μ : YoungDiagram) (a b : μ.cells)
    (hr : row μ a < row μ b) (hc : OAI.PartialPermutation.YoungTabloid.col μ a ≠ OAI.PartialPermutation.YoungTabloid.col μ b) :
    ¬ Transversal μ (relabel μ (Equiv.swap a b) (canonical μ)) := by
  let z : μ.cells := ⟨(row μ a,OAI.PartialPermutation.YoungTabloid.col μ b), μ.up_left_mem (Nat.le_of_lt hr) le_rfl b.2⟩
  have hza : z ≠ a := by
    intro hz
    apply hc
    exact (congrArg (OAI.PartialPermutation.YoungTabloid.col μ) hz).symm
  have hzb : z ≠ b := by
    intro hz
    have hz' : row μ z = row μ b := congrArg (row μ) hz
    change row μ a = row μ b at hz'
    exact (Nat.ne_of_lt hr) hz'
  intro ht
  apply hzb
  apply (ht b z rfl ?_).symm
  change row μ ((Equiv.swap a b)⁻¹ b) = row μ ((Equiv.swap a b)⁻¹ z)
  rw [Equiv.swap_inv, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hza hzb]
  rfl

theorem polytabloid_swap_coefficient (μ : YoungDiagram) (a b : μ.cells) :
    polytabloid μ (relabel μ (Equiv.swap a b) (canonical μ)) =
      if row μ a = row μ b then 1 else if OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b then -1 else 0 := by
  by_cases hr : row μ a = row μ b
  · rw [if_pos hr, relabel_swap_fix μ (canonical μ) a b hr, polytabloid_canonical]
  · rw [if_neg hr]
    by_cases hc : OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b
    · rw [if_pos hc]
      have hab : a ≠ b := fun h => hr (congrArg (row μ) h)
      have he := polytabloid_alternating μ ⟨Equiv.swap a b,swap_mem_column μ a b hc⟩ (canonical μ)
      change polytabloid μ (relabel μ (Equiv.swap a b) (canonical μ)) =
        signC (Equiv.swap a b) * polytabloid μ (canonical μ) at he
      simpa only [signC_swap a b hab, polytabloid_canonical, mul_one] using he
    · rw [if_neg hc]
      apply alternating_zero_nontransversal μ _ (polytabloid_alternating μ)
      rcases lt_or_gt_of_ne hr with hlt | hgt
      · exact swap_nontransversal μ a b hlt hc
      · rw [Equiv.swap_comm]
        exact swap_nontransversal μ b a hgt (Ne.symm hc)

section Operators
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

def orderedSwapSum (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V :=
  ∑ a, ∑ b, if a = b then 0 else ρ (Equiv.swap a b)

theorem orderedSwapSum_commute (ρ : Representation ℂ (Equiv.Perm α) V) (g : Equiv.Perm α) :
    orderedSwapSum ρ * ρ g = ρ g * orderedSwapSum ρ := by
  simp only [orderedSwapSum, Finset.sum_mul, Finset.mul_sum]
  apply Fintype.sum_equiv g.symm
  intro a
  apply Fintype.sum_equiv g.symm
  intro b
  by_cases hab : a = b
  · simp [hab]
  · have hab' : g.symm a ≠ g.symm b := fun h => hab (g.symm.injective h)
    rw [if_neg hab, if_neg hab', ← map_mul, ← map_mul, Equiv.swap_mul_eq_mul_swap]
    rfl

theorem orderedSwapSum_relabel {β : Type*} [Fintype β] [DecidableEq β]
    (ρ : Representation ℂ (Equiv.Perm β) V) (e : α ≃ β) :
    orderedSwapSum (ρ.comp e.permCongrHom.toMonoidHom) = orderedSwapSum ρ := by
  unfold orderedSwapSum
  apply Fintype.sum_equiv e
  intro a
  apply Fintype.sum_equiv e
  intro b
  by_cases hab : a = b
  · simp [hab]
  · have hab' : e a ≠ e b := fun h => hab (e.injective h)
    rw [if_neg hab, if_neg hab']
    change ρ (e.permCongrHom (Equiv.swap a b)) = ρ (Equiv.swap (e a) (e b))
    congr 1
    apply Equiv.ext
    intro y
    change e (Equiv.swap a b (e.symm y)) = Equiv.swap (e a) (e b) y
    simpa only [e.apply_symm_apply] using (e.injective.swap_apply a b (e.symm y)).symm

theorem orderedSwapSum_scalar [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm α) V) [Representation.IsIrreducible ρ] :
    ∃ c : ℂ, orderedSwapSum ρ = c • (1 : Module.End ℂ V) := by
  let T : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := orderedSwapSum ρ
      isIntertwining' := fun g => by
        simpa only [Module.End.mul_eq_comp] using orderedSwapSum_commute ρ g }
  obtain ⟨c,hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.surjective T
  refine ⟨c, ?_⟩
  rw [Representation.IntertwiningMap.algebraMap_apply] at hc
  exact (congrArg Representation.IntertwiningMap.toLinearMap hc).symm
end Operators

def pairScore (μ : YoungDiagram) : ℂ :=
  ∑ a : μ.cells, ∑ b : μ.cells, if a = b then 0 else
    if row μ a = row μ b then 1 else if OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b then -1 else 0

def rowEarlierEquiv (μ : YoungDiagram) (b : μ.cells) :
    {a : μ.cells // row μ a = row μ b ∧ OAI.PartialPermutation.YoungTabloid.col μ a < OAI.PartialPermutation.YoungTabloid.col μ b} ≃ Fin (OAI.PartialPermutation.YoungTabloid.col μ b) where
  toFun a := ⟨OAI.PartialPermutation.YoungTabloid.col μ a.1, a.2.2⟩
  invFun i := ⟨⟨(row μ b,i.val), μ.up_left_mem le_rfl (Nat.le_of_lt i.2) b.2⟩,rfl,i.2⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext a.2.1.symm rfl
  right_inv i := rfl

def columnEarlierEquiv (μ : YoungDiagram) (b : μ.cells) :
    {a : μ.cells // OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b ∧ row μ a < row μ b} ≃ Fin (row μ b) where
  toFun a := ⟨row μ a.1, a.2.2⟩
  invFun i := ⟨⟨(i.val,OAI.PartialPermutation.YoungTabloid.col μ b), μ.up_left_mem (Nat.le_of_lt i.2) le_rfl b.2⟩,rfl,i.2⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl a.2.1.symm
  right_inv i := rfl

theorem rowEarlier_sum (μ : YoungDiagram) (b : μ.cells) :
    (∑ a : μ.cells, if row μ a = row μ b ∧ OAI.PartialPermutation.YoungTabloid.col μ a < OAI.PartialPermutation.YoungTabloid.col μ b then (1 : ℂ) else 0) = OAI.PartialPermutation.YoungTabloid.col μ b := by
  have h := Fintype.card_congr (rowEarlierEquiv μ b)
  rw [Fintype.card_fin] at h
  simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Fintype.card_subtype] using congrArg (fun t : ℕ => (t : ℂ)) h

theorem columnEarlier_sum (μ : YoungDiagram) (b : μ.cells) :
    (∑ a : μ.cells, if OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b ∧ row μ a < row μ b then (1 : ℂ) else 0) = row μ b := by
  have h := Fintype.card_congr (columnEarlierEquiv μ b)
  rw [Fintype.card_fin] at h
  simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Fintype.card_subtype] using congrArg (fun t : ℕ => (t : ℂ)) h

theorem pair_score_split (μ : YoungDiagram) (a b : μ.cells) :
    (if a = b then (0 : ℂ) else
      if row μ a = row μ b then 1 else if OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b then -1 else 0) =
      (if row μ a = row μ b ∧ OAI.PartialPermutation.YoungTabloid.col μ a < OAI.PartialPermutation.YoungTabloid.col μ b then 1 else 0) +
      (if row μ b = row μ a ∧ OAI.PartialPermutation.YoungTabloid.col μ b < OAI.PartialPermutation.YoungTabloid.col μ a then 1 else 0) -
      (if OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b ∧ row μ a < row μ b then 1 else 0) -
      (if OAI.PartialPermutation.YoungTabloid.col μ b = OAI.PartialPermutation.YoungTabloid.col μ a ∧ row μ b < row μ a then 1 else 0) := by
  by_cases hab : a = b
  · subst b; simp
  by_cases hr : row μ a = row μ b
  · have hc : OAI.PartialPermutation.YoungTabloid.col μ a ≠ OAI.PartialPermutation.YoungTabloid.col μ b := fun hc => hab (Subtype.ext (Prod.ext hr hc))
    rcases lt_or_gt_of_ne hc with hl | hl
    · simp [hab,hr,hc,Ne.symm hc,hl,not_lt_of_ge (Nat.le_of_lt hl)]
    · simp [hab,hr,hc,Ne.symm hc,hl,not_lt_of_ge (Nat.le_of_lt hl)]
  · by_cases hc : OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b
    · rcases lt_or_gt_of_ne hr with hl | hl
      · simp [hab,hr,Ne.symm hr,hc,hl,not_lt_of_ge (Nat.le_of_lt hl)]
      · simp [hab,hr,Ne.symm hr,hc,hl,not_lt_of_ge (Nat.le_of_lt hl)]
    · simp [hab,hr,Ne.symm hr,hc,Ne.symm hc]

def contentSum (μ : YoungDiagram) : ℂ := ∑ a : μ.cells, ((OAI.PartialPermutation.YoungTabloid.col μ a : ℂ) - row μ a)

theorem pairScore_eq_twice_content (μ : YoungDiagram) : pairScore μ = 2 * contentSum μ := by
  unfold pairScore
  simp_rw [pair_score_split]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hr : (∑ a : μ.cells, ∑ b : μ.cells,
      if row μ a = row μ b ∧ OAI.PartialPermutation.YoungTabloid.col μ a < OAI.PartialPermutation.YoungTabloid.col μ b then (1 : ℂ) else 0) = ∑ b : μ.cells, (OAI.PartialPermutation.YoungTabloid.col μ b : ℂ) := by
    rw [Finset.sum_comm]
    simp only [rowEarlier_sum]
  have hc : (∑ a : μ.cells, ∑ b : μ.cells,
      if OAI.PartialPermutation.YoungTabloid.col μ a = OAI.PartialPermutation.YoungTabloid.col μ b ∧ row μ a < row μ b then (1 : ℂ) else 0) = ∑ b : μ.cells, (row μ b : ℂ) := by
    rw [Finset.sum_comm]
    simp only [columnEarlier_sum]
  rw [hr,hc]
  simp only [rowEarlier_sum,columnEarlier_sum,contentSum,Finset.sum_sub_distrib]
  ring

theorem specht_orderedSwapSum (μ : YoungDiagram) :
    orderedSwapSum (spechtRep μ) = pairScore μ •
      (1 : Module.End ℂ (spechtSub μ).toSubmodule) := by
  obtain ⟨c,hc⟩ := orderedSwapSum_scalar (spechtRep μ)
  let e : (spechtSub μ).toSubmodule := ⟨polytabloid μ, polytabloid_mem_specht μ⟩
  have he := congrArg (fun T : Module.End ℂ (spechtSub μ).toSubmodule =>
    (T e).val (canonical μ)) hc
  have hl : ((orderedSwapSum (spechtRep μ)) e).val (canonical μ) = pairScore μ := by
    simp only [orderedSwapSum, LinearMap.sum_apply, Submodule.coe_sum,
      WithLp.ofLp_sum, Finset.sum_apply]
    change (∑ a, ∑ b, ((if a = b then (0 : Module.End ℂ (spechtSub μ).toSubmodule)
      else spechtRep μ (Equiv.swap a b)) e).val (canonical μ)) = _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b
    · simp only [if_pos hab, LinearMap.zero_apply, Submodule.coe_zero, PiLp.zero_apply]
    · rw [if_neg hab]
      change polytabloid μ (relabel μ (Equiv.swap a b)⁻¹ (canonical μ)) = _
      rw [Equiv.swap_inv, polytabloid_swap_coefficient]
      simp only [if_neg hab]
  have hr : ((c • (1 : Module.End ℂ (spechtSub μ).toSubmodule)) e).val (canonical μ) = c := by
    change c * polytabloid μ (canonical μ) = c
    rw [polytabloid_canonical, mul_one]
  rw [hl, hr] at he
  rw [hc, he]

theorem specht_transposition_content (μ : YoungDiagram) :
    (1/2 : ℂ) • orderedSwapSum (spechtRep μ) = contentSum μ •
      (1 : Module.End ℂ (spechtSub μ).toSubmodule) := by
  rw [specht_orderedSwapSum, pairScore_eq_twice_content, smul_smul]
  congr 1
  ring

theorem actual_transposition_content {n : ℕ} (μ : DiagramCounting.Shape n) :
    (1/2 : ℂ) • orderedSwapSum (SpechtActual.rep μ) = contentSum μ.1 •
      (1 : Module.End ℂ (spechtSub μ.1).toSubmodule) := by
  rw [SpechtActual.rep, orderedSwapSum_relabel]
  exact specht_transposition_content μ.1

end
end WeldedPath.YoungTranspositionContent

end

-- Solutions.YoungStripContentGap
section

namespace WeldedPath.YoungStripContent

noncomputable section
open Classical SpechtPieri YoungCounts OAI.PartialPermutation
open scoped BigOperators

def contentInt (μ : YoungDiagram) : ℤ := ∑ a ∈ μ.cells, ((a.2 : ℤ) - a.1)

def stripCols (ν μ : YoungDiagram) : Finset ℕ := (μ.cells \ ν.cells).image Prod.snd

lemma added_row_eq_colLen {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    {a : ℕ × ℕ} (ha : a ∈ μ.cells \ ν.cells) : a.1 = ν.colLen a.2 := by
  have hx := Finset.mem_sdiff.mp ha
  have hlow : ν.colLen a.2 ≤ a.1 := by
    exact Nat.le_of_not_gt (fun h => hx.2 (ν.mem_iff_lt_colLen.mpr h))
  have hhi := μ.mem_iff_lt_colLen.mp hx.1
  have hcap := (horizontalStrip_colLen hs.1).mp hs a.2
  omega

lemma stripCols_card {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    (stripCols ν μ).card = μ.card - ν.card := by
  have hi : Set.InjOn Prod.snd (↑(μ.cells \ ν.cells) : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact hs.2 a (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp ha).2
      b (Finset.mem_sdiff.mp hb).1 (Finset.mem_sdiff.mp hb).2 hab
  rw [stripCols, Finset.card_image_iff.mpr hi]
  exact Finset.card_sdiff_of_subset hs.1

lemma mem_stripCols_iff {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) (c : ℕ) :
    c ∈ stripCols ν μ ↔ ν.colLen c < μ.colLen c := by
  constructor
  · rintro hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    rw [← added_row_eq_colLen hs ha]
    exact μ.mem_iff_lt_colLen.mp (Finset.mem_sdiff.mp ha).1
  · intro hc
    apply Finset.mem_image.mpr
    refine ⟨(ν.colLen c,c), Finset.mem_sdiff.mpr ⟨μ.mem_iff_lt_colLen.mpr hc, ?_⟩, rfl⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen, lt_self_iff_false, not_false_eq_true]

lemma colLen_eq_of_not_strip {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    {c : ℕ} (hc : c ∉ stripCols ν μ) : μ.colLen c = ν.colLen c := by
  have hlo : ν.colLen c ≤ μ.colLen c := by
    by_contra hn
    have hi : μ.colLen c < ν.colLen c := Nat.lt_of_not_ge hn
    have hh := μ.mem_iff_lt_colLen.mp (hs.1 (ν.mem_iff_lt_colLen.mpr hi))
    omega
  have hhi := not_lt.mp (mt (mem_stripCols_iff hs c).mpr hc)
  omega

lemma stripCols_subset_range {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    stripCols ν μ ⊆ Finset.range (μ.rowLen 0) := by
  intro c hc
  have hp : 0 < μ.colLen c := lt_of_le_of_lt (Nat.zero_le _) ((mem_stripCols_iff hs c).mp hc)
  exact Finset.mem_range.mpr (μ.mem_iff_lt_rowLen.mp (μ.mem_iff_lt_colLen.mpr hp))

lemma colLen_zero_of_rowLen_le (ν : YoungDiagram) {c : ℕ} (hc : ν.rowLen 0 ≤ c) :
    ν.colLen c = 0 := by
  by_contra hn
  have hm := ν.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero hn)
  have hl := ν.mem_iff_lt_rowLen.mp hm
  omega

lemma omitted_column_lt_card {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    (n : ℕ) (hcard : (stripCols ν μ).card = n) {c : ℕ}
    (hc : c < n) (hcn : c ∉ stripCols ν μ) : c < ν.card := by
  have hpos : 0 < ν.colLen c := by
    by_contra hn
    have hz : ν.colLen c = 0 := by omega
    have hmz : μ.colLen c = 0 := (colLen_eq_of_not_strip hs hcn).trans hz
    have hsub : stripCols ν μ ⊆ Finset.range c := by
      intro d hd
      apply Finset.mem_range.mpr
      by_contra hdn
      have hle := μ.colLen_anti c d (Nat.le_of_not_gt hdn)
      have hdp := (mem_stripCols_iff hs d).mp hd
      omega
    have hle := Finset.card_le_card hsub
    rw [hcard, Finset.card_range] at hle
    omega
  have hrow : c < ν.rowLen 0 :=
    ν.mem_iff_lt_rowLen.mp (ν.mem_iff_lt_colLen.mpr hpos)
  exact hrow.trans_le (DiagramCounting.rowLen_le_card ν 0)

lemma strip_content_sum {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    contentInt μ - contentInt ν =
      ∑ c ∈ stripCols ν μ, ((c : ℤ) - ν.colLen c) := by
  rw [contentInt, contentInt, ← Finset.sum_sdiff_eq_sub hs.1]
  rw [stripCols, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [added_row_eq_colLen hs ha]
  · intro a ha b hb hab
    exact hs.2 a (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp ha).2
      b (Finset.mem_sdiff.mp hb).1 (Finset.mem_sdiff.mp hb).2 hab

lemma sum_colLen (ν : YoungDiagram) (n : ℕ) (hn : ν.rowLen 0 ≤ n) :
    ∑ c ∈ Finset.range n, ν.colLen c = ν.card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := ν.cells) (t := Finset.range n)
    (f := Prod.snd) (fun a ha => Finset.mem_range.mpr
      ((ν.mem_iff_lt_rowLen.mp ha).trans_le ((ν.rowLen_anti 0 a.1 (Nat.zero_le _)).trans hn)))
  simpa only [YoungDiagram.colLen_eq_card, YoungDiagram.col] using h.symm

lemma minimum_content_sum (ν : YoungDiagram) (n : ℕ) (hn : ν.rowLen 0 ≤ n) :
    (∑ c ∈ Finset.range n, ((c : ℤ) - ν.colLen c)) =
      (∑ c ∈ Finset.range n, (c : ℤ)) - ν.card := by
  rw [Finset.sum_sub_distrib]
  have hh : (∑ c ∈ Finset.range n, (ν.colLen c : ℤ)) = ν.card := by
    exact_mod_cast sum_colLen ν n hn
  rw [hh]

lemma equal_card_difference {α : Type*} [DecidableEq α] (S R : Finset α)
    (hc : S.card = R.card) : (S \ R).card = (R \ S).card := by
  rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm]
  omega

lemma finite_weight_gap (S : Finset ℕ) (n j : ℕ) (hj : j ≤ n)
    (hc : S.card = n) (w : ℕ → ℤ)
    (hlo : ∀ c ∈ S \ Finset.range n, (n : ℤ) ≤ w c)
    (hhi : ∀ c ∈ Finset.range n \ S, w c ≤ (j : ℤ)-1) :
    S = Finset.range n ∨
      (n : ℤ) - j + 1 ≤ (∑ c ∈ S, w c) - ∑ c ∈ Finset.range n, w c := by
  by_cases he : S = Finset.range n
  · exact Or.inl he
  right
  have hcard : (S \ Finset.range n).card = (Finset.range n \ S).card :=
    equal_card_difference S (Finset.range n) (by simpa using hc)
  have hpos : 1 ≤ (S \ Finset.range n).card := by
    by_contra hn
    have hz : (S \ Finset.range n).card = 0 := by omega
    have hsub : S ⊆ Finset.range n := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hz)
    exact he (Finset.eq_of_subset_of_card_le hsub (by simpa using hc.ge))
  have hB : ((S \ Finset.range n).card : ℤ) * n ≤ ∑ c ∈ S \ Finset.range n, w c := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hlo
  have hA : (∑ c ∈ Finset.range n \ S, w c) ≤ ((Finset.range n \ S).card : ℤ) * ((j : ℤ)-1) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hhi
  have hk : (1 : ℤ) ≤ (S \ Finset.range n).card := by exact_mod_cast hpos
  have hgap : (0 : ℤ) ≤ (n : ℤ)-j+1 := by omega
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  have hci : ((S \ Finset.range n).card : ℤ) = (Finset.range n \ S).card := by exact_mod_cast hcard
  nlinarith

theorem horizontal_content_gap {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    (n : ℕ) (hsize : μ.card = ν.card+n) (hn : ν.card ≤ n) :
    let excess := contentInt μ - contentInt ν - (∑ c ∈ Finset.range n, (c : ℤ)) + ν.card
    (stripCols ν μ = Finset.range n ∧ excess = 0) ∨
      (n : ℤ)-ν.card+1 ≤ excess := by
  dsimp only
  have hc : (stripCols ν μ).card = n := by rw [stripCols_card hs, hsize]; omega
  have hwidth : ν.rowLen 0 ≤ n := (DiagramCounting.rowLen_le_card ν 0).trans hn
  have hh := finite_weight_gap (stripCols ν μ) n ν.card hn hc
    (fun c => (c : ℤ)-ν.colLen c) (by
      intro c hc
      have hcn : n ≤ c := Nat.le_of_not_gt (fun hh => (Finset.mem_sdiff.mp hc).2 (Finset.mem_range.mpr hh))
      rw [colLen_zero_of_rowLen_le ν (hwidth.trans hcn), Nat.cast_zero, sub_zero]
      exact_mod_cast hcn) (by
      intro c hc
      have hlt := omitted_column_lt_card hs n (by rw [stripCols_card hs, hsize]; omega)
        (Finset.mem_range.mp (Finset.mem_sdiff.mp hc).1) (Finset.mem_sdiff.mp hc).2
      have hci : (c : ℤ) < ν.card := by exact_mod_cast hlt
      have hnonneg : (0 : ℤ) ≤ ν.colLen c := by positivity
      omega)
  rw [← strip_content_sum hs, minimum_content_sum ν n hwidth] at hh
  rcases hh with he | hgap
  · left
    refine ⟨he, ?_⟩
    rw [strip_content_sum hs, he, minimum_content_sum ν n hwidth]
    ring
  · right
    linarith

lemma stripCols_eq_range_iff_firstRow {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    (n : ℕ) (hsize : μ.card = ν.card+n) (hn : ν.card ≤ n) :
    stripCols ν μ = Finset.range n ↔ μ.rowLen 0 = n := by
  have hc : (stripCols ν μ).card = n := by rw [stripCols_card hs, hsize]; omega
  constructor
  · intro he
    have hlo : n ≤ μ.rowLen 0 := by
      have hh := Finset.card_le_card (stripCols_subset_range hs)
      simpa only [hc,Finset.card_range] using hh
    have hhi : μ.rowLen 0 ≤ n := by
      by_contra hhi
      have hp : 0 < μ.colLen n := μ.mem_iff_lt_colLen.mp
        (μ.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hhi))
      have hz := colLen_zero_of_rowLen_le ν ((DiagramCounting.rowLen_le_card ν 0).trans hn)
      have hm : n ∈ stripCols ν μ := (mem_stripCols_iff hs n).mpr (hz ▸ hp)
      rw [he,Finset.mem_range] at hm
      omega
    omega
  · intro he
    apply Finset.eq_of_subset_of_card_le
    · simpa only [he] using stripCols_subset_range hs
    · simp only [hc,Finset.card_range]
      exact le_rfl

theorem content_excess_nonneg_and_gap {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    (n : ℕ) (hsize : μ.card = ν.card+n) (hn : ν.card ≤ n) :
    let excess := contentInt μ - contentInt ν - (∑ c ∈ Finset.range n, (c : ℤ)) + ν.card
    0 ≤ excess ∧ (excess = 0 ↔ μ.rowLen 0 = n) ∧
      (μ.rowLen 0 ≠ n → (n : ℤ)-ν.card+1 ≤ excess) := by
  dsimp only
  rcases horizontal_content_gap hs n hsize hn with ⟨hS,hzero⟩ | hgap
  · have hrow := (stripCols_eq_range_iff_firstRow hs n hsize hn).mp hS
    exact ⟨by omega, ⟨fun _ => hrow, fun _ => hzero⟩, fun h => (h hrow).elim⟩
  · have hpos : (0 : ℤ) < (n : ℤ)-ν.card+1 := by omega
    have hrow : μ.rowLen 0 ≠ n := by
      intro hrow
      have hS := (stripCols_eq_range_iff_firstRow hs n hsize hn).mpr hrow
      have he : contentInt μ - contentInt ν =
          (∑ c ∈ Finset.range n, (c : ℤ))-ν.card := by
        rw [strip_content_sum hs,hS,minimum_content_sum ν n
          ((DiagramCounting.rowLen_le_card ν 0).trans hn)]
      omega
    exact ⟨by omega, ⟨by omega, fun h => (hrow h).elim⟩, fun _ => hgap⟩

lemma contentInt_complex (μ : YoungDiagram) :
    (contentInt μ : ℂ) = YoungTranspositionContent.contentSum μ := by
  simp only [contentInt, Int.cast_sum, Int.cast_sub, Int.cast_natCast,
    YoungTranspositionContent.contentSum]
  change (∑ x ∈ μ.cells, ((x.2 : ℂ)-x.1)) = ∑ a : μ.cells, ((a.val.2 : ℂ)-a.val.1)
  exact (Finset.sum_coe_sort μ.cells (fun a : ℕ × ℕ => (a.2 : ℂ)-a.1)).symm

lemma sum_range_int_eq_choose (n : ℕ) :
    (∑ c ∈ Finset.range n, (c : ℤ)) = (n.choose 2 : ℤ) := by
  rw [← Nat.cast_sum, Finset.sum_range_id, ← Nat.choose_two_right]

def excess (ν μ : YoungDiagram) (n : ℕ) : ℤ :=
  contentInt μ - contentInt ν - n.choose 2 + ν.card

theorem excess_gap {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    (n : ℕ) (hsize : μ.card = ν.card+n) (hn : ν.card ≤ n) :
    0 ≤ excess ν μ n ∧ (excess ν μ n = 0 ↔ μ.rowLen 0 = n) ∧
      (μ.rowLen 0 ≠ n → (n : ℤ)-ν.card+1 ≤ excess ν μ n) := by
  simpa only [excess, sum_range_int_eq_choose] using
    content_excess_nonneg_and_gap hs n hsize hn

lemma minimum_shape {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ)
    (n : ℕ) (hsize : μ.card = ν.card+n) (hn : ν.card ≤ n)
    (hrow : μ.rowLen 0 = n) :
    μ = prependRow n ν ((DiagramCounting.rowLen_le_card ν 0).trans hn) := by
  have hS := (stripCols_eq_range_iff_firstRow hs n hsize hn).mpr hrow
  ext a
  change a ∈ μ ↔ a ∈ prependRow n ν ((DiagramCounting.rowLen_le_card ν 0).trans hn)
  rw [mem_prependRow]
  by_cases hj : a.2 < n
  · have hp : ν.colLen a.2 < μ.colLen a.2 := (mem_stripCols_iff hs a.2).mp
      (hS ▸ Finset.mem_range.mpr hj)
    have hcap := (horizontalStrip_colLen hs.1).mp hs a.2
    have hlen : μ.colLen a.2 = ν.colLen a.2+1 := by omega
    rw [YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_colLen, hlen]
    omega
  · have hz := colLen_zero_of_rowLen_le ν
      (((DiagramCounting.rowLen_le_card ν 0).trans hn).trans (Nat.le_of_not_gt hj))
    have hmz := colLen_zero_of_rowLen_le μ (hrow ▸ Nat.le_of_not_gt hj)
    rw [YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_colLen, hmz, hz]
    omega



end
end WeldedPath.YoungStripContent

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





theorem addPair_apply_self {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) : I.addPair x y x = some y := by
  simp [InjDb.addPair, hx, hy]

theorem addPair_injective {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    Set.InjOn (I.addPair x) {y | I.symm y = none} := by
  intro y hy z hz h
  have hh := congrArg (fun J : InjDb s => J x) h
  rw [addPair_apply_self I x y hx hy, addPair_apply_self I x z hx hz] at hh
  exact Option.some.inj hh


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


theorem sum_basis [DecidableEq X] (ψ : Hil X) :
    (∑ x, ψ x • ket x) = ψ := by
  ext y
  simp [ket_apply]

theorem diagProj_apply [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) (x : X) :
    diagProj P ψ x = if P x then ψ x else 0 := by
  simp [diagProj, ketBra_apply, inner_ket, ket_apply]



theorem diagProj_ket [DecidableEq X] (P : X → Prop) [DecidablePred P] (x : X) :
    diagProj P (ket x) = if P x then ket x else 0 := by
  ext y
  by_cases hx : P x <;> by_cases hy : y = x <;>
    simp_all [diagProj_apply, ket_apply]





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




theorem Hlevel_le (r : ℕ) : Hlevel s r ≤ Hle s r := by
  cases r with
  | zero => exact le_rfl
  | succ r => exact inf_le_left


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









theorem flipDb_norm (s : ℕ) (ψ : Hil (InjDb s)) : ‖flipDb s ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  exact PEquiv.symm_symm




end WeldedPath.EncodedOracleUnitary

end

-- Solutions.WeldedPathOperatorPolar
section

namespace WeldedPath.OperatorPolar

open scoped BigOperators
open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]











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




end WeldedPath.CompletionFrame

end

-- Solutions.WeldedPathCompletionFrameInvariant
section

namespace WeldedPath.CompletionFrame

open Classical InjDb HilbertSupport CompletionLevels
open scoped BigOperators

variable {s : ℕ}





noncomputable def translate (a : Equiv.Perm (Fin s)) :
    Hil (Equiv.Perm (Fin s)) →ₗ[ℂ] Hil (Equiv.Perm (Fin s)) where
  toFun v := WithLp.toLp 2 (fun φ => v (a⁻¹ * φ))
  map_add' v w := by ext φ; rfl
  map_smul' c v := by ext φ; rfl

lemma translate_apply (a : Equiv.Perm (Fin s)) (v : Hil (Equiv.Perm (Fin s)))
    (φ : Equiv.Perm (Fin s)) : translate a v φ = v (a⁻¹ * φ) := rfl



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


lemma frame_adjoint (s r : ℕ) : ContinuousLinearMap.adjoint (frame s r) = frame s r := by
  have hk (u v : Hil (Equiv.Perm (Fin s))) :
      ketBra u v = InnerProductSpace.rankOne ℂ u v := by
    ext x
    rfl
  simp only [frame, hk, map_sum, InnerProductSpace.adjoint_rankOne]

lemma frame_symmetric (r : ℕ) (v w : Hil (Equiv.Perm (Fin s))) :
    inner ℂ (frame s r v) w = inner ℂ v (frame s r w) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, frame_adjoint]





/-- The unprojected synthesis map on databases with exactly r records. -/
noncomputable def synthesis (s r : ℕ) :
    Hil (InjDb s) →L[ℂ] Hil (Equiv.Perm (Fin s)) :=
  ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I.size = r),
    ketBra (completion I) (ket I)

lemma synthesis_apply (r : ℕ) (v : Hil (InjDb s)) :
    synthesis s r v = ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I.size = r),
      v I • completion I := by
  simp only [synthesis, ContinuousLinearMap.sum_apply, ketBra_apply, inner_ket]





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

-- Solutions.YoungPieriComplete
section

-- MODULE FiniteCommutingInvariants
section

namespace WeldedPath.FiniteCommutingInvariants

noncomputable section
open Classical

variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fixedSubrepresentation (ρ : Representation ℂ G V) (τ : Representation ℂ H V)
    (hcomm : ∀ g h, Commute (ρ g) (τ h)) : Subrepresentation ρ where
  toSubmodule := τ.invariants
  apply_mem_toSubmodule := by
    intro g v hv h
    have he := LinearMap.congr_fun (hcomm g h).eq v
    change ρ g (τ h v)=τ h (ρ g v) at he
    rw [← he,hv h]

def restrictedMap (ρ : Representation ℂ G V) (τ : Representation ℂ H V)
    (hcomm : ∀ g h, Commute (ρ g) (τ h)) (σ : Representation ℂ G W)
    (F : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap (fixedSubrepresentation ρ τ hcomm).toRepresentation σ where
  toLinearMap := F.toLinearMap.comp (fixedSubrepresentation ρ τ hcomm).toSubmodule.subtype
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro v
    change F (ρ g v.1)=σ g (F v.1)
    exact LinearMap.congr_fun (F.isIntertwining' g) v.1

theorem surjective_on_invariants [Fintype H]
    (τ : Representation ℂ H V) (F : V →ₗ[ℂ] W) (hF : Function.Surjective F)
    (hinv : ∀ h v, F (τ h v)=F v) :
    ∀ w, ∃ v : V, v ∈ τ.invariants ∧ F v=w := by
  let T : Representation.IntertwiningMap τ (Representation.trivial ℂ H W) :=
    { toLinearMap := F
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro v
        exact hinv h v }
  obtain ⟨J,hJ⟩ := FiniteRepresentationBranching.exists_equivariant_section T hF
  intro w
  refine ⟨J w,?_,hJ w⟩
  intro h
  have he := LinearMap.congr_fun (J.isIntertwining' h) w
  change τ h (J.toLinearMap w)=J.toLinearMap w
  simpa only [LinearMap.comp_apply,Representation.trivial_apply] using he.symm

theorem restrictedMap_surjective [Fintype H]
    (ρ : Representation ℂ G V) (τ : Representation ℂ H V)
    (hcomm : ∀ g h, Commute (ρ g) (τ h)) (σ : Representation ℂ G W)
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Surjective F)
    (hinv : ∀ h v, F (τ h v)=F v) :
    Function.Surjective (restrictedMap ρ τ hcomm σ F) := by
  intro w
  obtain ⟨v,hv,hvw⟩ := surjective_on_invariants τ F.toLinearMap hF hinv w
  exact ⟨⟨v,hv⟩,hvw⟩

end
end WeldedPath.FiniteCommutingInvariants
end

-- MODULE YoungPieriMaps
section

namespace WeldedPath.SpechtPieri

noncomputable section
open Classical YoungCounts OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid

def extendEmbedding {α β : Type*} [Fintype α] [Fintype β] (f g : α ↪ β) : Equiv.Perm β :=
  Equiv.extendSubtype (f.toEquivRange.symm.trans g.toEquivRange)

lemma extendEmbedding_apply {α β : Type*} [Fintype α] [Fintype β] (f g : α ↪ β) (a : α) :
    extendEmbedding f g (f a)=g a := by
  unfold extendEmbedding
  rw [Equiv.extendSubtype_apply_of_mem _ _ ⟨a,rfl⟩]
  change g (f.toEquivRange.symm (f.toEquivRange a))=g a
  rw [Equiv.symm_apply_apply]

lemma viaEmbedding_commute_fixing {α β : Type*} [Finite α] [Finite β]
    (f : α ↪ β) (k : Equiv.Perm α) (g : Equiv.Perm β)
    (hg : ∀ a, g (f a)=f a) : Commute (k.viaEmbedding f) g := by
  apply Equiv.ext
  intro x
  change k.viaEmbedding f (g x)=g (k.viaEmbedding f x)
  by_cases hx : x ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hx
    rw [hg,Equiv.Perm.viaEmbedding_apply,hg]
  · have hgx : g x ∉ Set.range f := by
      rintro ⟨a,ha⟩
      have he : f a=x := g.injective ((hg a).trans ha)
      exact hx ⟨a,he⟩
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem k f x hx,
      Equiv.Perm.viaEmbedding_apply_of_notMem k f (g x) hgx]

def prefixSet {j s : ℕ} (h : j ≤ s) : Finset (Fin s) :=
  Finset.univ.map (Fin.castLEEmb h)

def retainedRep {j s : ℕ} (μ : DiagramCounting.Shape s) (h : j ≤ s) :
    Representation ℂ (Equiv.Perm (Fin j)) (spechtSub μ.1).toSubmodule :=
  (SpechtActual.rep μ).comp (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h))

def discardedRep {j s : ℕ} (μ : DiagramCounting.Shape s) (h : j ≤ s) :
    Representation ℂ (CompletionFrame.fixing (prefixSet h)) (spechtSub μ.1).toSubmodule :=
  (SpechtActual.rep μ).comp (CompletionFrame.fixing (prefixSet h)).subtype

lemma retained_discarded_commute {j s : ℕ} (μ : DiagramCounting.Shape s) (h : j ≤ s)
    (g : Equiv.Perm (Fin j)) (k : CompletionFrame.fixing (prefixSet h)) :
    Commute (retainedRep μ h g) (discardedRep μ h k) := by
  exact (viaEmbedding_commute_fixing (Fin.castLEEmb h) g k.1 (fun i =>
    k.2 _ (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩))).map (SpechtActual.rep μ)

def pieriFixedSubrepresentation {j s : ℕ} (μ : DiagramCounting.Shape s) (h : j ≤ s) :
    Subrepresentation (retainedRep μ h) :=
  FiniteCommutingInvariants.fixedSubrepresentation (retainedRep μ h) (discardedRep μ h)
    (retained_discarded_commute μ h)

def pieriTableau {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) : Fin s ≃ μ.1.cells :=
  (extendEmbedding (Fin.castLEEmb h)
    ((SpechtActual.labels ν).symm.toEmbedding.trans
      ((cellInclusion hsub).trans (SpechtActual.labels μ).toEmbedding))).trans
    (SpechtActual.labels μ).symm

lemma pieriTableau_apply {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) (i : Fin j) :
    pieriTableau ν μ h hsub (Fin.castLEEmb h i)=cellInclusion hsub ((SpechtActual.labels ν).symm i) := by
  unfold pieriTableau
  rw [Equiv.trans_apply,extendEmbedding_apply]
  exact (SpechtActual.labels μ).symm_apply_apply _

def pieriRelabel {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) : Equiv.Perm μ.1.cells :=
  (SpechtActual.labels μ).trans (pieriTableau ν μ h hsub)

lemma pieri_conjugacy {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) (g : Equiv.Perm (Fin s)) :
    pieriRelabel ν μ h hsub * (SpechtActual.labels μ).symm.permCongrHom g =
      (pieriTableau ν μ h hsub).permCongrHom g * pieriRelabel ν μ h hsub := by
  apply Equiv.ext
  intro x
  simp [pieriRelabel,Equiv.Perm.mul_apply,Equiv.permCongrHom_coe,Equiv.permCongr_apply]

lemma pieri_inclusion {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) (g : Equiv.Perm (Fin s)) (k : Equiv.Perm (Fin j))
    (hg : ∀ i, g (Fin.castLEEmb h i)=Fin.castLEEmb h (k i)) (x : ν.1.cells) :
    (pieriTableau ν μ h hsub).permCongrHom g (cellInclusion hsub x)=
      cellInclusion hsub ((SpechtActual.labels ν).symm.permCongrHom k x) := by
  have he : cellInclusion hsub x=pieriTableau ν μ h hsub (Fin.castLEEmb h (SpechtActual.labels ν x)) := by
    rw [pieriTableau_apply,Equiv.symm_apply_apply]
  rw [he]
  change pieriTableau ν μ h hsub
    (g ((pieriTableau ν μ h hsub).symm
      (pieriTableau ν μ h hsub (Fin.castLEEmb h (SpechtActual.labels ν x))))) = _
  rw [Equiv.symm_apply_apply,hg,pieriTableau_apply]
  rfl

def rawPieriMap {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) :
    (spechtSub μ.1).toSubmodule →ₗ[ℂ] (spechtSub ν.1).toSubmodule :=
  (restrictionMap hsub).comp (spechtRep μ.1 (pieriRelabel ν μ h hsub))

lemma rawPieriMap_action {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) (g : Equiv.Perm (Fin s)) (k : Equiv.Perm (Fin j))
    (hg : ∀ i, g (Fin.castLEEmb h i)=Fin.castLEEmb h (k i))
    (v : (spechtSub μ.1).toSubmodule) :
    rawPieriMap ν μ h hsub (SpechtActual.rep μ g v)=
      SpechtActual.rep ν k (rawPieriMap ν μ h hsub v) := by
  change restrictionMap hsub (spechtRep μ.1 (pieriRelabel ν μ h hsub)
      (spechtRep μ.1 ((SpechtActual.labels μ).symm.permCongrHom g) v)) =
    spechtRep ν.1 ((SpechtActual.labels ν).symm.permCongrHom k)
      (restrictionMap hsub (spechtRep μ.1 (pieriRelabel ν μ h hsub) v))
  rw [← Module.End.mul_apply,← map_mul,pieri_conjugacy,map_mul,Module.End.mul_apply]
  exact restrictionMap_equivariant hsub _ _ (pieri_inclusion ν μ h hsub g k hg) _

def pieriMap {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) :
    Representation.IntertwiningMap (retainedRep μ h) (SpechtActual.rep ν) where
  toLinearMap := rawPieriMap ν μ h hsub
  isIntertwining' := by
    intro k
    apply LinearMap.ext
    intro v
    exact rawPieriMap_action ν μ h hsub _ k (Equiv.Perm.viaEmbedding_apply k (Fin.castLEEmb h)) v

theorem pieriMap_surjective {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hs : HorizontalStrip ν.1 μ.1) : Function.Surjective (pieriMap ν μ h hs.1) := by
  intro w
  obtain ⟨v,hv⟩ := restrictionMap_surjective hs w
  refine ⟨spechtRep μ.1 (pieriRelabel ν μ h hs.1)⁻¹ v,?_⟩
  change restrictionMap hs.1 (spechtRep μ.1 (pieriRelabel ν μ h hs.1)
    (spechtRep μ.1 (pieriRelabel ν μ h hs.1)⁻¹ v))=w
  rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
  exact hv

lemma pieriMap_discarded_invariant {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) (k : CompletionFrame.fixing (prefixSet h))
    (v : (spechtSub μ.1).toSubmodule) :
    pieriMap ν μ h hsub (discardedRep μ h k v)=pieriMap ν μ h hsub v := by
  change rawPieriMap ν μ h hsub (SpechtActual.rep μ k.1 v)=rawPieriMap ν μ h hsub v
  have he := rawPieriMap_action ν μ h hsub k.1 1 (fun i =>
    k.2 _ (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)) v
  simpa only [map_one,Module.End.one_apply] using he

def fixedPieriMap {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hsub : ν.1 ≤ μ.1) :
    Representation.IntertwiningMap (pieriFixedSubrepresentation μ h).toRepresentation (SpechtActual.rep ν) :=
  FiniteCommutingInvariants.restrictedMap (retainedRep μ h) (discardedRep μ h)
    (retained_discarded_commute μ h) (SpechtActual.rep ν) (pieriMap ν μ h hsub)

theorem fixedPieriMap_surjective {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hs : HorizontalStrip ν.1 μ.1) :
    Function.Surjective (fixedPieriMap ν μ h hs.1) :=
  FiniteCommutingInvariants.restrictedMap_surjective (retainedRep μ h) (discardedRep μ h)
    (retained_discarded_commute μ h) (SpechtActual.rep ν) (pieriMap ν μ h hs.1)
    (pieriMap_surjective ν μ h hs) (pieriMap_discarded_invariant ν μ h hs.1)

end
end WeldedPath.SpechtPieri
end

-- MODULE YoungPieriDecomposition
section

namespace WeldedPath.SpechtPieri

noncomputable section
open Classical YoungCounts YoungBranching OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open scoped BigOperators

abbrev PieriShape {s : ℕ} (μ : DiagramCounting.Shape s) (j : ℕ) :=
  {ν : DiagramCounting.Shape j // HorizontalStrip ν.1 μ.1}

theorem stripDimension_eq_specht_sum {s : ℕ} (μ : DiagramCounting.Shape s) (j : ℕ) :
    stripDimension j μ.1 = ∑ ν : PieriShape μ j, Module.finrank ℂ (spechtSub ν.1.1).toSubmodule := by
  calc
    _ = ∑ ν : DiagramCounting.Shape j,
        if HorizontalStrip ν.1 μ.1 then Module.finrank ℂ (spechtSub ν.1).toSubmodule else 0 := by
      symm
      apply Finset.sum_bij (fun ν _ => ν.1)
      · intro ν hν
        exact mem_level.mpr ν.2
      · intro ν hν η hη he
        exact Subtype.ext he
      · intro ν hν
        exact ⟨⟨ν,mem_level.mp hν⟩,Finset.mem_univ _,rfl⟩
      · intro ν hν
        rw [← YoungSpechtDimension.standardCount_eq_specht_finrank,
          ← tableauCount_eq_standardCount]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

theorem pieriFixed_finrank {j s : ℕ} (μ : DiagramCounting.Shape s) (h : j ≤ s) :
    Module.finrank ℂ (pieriFixedSubrepresentation μ h).toSubmodule =
      ∑ ν : PieriShape μ j, Module.finrank ℂ (spechtSub ν.1.1).toSubmodule := by
  have hc : (prefixSet h).card = (CompletionFrame.prefixComplement (Nat.sub_le s j)).card := by
    simp only [prefixSet,Finset.card_map,Finset.card_univ,Fintype.card_fin,
      CompletionFrame.prefixComplement_card,Nat.sub_sub_self h]
  have he := CompletionFrame.finrank_fixing_eq_of_card (SpechtActual.rep μ)
    (prefixSet h) (CompletionFrame.prefixComplement (Nat.sub_le s j)) hc
  rw [CompletionFrame.prefix_invariants] at he
  change Module.finrank ℂ (discardedRep μ h).invariants =
    Module.finrank ℂ (initialRep μ (Nat.sub_le s j)).invariants at he
  rw [← initialFixed_eq_invariants,initial_fixed_pieri_dimension,Nat.sub_sub_self h] at he
  exact he.trans (stripDimension_eq_specht_sum μ j)

theorem fixedPieriMap_ne_zero {j s : ℕ} (ν : DiagramCounting.Shape j) (μ : DiagramCounting.Shape s)
    (h : j ≤ s) (hs : HorizontalStrip ν.1 μ.1) : fixedPieriMap ν μ h hs.1 ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := fixedPieriMap_surjective ν μ h hs ⟨polytabloid ν.1,polytabloid_mem_specht ν.1⟩
  rw [hz] at hv
  exact polytabloid_ne_zero ν.1 (congrArg Subtype.val hv).symm

/-- The full horizontal-strip Pieri decomposition on the actual subgroup-fixed
canonical Specht module, with the retained-coordinate symmetric-group action. -/
theorem pieri_equiv {j s : ℕ} (μ : DiagramCounting.Shape s) (h : j ≤ s) :
    ∃ E : (pieriFixedSubrepresentation μ h).toSubmodule ≃ₗ[ℂ]
        (∀ ν : PieriShape μ j, (spechtSub ν.1.1).toSubmodule),
      (∀ v ν, E v ν=fixedPieriMap ν.1 μ h ν.2.1 v) ∧
      (∀ g v ν, E ((pieriFixedSubrepresentation μ h).toRepresentation g v) ν =
        SpechtActual.rep ν.1 g (E v ν)) := by
  let F (ν : PieriShape μ j) := fixedPieriMap ν.1 μ h ν.2.1
  have hne (ν η : PieriShape μ j) (hne : ν≠η) :
      ¬ Nonempty (Representation.Equiv (SpechtActual.rep ν.1) (SpechtActual.rep η.1)) := by
    rintro ⟨E⟩
    exact hne (Subtype.ext (SpechtActual.rep_equiv_shape_eq ν.1 η.1 E))
  obtain ⟨E,hE⟩ := FiniteRepresentationBranching.exists_equiv_of_dim_sum
    (pieriFixedSubrepresentation μ h).toRepresentation (fun ν : PieriShape μ j => SpechtActual.rep ν.1)
    hne F (fun ν => fixedPieriMap_ne_zero ν.1 μ h ν.2) (pieriFixed_finrank μ h)
  refine ⟨E,hE,?_⟩
  intro g v ν
  rw [hE,hE]
  exact LinearMap.congr_fun ((F ν).isIntertwining' g) v

end
end WeldedPath.SpechtPieri
end


end

-- Solutions.WeldedPathOrderedMatching
section

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical InjDb CompletionFrame

abbrev OrderedInjection (j s : ℕ) := Fin j ↪ Fin s
abbrev MatchingLevel (s j : ℕ) := {I : InjDb s // I.size=j}

def database {j s : ℕ} (u v : OrderedInjection j s) : InjDb s :=
  restrict (SpechtPieri.extendEmbedding u v) (Finset.univ.map u)

theorem database_record_iff {j s : ℕ} (u v : OrderedInjection j s) (x y : Fin s) :
    database u v x=some y ↔ ∃ i, u i=x ∧ v i=y := by
  rw [database,restrict_apply]
  by_cases hx : x ∈ Finset.univ.map u
  · rw [if_pos hx]
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
    rw [SpechtPieri.extendEmbedding_apply]
    constructor
    · intro he
      exact ⟨i,rfl,Option.some.inj he⟩
    · rintro ⟨k,hk,hv⟩
      have hki : k=i := u.injective hk
      subst k
      exact congrArg some hv
  · rw [if_neg hx]
    constructor
    · intro he
      cases he
    · rintro ⟨i,hi,hv⟩
      exact (hx (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,hi⟩)).elim

@[simp] theorem database_record {j s : ℕ} (u v : OrderedInjection j s) (i : Fin j) :
    database u v (u i)=some (v i) :=
  (database_record_iff u v _ _).mpr ⟨i,rfl,rfl⟩

@[simp] theorem database_size {j s : ℕ} (u v : OrderedInjection j s) :
    (database u v).size=j := by
  rw [database,restrict_size]
  simp


def matching {j s : ℕ} (u v : OrderedInjection j s) : MatchingLevel s j :=
  ⟨database u v,database_size u v⟩

theorem database_ext {j s : ℕ} (u v : OrderedInjection j s) (I : InjDb s)
    (hI : ∀ x y, I x=some y ↔ ∃ i, u i=x ∧ v i=y) : database u v=I := by
  apply PEquiv.ext
  intro x
  apply Option.ext
  intro y
  simp only [Option.mem_def,database_record_iff,hI]

theorem matching_surjective {j s : ℕ} :
    Function.Surjective (fun p : OrderedInjection j s × OrderedInjection j s => matching p.1 p.2) := by
  intro I
  have hcard : Fintype.card (domain I.1)=j := by rw [Fintype.card_coe,card_domain,I.2]
  let e : Fin j ≃ domain I.1 := (Fintype.equivFinOfCardEq hcard).symm
  let u : OrderedInjection j s := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hu (i : Fin j) : (I.1 (u i)).isSome := (mem_domain I.1 (u i)).mp (e i).2
  let value : Fin j → Fin s := fun i => (I.1 (u i)).get (hu i)
  have hvalue (i : Fin j) : I.1 (u i)=some (value i) := (Option.some_get (hu i)).symm
  have hv : Function.Injective value := by
    intro i k hik
    apply u.injective
    have hi := (I.1.inv (u i) (value i)).mpr (hvalue i)
    have hk := (I.1.inv (u k) (value k)).mpr (hvalue k)
    rw [hik] at hi
    exact Option.some.inj (hi.symm.trans hk)
  let v : OrderedInjection j s := ⟨value,hv⟩
  refine ⟨(u,v),?_⟩
  apply Subtype.ext
  apply database_ext
  intro x y
  constructor
  · intro hxy
    have hx : x ∈ domain I.1 := (mem_domain I.1 x).mpr (by simp only [hxy,Option.isSome_some])
    let i := e.symm ⟨x,hx⟩
    have hui : u i=x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
    have hvi : v i=y := by
      have hh := hvalue i
      rw [hui,hxy] at hh
      exact (Option.some.inj hh).symm
    exact ⟨i,hui,hvi⟩
  · rintro ⟨i,rfl,rfl⟩
    exact hvalue i

theorem database_eq_iff_reindex {j s : ℕ} (u v u' v' : OrderedInjection j s) :
    database u v=database u' v' ↔
      ∃ σ : Equiv.Perm (Fin j), (∀ i, u' (σ i)=u i) ∧ (∀ i, v' (σ i)=v i) := by
  constructor
  · intro he
    have hex (i : Fin j) : ∃ k, u' k=u i ∧ v' k=v i := by
      apply (database_record_iff u' v' _ _).mp
      rw [← he]
      exact database_record u v i
    let f : Fin j → Fin j := fun i => (hex i).choose
    have hf0 (i : Fin j) : u' (f i)=u i ∧ v' (f i)=v i := (hex i).choose_spec
    have hf : Function.Injective f := by
      intro i k hik
      apply u.injective
      exact (hf0 i).1.symm.trans ((congrArg u' hik).trans (hf0 k).1)
    let σ : Equiv.Perm (Fin j) := Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,rfl⟩)
    exact ⟨σ,fun i => (hf0 i).1,fun i => (hf0 i).2⟩
  · rintro ⟨σ,hu,hv⟩
    apply database_ext
    intro x y
    rw [database_record_iff]
    constructor
    · rintro ⟨k,hkx,hky⟩
      refine ⟨σ.symm k,?_,?_⟩
      · rw [← hu,Equiv.apply_symm_apply]
        exact hkx
      · rw [← hv,Equiv.apply_symm_apply]
        exact hky
    · rintro ⟨i,hix,hiy⟩
      exact ⟨σ i,(hu i).trans hix,(hv i).trans hiy⟩

def reindex {j s : ℕ} (u : OrderedInjection j s) (σ : Equiv.Perm (Fin j)) :
    OrderedInjection j s := σ.toEmbedding.trans u


@[simp] theorem database_reindex {j s : ℕ} (u v : OrderedInjection j s) (σ : Equiv.Perm (Fin j)) :
    database (reindex u σ) (reindex v σ)=database u v :=
  (database_eq_iff_reindex _ _ _ _).mpr ⟨σ,fun _ => rfl,fun _ => rfl⟩

/-- Functions on ordered pairs that descend through simultaneous reindexing. -/
def diagonalFixed (j s : ℕ) :
    Submodule ℂ ((OrderedInjection j s × OrderedInjection j s) → ℂ) where
  carrier := {f | ∀ u v σ, f (reindex u σ,reindex v σ)=f (u,v)}
  zero_mem' := by intro u v σ; rfl
  add_mem' := by intro f g hf hg u v σ; exact congrArg₂ (·+·) (hf u v σ) (hg u v σ)
  smul_mem' := by intro c f hf u v σ; exact congrArg (c * ·) (hf u v σ)

def pullback (j s : ℕ) :
    (MatchingLevel s j → ℂ) →ₗ[ℂ] diagonalFixed j s where
  toFun f := ⟨fun p => f (matching p.1 p.2),by
    intro u v σ
    apply congrArg f
    exact Subtype.ext (database_reindex u v σ)⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl


theorem pullback_injective (j s : ℕ) : Function.Injective (pullback j s) := by
  intro f g he
  funext I
  obtain ⟨⟨u,v⟩,rfl⟩ := matching_surjective I
  exact congrFun (congrArg Subtype.val he) (u,v)

theorem diagonalFixed_fiber {j s : ℕ} (f : diagonalFixed j s)
    (u v u' v' : OrderedInjection j s) (he : database u v=database u' v') :
    f.1 (u,v)=f.1 (u',v') := by
  obtain ⟨σ,hu,hv⟩ := (database_eq_iff_reindex u v u' v').mp he
  have heu : reindex u' σ=u := by apply Function.Embedding.ext; intro i; exact hu i
  have hev : reindex v' σ=v := by apply Function.Embedding.ext; intro i; exact hv i
  simpa only [heu,hev] using f.2 u' v' σ

theorem pullback_surjective (j s : ℕ) : Function.Surjective (pullback j s) := by
  intro f
  let choose (I : MatchingLevel s j) := (matching_surjective I).choose
  have hchoose (I : MatchingLevel s j) : matching (choose I).1 (choose I).2=I :=
    (matching_surjective I).choose_spec
  refine ⟨fun I => f.1 (choose I),?_⟩
  apply Subtype.ext
  funext p
  exact diagonalFixed_fiber f _ _ _ _ (congrArg Subtype.val (hchoose (matching p.1 p.2)))

/-- Actual size-j databases are precisely the diagonal Sj quotient of two
ordered injection spaces. This is a linear equivalence, with no spectral
decomposition or counting assumption. -/
def matchingEquiv (j s : ℕ) : (MatchingLevel s j → ℂ) ≃ₗ[ℂ] diagonalFixed j s :=
  LinearEquiv.ofBijective (pullback j s) ⟨pullback_injective j s,pullback_surjective j s⟩


def permute {j s : ℕ} (π : Equiv.Perm (Fin s)) (u : OrderedInjection j s) :
    OrderedInjection j s := u.trans π.toEmbedding

@[simp] theorem permute_apply {j s : ℕ} (π : Equiv.Perm (Fin s))
    (u : OrderedInjection j s) (i : Fin j) : permute π u i=π (u i) := rfl



end
end WeldedPath.OrderedMatching

end

-- Solutions.WeldedPathOrderedCosets
section

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical CompletionFrame

variable {j s : ℕ}

def fromPerm (h : j ≤ s) (π : Equiv.Perm (Fin s)) : OrderedInjection j s :=
  permute π (Fin.castLEEmb h)


theorem fromPerm_surjective (h : j ≤ s) : Function.Surjective (fromPerm h) := by
  intro u
  refine ⟨SpechtPieri.extendEmbedding (Fin.castLEEmb h) u,?_⟩
  apply Function.Embedding.ext
  intro i
  exact SpechtPieri.extendEmbedding_apply _ _ i

theorem fromPerm_mul_fixing (h : j ≤ s) (π : Equiv.Perm (Fin s))
    (τ : fixing (SpechtPieri.prefixSet h)) : fromPerm h (π*τ.1)=fromPerm h π := by
  apply Function.Embedding.ext
  intro i
  change π (τ.1 (Fin.castLE h i))=π (Fin.castLE h i)
  exact congrArg π (τ.2 _ (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩))

theorem fromPerm_eq_iff (h : j ≤ s) (π ρ : Equiv.Perm (Fin s)) :
    fromPerm h π=fromPerm h ρ ↔ ρ⁻¹*π ∈ fixing (SpechtPieri.prefixSet h) := by
  constructor
  · intro he x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
    have hh := congrArg (fun u : OrderedInjection j s => u i) he
    change ρ.symm (π (Fin.castLE h i))=Fin.castLE h i
    change π (Fin.castLE h i)=ρ (Fin.castLE h i) at hh
    rw [hh,Equiv.symm_apply_apply]
  · intro he
    apply Function.Embedding.ext
    intro i
    have hh := he _ (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    change ρ.symm (π (Fin.castLE h i))=Fin.castLE h i at hh
    exact ρ.symm.injective (hh.trans (ρ.symm_apply_apply _).symm)

def rightFixed (h : j ≤ s) : Submodule ℂ (Equiv.Perm (Fin s) → ℂ) where
  carrier := {f | ∀ π (τ : fixing (SpechtPieri.prefixSet h)), f (π*τ.1)=f π}
  zero_mem' := by intro π τ; rfl
  add_mem' := by intro f g hf hg π τ; exact congrArg₂ (·+·) (hf π τ) (hg π τ)
  smul_mem' := by intro c f hf π τ; exact congrArg (c * ·) (hf π τ)

def cosetPullback (h : j ≤ s) : (OrderedInjection j s → ℂ) →ₗ[ℂ] rightFixed h where
  toFun f := ⟨fun π => f (fromPerm h π),fun π τ => congrArg f (fromPerm_mul_fixing h π τ)⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl


theorem cosetPullback_injective (h : j ≤ s) : Function.Injective (cosetPullback h) := by
  intro f g he
  funext u
  obtain ⟨π,rfl⟩ := fromPerm_surjective h u
  exact congrFun (congrArg Subtype.val he) π

theorem rightFixed_fiber (h : j ≤ s) (f : rightFixed h) (π ρ : Equiv.Perm (Fin s))
    (he : fromPerm h π=fromPerm h ρ) : f.1 π=f.1 ρ := by
  have hh := f.2 ρ ⟨ρ⁻¹*π,(fromPerm_eq_iff h π ρ).mp he⟩
  simpa only [mul_inv_cancel_left] using hh

theorem cosetPullback_surjective (h : j ≤ s) : Function.Surjective (cosetPullback h) := by
  intro f
  let choose (u : OrderedInjection j s) := (fromPerm_surjective h u).choose
  have hchoose (u : OrderedInjection j s) : fromPerm h (choose u)=u :=
    (fromPerm_surjective h u).choose_spec
  refine ⟨fun u => f.1 (choose u),?_⟩
  apply Subtype.ext
  funext π
  exact rightFixed_fiber h f _ _ (hchoose (fromPerm h π))

def cosetEquiv (h : j ≤ s) : (OrderedInjection j s → ℂ) ≃ₗ[ℂ] rightFixed h :=
  LinearEquiv.ofBijective (cosetPullback h) ⟨cosetPullback_injective h,cosetPullback_surjective h⟩



theorem fromPerm_retained (h : j ≤ s) (π : Equiv.Perm (Fin s)) (σ : Equiv.Perm (Fin j)) :
    fromPerm h (π*(Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ))=
      reindex (fromPerm h π) σ := by
  apply Function.Embedding.ext
  intro i
  change π (Equiv.Perm.viaEmbedding σ (Fin.castLEEmb h) (Fin.castLE h i))=
    π (Fin.castLE h (σ i))
  exact congrArg π (Equiv.Perm.viaEmbedding_apply σ (Fin.castLEEmb h) i)

end
end WeldedPath.OrderedMatching

end

-- Solutions.FiniteProjectedHom
section

namespace WeldedPath.FiniteProjectedHom

noncomputable section
open Classical
open scoped BigOperators

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def throughProjection (P : V →ₗ[ℂ] V) : Submodule ℂ (V →ₗ[ℂ] W) where
  carrier := {F | F.comp P=F}
  zero_mem' := rfl
  add_mem' := by
    intro F G hF hG
    change (F+G).comp P=F+G
    rw [LinearMap.add_comp]
    exact congrArg₂ (·+·) hF hG
  smul_mem' := by
    intro c F hF
    change (c • F).comp P=c • F
    rw [LinearMap.smul_comp]
    exact congrArg (c • ·) hF


def projectedHomEquiv (S : Submodule ℂ V) (P : V →ₗ[ℂ] V)
    (hP : LinearMap.IsProj S P) :
    throughProjection (W := W) P ≃ₗ[ℂ] (S →ₗ[ℂ] W) where
  toFun F := F.1.comp S.subtype
  invFun F := ⟨F.comp (P.codRestrict S hP.1),by
    ext v
    apply congrArg F
    apply Subtype.ext
    exact hP.2 _ (hP.1 v)⟩
  left_inv F := by
    apply Subtype.ext
    exact F.2
  right_inv F := by
    ext v
    change F ⟨P v.1,hP.1 v.1⟩=F v
    congr 1
    exact Subtype.ext (hP.2 v.1 v.2)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl



section Group
variable {H : Type*} [Group H] [Fintype H]

def rightInvariantHom (τ : Representation ℂ H V) : Submodule ℂ (V →ₗ[ℂ] W) where
  carrier := {F | ∀ h, F.comp (τ h)=F}
  zero_mem' := by intro h; rfl
  add_mem' := by
    intro F G hF hG h
    rw [LinearMap.add_comp]
    exact congrArg₂ (·+·) (hF h) (hG h)
  smul_mem' := by
    intro c F hF h
    rw [LinearMap.smul_comp]
    exact congrArg (c • ·) (hF h)

variable [Invertible (Fintype.card H : ℂ)]

theorem averageMap_comp (τ : Representation ℂ H V) (h : H) :
    τ.averageMap.comp (τ h)=τ.averageMap := by
  change τ.asAlgebraHom (GroupAlgebra.average ℂ H)*τ h=
    τ.asAlgebraHom (GroupAlgebra.average ℂ H)
  rw [← Representation.asAlgebraHom_single_one,← map_mul,GroupAlgebra.mul_average_right]

theorem invariant_comp_averageMap (τ : Representation ℂ H V)
    (F : V →ₗ[ℂ] W) (hF : ∀ h, F.comp (τ h)=F) : F.comp τ.averageMap=F := by
  have hform : τ.averageMap=(⅟(Fintype.card H : ℂ)) • ∑ h : H, τ h := by
    simp [Representation.averageMap,GroupAlgebra.average,map_sum]
  rw [hform]
  ext v
  have hf (h : H) : F (τ h v)=F v := LinearMap.congr_fun (hF h) v
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    map_smul,map_sum,hf,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,invOf_mul_self,one_smul]

theorem rightInvariantHom_eq (τ : Representation ℂ H V) :
    rightInvariantHom (W := W) τ=throughProjection τ.averageMap := by
  ext F
  constructor
  · exact invariant_comp_averageMap τ F
  · intro hF h
    change F.comp τ.averageMap=F at hF
    calc
      F.comp (τ h)=(F.comp τ.averageMap).comp (τ h) := by rw [hF]
      _ = F.comp (τ.averageMap.comp (τ h)) := LinearMap.comp_assoc _ _ _
      _ = F.comp τ.averageMap := by rw [averageMap_comp]
      _ = F := hF

def invariantHomEquiv (τ : Representation ℂ H V) :
    rightInvariantHom (W := W) τ ≃ₗ[ℂ] (τ.invariants →ₗ[ℂ] W) :=
  (LinearEquiv.ofEq _ _ (rightInvariantHom_eq τ)).trans
    (projectedHomEquiv τ.invariants τ.averageMap τ.isProj_averageMap)


end Group
end
end WeldedPath.FiniteProjectedHom

end

-- Solutions.FiniteGroupFourierEquiv
section

namespace WeldedPath.FiniteFourier

noncomputable section
open Classical OAI.PartialPermutation
open scoped BigOperators

variable (G : Type*) [Group G] [Fintype G]

abbrev Family := (c : IrreducibleIndex G) → Module.End ℂ (irreducibleSpace c)

def transform : (G → ℂ) →ₗ[ℂ] Family G where
  toFun a c := complexFourier (irreducibleRep c) a
  map_add' a b := by
    funext c
    simp only [complexFourier,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' z a := by
    funext c
    simp only [complexFourier,Pi.smul_apply,smul_eq_mul,smul_smul,Finset.smul_sum,RingHom.id_apply]

def inverseFormula (A : Family G) (h : G) : ℂ :=
  ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ) / Fintype.card G *
    LinearMap.trace ℂ (irreducibleSpace c) (irreducibleRep c h⁻¹ * A c)

lemma trace_kernel (g h : G) :
    (∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ) / Fintype.card G *
      LinearMap.trace ℂ (irreducibleSpace c) (irreducibleRep c (h⁻¹*g))) =
      if g=h then 1 else 0 := by
  have he := sum_regular_character_kernels (g⁻¹*h)
  simpa only [centralCharacterKernel,Representation.character,mul_inv_rev,inv_inv,
    inv_mul_eq_one,irreducibleDegree] using he

theorem inverse_transform (a : G → ℂ) (h : G) : inverseFormula G (transform G a) h = a h := by
  unfold inverseFormula transform
  simp only [LinearMap.coe_mk,AddHom.coe_mk,complexFourier,Finset.mul_sum,
    mul_smul_comm,map_sum,map_smul,← map_mul,smul_eq_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ g : G, a g * (∑ c : IrreducibleIndex G,
        (irreducibleDegree c : ℂ) / Fintype.card G *
          LinearMap.trace ℂ (irreducibleSpace c) (irreducibleRep c (h⁻¹*g))) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = ∑ g : G, a g * (if g=h then 1 else 0) := by simp_rw [trace_kernel]
    _ = a h := by simp

theorem transform_injective : Function.Injective (transform G) := by
  intro a b he
  funext h
  rw [← inverse_transform G a h,← inverse_transform G b h,he]






section Covariance
variable {G} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

theorem fourier_left_translate (a : G → ℂ) (h : G) :
    complexFourier ρ (fun g => a (h⁻¹*g)) = ρ h * complexFourier ρ a := by
  simp only [complexFourier,Finset.mul_sum,mul_smul_comm,← map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
  intro g
  simp [mul_assoc]

theorem fourier_right_translate (a : G → ℂ) (h : G) :
    complexFourier ρ (fun g => a (g*h)) = complexFourier ρ a * ρ h⁻¹ := by
  simp only [complexFourier,Finset.sum_mul,smul_mul_assoc,← map_mul]
  apply Fintype.sum_equiv (Equiv.mulRight h)
  intro g
  simp only [Equiv.coe_mulRight,mul_assoc,mul_inv_cancel,mul_one]


theorem fourier_equiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G W) (e : Representation.Equiv ρ τ) (a : G → ℂ) (v : V) :
    e (complexFourier ρ a v) = complexFourier τ a (e v) := by
  simp only [complexFourier,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact LinearMap.congr_fun (e.isIntertwining' g) v

end Covariance

open OAI.PartialPermutation.YoungTabloid

abbrev SpechtFamily (n : ℕ) :=
  (μ : DiagramCounting.Shape n) → Module.End ℂ (spechtSub μ.1).toSubmodule

def spechtTransform (n : ℕ) : (Equiv.Perm (Fin n) → ℂ) →ₗ[ℂ] SpechtFamily n where
  toFun a μ := complexFourier (SpechtActual.rep μ) a
  map_add' a b := by
    funext μ
    simp only [complexFourier,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' z a := by
    funext μ
    simp only [complexFourier,Pi.smul_apply,smul_eq_mul,smul_smul,Finset.smul_sum,RingHom.id_apply]

theorem spechtTransform_injective (n : ℕ) : Function.Injective (spechtTransform n) := by
  intro a b he
  apply transform_injective (Equiv.Perm (Fin n))
  funext c
  obtain ⟨μ,rfl⟩ := (SpechtActual.index_bijective n).surjective c
  obtain ⟨e⟩ := SpechtActual.index_spec μ
  have hec := congrFun he μ
  change complexFourier (SpechtActual.rep μ) a = complexFourier (SpechtActual.rep μ) b at hec
  apply LinearMap.ext
  intro v
  apply e.injective
  change e (complexFourier (irreducibleRep (SpechtActual.index μ)) a v) =
    e (complexFourier (irreducibleRep (SpechtActual.index μ)) b v)
  rw [fourier_equiv, fourier_equiv, hec]

lemma specht_family_finrank (n : ℕ) : Module.finrank ℂ (SpechtFamily n) = n.factorial := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_linearMap,← pow_two]
  exact YoungSpechtDimension.specht_degree_square_sum n

theorem spechtTransform_bijective (n : ℕ) : Function.Bijective (spechtTransform n) := by
  have hd : Module.finrank ℂ (Equiv.Perm (Fin n) → ℂ) = Module.finrank ℂ (SpechtFamily n) := by
    rw [specht_family_finrank,Module.finrank_pi,Fintype.card_perm,Fintype.card_fin]
  exact ⟨spechtTransform_injective n,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp (spechtTransform_injective n)⟩

def spechtFourierEquiv (n : ℕ) : (Equiv.Perm (Fin n) → ℂ) ≃ₗ[ℂ] SpechtFamily n :=
  LinearEquiv.ofBijective (spechtTransform n) (spechtTransform_bijective n)


end
end WeldedPath.FiniteFourier


end

-- Solutions.WeldedPathInjectionModelComplete
section

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical CompletionFrame OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open FiniteProjectedHom SpechtPieri

variable {j s : ℕ}

abbrev FixedFourierFamily (h : j ≤ s) :=
  (μ : DiagramCounting.Shape s) → rightInvariantHom
    (W := (spechtSub μ.1).toSubmodule) (discardedRep μ h)

def fixedFourier (h : j ≤ s) : rightFixed h →ₗ[ℂ] FixedFourierFamily h where
  toFun f μ := ⟨complexFourier (SpechtActual.rep μ) f.1,by
    intro τ
    have he := FiniteFourier.fourier_right_translate (SpechtActual.rep μ) f.1 τ.1⁻¹
    have hf : (fun g => f.1 (g*τ.1⁻¹))=f.1 := funext (fun g => f.2 g τ⁻¹)
    rw [hf,inv_inv] at he
    exact he.symm⟩
  map_add' f g := by
    funext μ
    apply Subtype.ext
    exact congrFun ((FiniteFourier.spechtTransform s).map_add f.1 g.1) μ
  map_smul' c f := by
    funext μ
    apply Subtype.ext
    exact congrFun ((FiniteFourier.spechtTransform s).map_smul c f.1) μ


theorem fixedFourier_injective (h : j ≤ s) : Function.Injective (fixedFourier h) := by
  intro f g he
  apply Subtype.ext
  apply FiniteFourier.spechtTransform_injective s
  funext μ
  exact congrArg Subtype.val (congrFun he μ)

theorem fixedFourier_surjective (h : j ≤ s) : Function.Surjective (fixedFourier h) := by
  intro F
  let a := (FiniteFourier.spechtFourierEquiv s).symm (fun μ => (F μ).1)
  have ha (μ : DiagramCounting.Shape s) : complexFourier (SpechtActual.rep μ) a=(F μ).1 :=
    congrFun ((FiniteFourier.spechtFourierEquiv s).apply_symm_apply _) μ
  have hfix : a ∈ rightFixed h := by
    intro π τ
    have he : (fun g => a (g*τ.1))=a := by
      apply FiniteFourier.spechtTransform_injective s
      funext μ
      change complexFourier (SpechtActual.rep μ) (fun g => a (g*τ.1))=
        complexFourier (SpechtActual.rep μ) a
      rw [FiniteFourier.fourier_right_translate,ha]
      exact (F μ).2 τ⁻¹
    exact congrFun he π
  refine ⟨⟨a,hfix⟩,?_⟩
  funext μ
  apply Subtype.ext
  exact ha μ

def fixedFourierEquiv (h : j ≤ s) : rightFixed h ≃ₗ[ℂ] FixedFourierFamily h :=
  LinearEquiv.ofBijective (fixedFourier h) ⟨fixedFourier_injective h,fixedFourier_surjective h⟩

def injectionFixedFourierEquiv (h : j ≤ s) :
    (OrderedInjection j s → ℂ) ≃ₗ[ℂ] FixedFourierFamily h :=
  (cosetEquiv h).trans (fixedFourierEquiv h)

@[simp] theorem injectionFixedFourierEquiv_apply (h : j ≤ s)
    (f : OrderedInjection j s → ℂ) (μ : DiagramCounting.Shape s) :
    (injectionFixedFourierEquiv h f μ).1=
      complexFourier (SpechtActual.rep μ) (fun π => f (fromPerm h π)) := rfl

def chosenPieri (μ : DiagramCounting.Shape s) (h : j ≤ s) :
    (pieriFixedSubrepresentation μ h).toSubmodule ≃ₗ[ℂ]
      ((ν : PieriShape μ j) → (spechtSub ν.1.1).toSubmodule) :=
  (pieri_equiv μ h).choose

theorem chosenPieri_action (μ : DiagramCounting.Shape s) (h : j ≤ s)
    (σ : Equiv.Perm (Fin j)) (v : (pieriFixedSubrepresentation μ h).toSubmodule)
    (ν : PieriShape μ j) :
    chosenPieri μ h ((pieriFixedSubrepresentation μ h).toRepresentation σ v) ν=
      SpechtActual.rep ν.1 σ (chosenPieri μ h v ν) :=
  (pieri_equiv μ h).choose_spec.2 σ v ν

abbrev InjectionBlocks (j s : ℕ) := (μ : DiagramCounting.Shape s) →
  (ν : PieriShape μ j) → (spechtSub ν.1.1).toSubmodule →ₗ[ℂ] (spechtSub μ.1).toSubmodule

def pieriHomEquiv (μ : DiagramCounting.Shape s) (h : j ≤ s) :
    rightInvariantHom (W := (spechtSub μ.1).toSubmodule) (discardedRep μ h) ≃ₗ[ℂ]
      ((ν : PieriShape μ j) → (spechtSub ν.1.1).toSubmodule →ₗ[ℂ] (spechtSub μ.1).toSubmodule) := by
  letI : Invertible (Fintype.card (fixing (prefixSet h)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact (invariantHomEquiv (discardedRep μ h)).trans
    (((chosenPieri μ h).arrowCongr (LinearEquiv.refl ℂ _)).trans
      (LinearMap.lsum ℂ (fun ν : PieriShape μ j => (spechtSub ν.1.1).toSubmodule) ℂ).symm)

/-- The actual ordered-injection representation in canonical horizontal-strip
Fourier blocks. The multiplicity spaces are the proved canonical Specht modules. -/
def injectionFourierEquiv (h : j ≤ s) : (OrderedInjection j s → ℂ) ≃ₗ[ℂ] InjectionBlocks j s :=
  (injectionFixedFourierEquiv h).trans (LinearEquiv.piCongrRight (fun μ => pieriHomEquiv μ h))

end
end WeldedPath.OrderedMatching

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid SpechtPieri

variable {j s : ℕ}

def ambientAction (π : Equiv.Perm (Fin s)) :
    (OrderedInjection j s → ℂ) →ₗ[ℂ] (OrderedInjection j s → ℂ) where
  toFun f u := f (permute π⁻¹ u)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def retainedAction (σ : Equiv.Perm (Fin j)) :
    (OrderedInjection j s → ℂ) →ₗ[ℂ] (OrderedInjection j s → ℂ) where
  toFun f u := f (reindex u σ)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def ambientRepresentation (j s : ℕ) :
    Representation ℂ (Equiv.Perm (Fin s)) (OrderedInjection j s → ℂ) where
  toFun := ambientAction
  map_one' := by
    apply LinearMap.ext
    intro f
    funext u
    change f (permute 1 u)=f u
    congr 1
  map_mul' π ρ := by
    apply LinearMap.ext
    intro f
    funext u
    change f (permute (π*ρ)⁻¹ u)=f (permute ρ⁻¹ (permute π⁻¹ u))
    congr 1

def retainedRepresentation (j s : ℕ) :
    Representation ℂ (Equiv.Perm (Fin j)) (OrderedInjection j s → ℂ) where
  toFun := retainedAction
  map_one' := by
    apply LinearMap.ext
    intro f
    funext u
    change f (reindex u 1)=f u
    congr 1
  map_mul' π ρ := by
    apply LinearMap.ext
    intro f
    funext u
    change f (reindex u (π*ρ))=f (reindex (reindex u π) ρ)
    congr 1

theorem injectionFixedFourier_left (h : j ≤ s) (π : Equiv.Perm (Fin s))
    (f : OrderedInjection j s → ℂ) (μ : DiagramCounting.Shape s) :
    (injectionFixedFourierEquiv h (ambientAction π f) μ).1=
      SpechtActual.rep μ π * (injectionFixedFourierEquiv h f μ).1 := by
  simp only [injectionFixedFourierEquiv_apply]
  have he : (fun ρ => ambientAction π f (fromPerm h ρ))=
      (fun ρ => f (fromPerm h (π⁻¹*ρ))) := rfl
  rw [he]
  exact FiniteFourier.fourier_left_translate (SpechtActual.rep μ)
    (fun ρ => f (fromPerm h ρ)) π

theorem injectionFixedFourier_right (h : j ≤ s) (σ : Equiv.Perm (Fin j))
    (f : OrderedInjection j s → ℂ) (μ : DiagramCounting.Shape s) :
    (injectionFixedFourierEquiv h (retainedAction σ f) μ).1=
      (injectionFixedFourierEquiv h f μ).1 * retainedRep μ h σ⁻¹ := by
  simp only [injectionFixedFourierEquiv_apply]
  have he : (fun ρ => retainedAction σ f (fromPerm h ρ))=
      (fun ρ => f (fromPerm h (ρ*Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ))) := by
    funext ρ
    exact congrArg f (fromPerm_retained h ρ σ).symm
  rw [he]
  have ht := FiniteFourier.fourier_right_translate (SpechtActual.rep μ)
    (fun ρ => f (fromPerm h ρ)) (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ)
  refine ht.trans ?_
  congr 1

def pieriInsertion (μ : DiagramCounting.Shape s) (h : j ≤ s) (ν : PieriShape μ j) :
    (spechtSub ν.1.1).toSubmodule →ₗ[ℂ] (pieriFixedSubrepresentation μ h).toSubmodule :=
  (chosenPieri μ h).symm.toLinearMap.comp
    (LinearMap.single ℂ (fun η : PieriShape μ j => (spechtSub η.1.1).toSubmodule) ν)

theorem pieriInsertion_action (μ : DiagramCounting.Shape s) (h : j ≤ s)
    (ν : PieriShape μ j) (σ : Equiv.Perm (Fin j)) (v : (spechtSub ν.1.1).toSubmodule) :
    (pieriFixedSubrepresentation μ h).toRepresentation σ (pieriInsertion μ h ν v)=
      pieriInsertion μ h ν (SpechtActual.rep ν.1 σ v) := by
  apply (chosenPieri μ h).injective
  funext η
  rw [chosenPieri_action]
  change SpechtActual.rep η.1 σ
      (chosenPieri μ h ((chosenPieri μ h).symm (Pi.single ν v)) η)=
    chosenPieri μ h ((chosenPieri μ h).symm (Pi.single ν (SpechtActual.rep ν.1 σ v))) η
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  by_cases he : η=ν
  · subst η
    simp
  · simp [Pi.single_apply,he]


@[simp] theorem injectionFourierEquiv_apply (h : j ≤ s) (f : OrderedInjection j s → ℂ)
    (μ : DiagramCounting.Shape s) (ν : PieriShape μ j) (v : (spechtSub ν.1.1).toSubmodule) :
    injectionFourierEquiv h f μ ν v=
      (injectionFixedFourierEquiv h f μ).1 (pieriInsertion μ h ν v).1 := rfl

theorem injectionFourier_left (h : j ≤ s) (π : Equiv.Perm (Fin s))
    (f : OrderedInjection j s → ℂ) (μ : DiagramCounting.Shape s) (ν : PieriShape μ j)
    (v : (spechtSub ν.1.1).toSubmodule) :
    injectionFourierEquiv h (ambientAction π f) μ ν v=
      SpechtActual.rep μ π (injectionFourierEquiv h f μ ν v) := by
  simp only [injectionFourierEquiv_apply,injectionFixedFourier_left,Module.End.mul_apply]

theorem injectionFourier_right (h : j ≤ s) (σ : Equiv.Perm (Fin j))
    (f : OrderedInjection j s → ℂ) (μ : DiagramCounting.Shape s) (ν : PieriShape μ j)
    (v : (spechtSub ν.1.1).toSubmodule) :
    injectionFourierEquiv h (retainedAction σ f) μ ν v=
      injectionFourierEquiv h f μ ν (SpechtActual.rep ν.1 σ⁻¹ v) := by
  simp only [injectionFourierEquiv_apply,injectionFixedFourier_right,Module.End.mul_apply]
  apply congrArg (injectionFixedFourierEquiv h f μ).1
  exact congrArg Subtype.val (pieriInsertion_action μ h ν σ⁻¹ v)

end
end WeldedPath.OrderedMatching

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical
open scoped BigOperators

section Kernel
variable (X : Type*) [Fintype X]

def kernelEquiv : (X × X → ℂ) ≃ₗ[ℂ] Module.End ℂ (X → ℂ) :=
  ({toFun := fun f x y => f (x,y)
    invFun := fun M p => M p.1 p.2
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl} : (X × X → ℂ) ≃ₗ[ℂ] Matrix X X ℂ).trans Matrix.toLin'

@[simp] theorem kernelEquiv_apply (f : X × X → ℂ) (g : X → ℂ) (x : X) :
    kernelEquiv X f g x=∑ y, f (x,y)*g y := rfl


end Kernel

variable {j s : ℕ}

def reindexEquiv (σ : Equiv.Perm (Fin j)) : OrderedInjection j s ≃ OrderedInjection j s where
  toFun u := reindex u σ
  invFun u := reindex u σ⁻¹
  left_inv u := by
    apply Function.Embedding.ext
    intro i
    exact congrArg u (σ.apply_symm_apply i)
  right_inv u := by
    apply Function.Embedding.ext
    intro i
    exact congrArg u (σ.symm_apply_apply i)

@[simp] theorem reindexEquiv_apply (σ : Equiv.Perm (Fin j)) (u : OrderedInjection j s) :
    reindexEquiv σ u=reindex u σ := rfl

theorem retainedAction_single (σ : Equiv.Perm (Fin j)) (v : OrderedInjection j s) :
    retainedAction σ (Pi.single (reindex v σ) 1)=Pi.single v 1 := by
  funext u
  change (Pi.single (reindex v σ) 1 : OrderedInjection j s → ℂ) (reindex u σ)=
    (Pi.single v 1 : OrderedInjection j s → ℂ) u
  simp only [Pi.single_apply]
  have he : reindex u σ=reindex v σ ↔ u=v := (reindexEquiv σ).injective.eq_iff
  simp only [he]

def retainedCommutant (j s : ℕ) : Submodule ℂ (Module.End ℂ (OrderedInjection j s → ℂ)) where
  carrier := {T | ∀ σ, T.comp (retainedAction σ)=(retainedAction σ).comp T}
  zero_mem' := by intro σ; simp
  add_mem' := by
    intro T U hT hU σ
    rw [LinearMap.add_comp,LinearMap.comp_add]
    exact congrArg₂ (·+·) (hT σ) (hU σ)
  smul_mem' := by
    intro c T hT σ
    rw [LinearMap.smul_comp,LinearMap.comp_smul]
    exact congrArg (c • ·) (hT σ)

theorem kernel_commutes_iff (f : OrderedInjection j s × OrderedInjection j s → ℂ) :
    kernelEquiv (OrderedInjection j s) f ∈ retainedCommutant j s ↔ f ∈ diagonalFixed j s := by
  constructor
  · intro h u v σ
    have he := congrFun (LinearMap.congr_fun (h σ) (Pi.single (reindex v σ) 1)) u
    change kernelEquiv _ f (retainedAction σ (Pi.single (reindex v σ) 1)) u=
      kernelEquiv _ f (Pi.single (reindex v σ) 1) (reindex u σ) at he
    rw [retainedAction_single] at he
    simp only [kernelEquiv_apply,Pi.single_apply,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true] at he
    exact he.symm
  · intro h σ
    apply LinearMap.ext
    intro g
    funext u
    change (∑ v, f (u,v)*g (reindex v σ))=
      ∑ v, f (reindex u σ,v)*g v
    apply Fintype.sum_equiv (reindexEquiv σ)
    intro v
    rw [reindexEquiv_apply,h u v σ]

def kernelFixedEquiv (j s : ℕ) : diagonalFixed j s ≃ₗ[ℂ] retainedCommutant j s where
  toFun f := ⟨kernelEquiv (OrderedInjection j s) f.1,(kernel_commutes_iff f.1).mpr f.2⟩
  invFun T := ⟨(kernelEquiv (OrderedInjection j s)).symm T.1,
    (kernel_commutes_iff _).mp (by simpa using T.2)⟩
  left_inv f := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  right_inv T := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact map_smul _ _ _

/-- Actual matching-level functions are the retained symmetric-group commutant
on the ordered-injection representation. -/
def matchingCommutantEquiv (j s : ℕ) :
    (MatchingLevel s j → ℂ) ≃ₗ[ℂ] retainedCommutant j s :=
  (matchingEquiv j s).trans (kernelFixedEquiv j s)


end
end WeldedPath.OrderedMatching

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical
open scoped BigOperators

variable {j s : ℕ}

def unused (u : OrderedInjection j s) : Finset (Fin s) := Finset.univ \ Finset.univ.map u

@[simp] theorem mem_unused (u : OrderedInjection j s) (x : Fin s) :
    x ∈ unused u ↔ ∀ i, u i≠x := by
  simp [unused]

theorem unused_card (u : OrderedInjection j s) : (unused u).card=s-j := by
  rw [unused,Finset.card_sdiff]
  simp

theorem sum_split_injection (u : OrderedInjection j s) (F : Fin s → ℂ) :
    (∑ x, F x)=(∑ i, F (u i))+∑ x ∈ unused u, F x := by
  have hd : Disjoint (Finset.univ.map u) (unused u) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  have he : Finset.univ.map u ∪ unused u=Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  calc
    _ = ∑ x ∈ Finset.univ.map u ∪ unused u, F x := by rw [he]
    _ = (∑ x ∈ Finset.univ.map u, F x)+(∑ x ∈ unused u, F x) := Finset.sum_union hd
    _ = _ := by rw [Finset.sum_map]

theorem permute_swap_used (u : OrderedInjection j s) (i k : Fin j) :
    permute (Equiv.swap (u i) (u k)) u=reindex u (Equiv.swap i k) := by
  apply Function.Embedding.ext
  intro a
  exact (u.injective.map_swap i k a).symm

theorem permute_swap_unused (u : OrderedInjection j s) (x y : Fin s)
    (hx : x ∈ unused u) (hy : y ∈ unused u) : permute (Equiv.swap x y) u=u := by
  apply Function.Embedding.ext
  intro i
  exact Equiv.swap_apply_of_ne_of_ne ((mem_unused u x).mp hx i) ((mem_unused u y).mp hy i)

def swapValue (f : OrderedInjection j s → ℂ) (u : OrderedInjection j s) (x y : Fin s) : ℂ :=
  if x=y then 0 else f (permute (Equiv.swap x y) u)

def replacementSum (f : OrderedInjection j s → ℂ) (u : OrderedInjection j s) : ℂ :=
  ∑ i, ∑ y ∈ unused u, f (permute (Equiv.swap (u i) y) u)

lemma swapValue_symm (f : OrderedInjection j s → ℂ) (u : OrderedInjection j s) (x y : Fin s) :
    swapValue f u x y=swapValue f u y x := by
  simp only [swapValue,Equiv.swap_comm,eq_comm]

lemma swapValue_used (f : OrderedInjection j s → ℂ) (u : OrderedInjection j s) (i k : Fin j) :
    swapValue f u (u i) (u k)=if i=k then 0 else f (reindex u (Equiv.swap i k)) := by
  simp only [swapValue,u.injective.eq_iff,permute_swap_used]

lemma swapValue_used_unused (f : OrderedInjection j s → ℂ) (u : OrderedInjection j s)
    (i : Fin j) (y : Fin s) (hy : y ∈ unused u) :
    swapValue f u (u i) y=f (permute (Equiv.swap (u i) y) u) :=
  if_neg ((mem_unused u y).mp hy i)

lemma unused_swap_sum (f : OrderedInjection j s → ℂ) (u : OrderedInjection j s) :
    (∑ x ∈ unused u, ∑ y ∈ unused u, swapValue f u x y)=
      (s-j : ℕ)*((s-j : ℕ)-1 : ℂ)*f u := by
  have hinner (x : Fin s) (hx : x ∈ unused u) :
      (∑ y ∈ unused u, swapValue f u x y)=((unused u).card-1 : ℂ)*f u := by
    have he : (∑ y ∈ unused u, swapValue f u x y)=
        ∑ y ∈ unused u, if x=y then 0 else f u := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [swapValue,permute_swap_unused u x y hx hy]
    rw [he]
    have he' : (∑ y ∈ unused u, if x=y then (0 : ℂ) else f u)=
        (∑ y ∈ unused u, f u)-(∑ y ∈ unused u, if x=y then f u else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      split_ifs <;> simp
    rw [he']
    simp only [Finset.sum_const,Finset.sum_ite_eq, hx,if_true]
    rw [nsmul_eq_mul]
    ring
  simp_rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_const,nsmul_eq_mul,unused_card]
  ring

/-- The ordered-tuple adjacency is the difference of the two transposition
class sums, with the unused-unused transpositions removed. -/
theorem ambient_swap_sum (f : OrderedInjection j s → ℂ) (u : OrderedInjection j s) :
    (∑ x : Fin s, ∑ y : Fin s, swapValue f u x y)=
      (∑ i : Fin j, ∑ k : Fin j, if i=k then 0 else f (reindex u (Equiv.swap i k)))+
        2*replacementSum f u+((s-j : ℕ)*((s-j : ℕ)-1 : ℂ))*f u := by
  rw [sum_split_injection u]
  simp_rw [sum_split_injection u (swapValue f u _)]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  have hused : (∑ i : Fin j, ∑ k : Fin j, swapValue f u (u i) (u k))=
      ∑ i : Fin j, ∑ k : Fin j, if i=k then 0 else f (reindex u (Equiv.swap i k)) := by
    simp_rw [swapValue_used]
  have hcross : (∑ i : Fin j, ∑ y ∈ unused u, swapValue f u (u i) y)=replacementSum f u := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro y hy
    exact swapValue_used_unused f u i y hy
  have hcross' : (∑ y ∈ unused u, ∑ i : Fin j, swapValue f u y (u i))=replacementSum f u := by
    rw [Finset.sum_comm]
    refine Eq.trans ?_ hcross
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro y hy
    exact swapValue_symm f u y (u i)
  rw [hused,hcross,hcross',unused_swap_sum]
  ring

theorem replacementSum_eq_content_difference (f : OrderedInjection j s → ℂ)
    (u : OrderedInjection j s) :
    replacementSum f u=
      (1/2 : ℂ)*(∑ x : Fin s, ∑ y : Fin s, swapValue f u x y)-
      (1/2 : ℂ)*(∑ i : Fin j, ∑ k : Fin j, if i=k then 0 else f (reindex u (Equiv.swap i k)))-
      ((s-j).choose 2 : ℂ)*f u := by
  rw [ambient_swap_sum,Nat.cast_choose_two]
  ring

end
end WeldedPath.OrderedMatching


end

-- Solutions.WeldedPathInjectionSpectrum
section

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid SpechtPieri
open YoungTranspositionContent YoungStripContent
open scoped BigOperators

variable {j s : ℕ}

lemma orderedSwapSum_vector {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (v : V) :
    orderedSwapSum ρ v=∑ x : Fin n, ∑ y : Fin n, if x=y then 0 else ρ (Equiv.swap x y) v := by
  simp only [orderedSwapSum,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases he : x=y
  · rw [if_pos he,if_pos he,LinearMap.zero_apply]
  · rw [if_neg he,if_neg he]

def birthOperator (j s : ℕ) : Module.End ℂ (OrderedInjection j s → ℂ) :=
  (j : ℂ) • 1+(1/2 : ℂ) • orderedSwapSum (ambientRepresentation j s)-
    (1/2 : ℂ) • orderedSwapSum (retainedRepresentation j s)-((s-j).choose 2 : ℂ) • 1

theorem birthOperator_apply (f : OrderedInjection j s → ℂ) (u : OrderedInjection j s) :
    birthOperator j s f u=(j : ℂ)*f u+replacementSum f u := by
  have hA : orderedSwapSum (ambientRepresentation j s) f u=
      ∑ x : Fin s, ∑ y : Fin s, swapValue f u x y := by
    rw [orderedSwapSum_vector]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases he : x=y
    · simp only [if_pos he,Pi.zero_apply,swapValue]
    · rw [if_neg he]
      change f (permute (Equiv.swap x y)⁻¹ u)=swapValue f u x y
      rw [Equiv.swap_inv,swapValue,if_neg he]
  have hR : orderedSwapSum (retainedRepresentation j s) f u=
      ∑ x : Fin j, ∑ y : Fin j, if x=y then 0 else f (reindex u (Equiv.swap x y)) := by
    rw [orderedSwapSum_vector]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases he : x=y
    · rw [if_pos he,if_pos he]
      rfl
    · rw [if_neg he,if_neg he]
      rfl
  change (j : ℂ)*f u+(1/2 : ℂ)*orderedSwapSum (ambientRepresentation j s) f u-
    (1/2 : ℂ)*orderedSwapSum (retainedRepresentation j s) f u-
    ((s-j).choose 2 : ℂ)*f u=_
  rw [hA,hR]
  rw [replacementSum_eq_content_difference]
  ring

theorem injectionFourier_ambient_class (h : j ≤ s) (f : OrderedInjection j s → ℂ)
    (μ : DiagramCounting.Shape s) (ν : PieriShape μ j) (v : (spechtSub ν.1.1).toSubmodule) :
    injectionFourierEquiv h (((1/2 : ℂ) • orderedSwapSum (ambientRepresentation j s)) f) μ ν v=
      contentSum μ.1 • injectionFourierEquiv h f μ ν v := by
  have he := LinearMap.congr_fun (actual_transposition_content μ) (injectionFourierEquiv h f μ ν v)
  simp only [LinearMap.smul_apply,orderedSwapSum_vector,Module.End.one_apply] at he
  rw [← he]
  simp only [LinearMap.smul_apply,orderedSwapSum_vector,map_smul,map_sum,Finset.sum_apply,
    Pi.smul_apply,LinearMap.smul_apply,LinearMap.sum_apply]
  apply congrArg ((1/2 : ℂ) • ·)
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases he : x=y
  · rw [if_pos he,if_pos he]
    simp
  · rw [if_neg he,if_neg he]
    exact injectionFourier_left h (Equiv.swap x y) f μ ν v

theorem injectionFourier_retained_class (h : j ≤ s) (f : OrderedInjection j s → ℂ)
    (μ : DiagramCounting.Shape s) (ν : PieriShape μ j) (v : (spechtSub ν.1.1).toSubmodule) :
    injectionFourierEquiv h (((1/2 : ℂ) • orderedSwapSum (retainedRepresentation j s)) f) μ ν v=
      contentSum ν.1.1 • injectionFourierEquiv h f μ ν v := by
  have he := LinearMap.congr_fun (actual_transposition_content ν.1) v
  have he' := congrArg (injectionFourierEquiv h f μ ν) he
  simp only [LinearMap.smul_apply,orderedSwapSum_vector,Module.End.one_apply,map_smul,map_sum] at he'
  rw [← he']
  simp only [LinearMap.smul_apply,orderedSwapSum_vector,map_smul,map_sum,Finset.sum_apply,
    Pi.smul_apply,LinearMap.smul_apply,LinearMap.sum_apply]
  apply congrArg ((1/2 : ℂ) • ·)
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases he : x=y
  · rw [if_pos he,if_pos he]
    simp
  · rw [if_neg he,if_neg he]
    change injectionFourierEquiv h (retainedAction (Equiv.swap x y) f) μ ν v=
      injectionFourierEquiv h f μ ν (SpechtActual.rep ν.1 (Equiv.swap x y) v)
    simpa only [Equiv.swap_inv] using injectionFourier_right h (Equiv.swap x y) f μ ν v

theorem injectionFourier_birth (h : j ≤ s) (f : OrderedInjection j s → ℂ)
    (μ : DiagramCounting.Shape s) (ν : PieriShape μ j) :
    injectionFourierEquiv h (birthOperator j s f) μ ν=
      (excess ν.1.1 μ.1 (s-j) : ℂ) • injectionFourierEquiv h f μ ν := by
  apply LinearMap.ext
  intro v
  have hv : ν.1.1.card=j := ν.1.2
  have hb : birthOperator j s f=(j : ℂ) • f+
      ((1/2 : ℂ) • orderedSwapSum (ambientRepresentation j s)) f-
      ((1/2 : ℂ) • orderedSwapSum (retainedRepresentation j s)) f-
      ((s-j).choose 2 : ℂ) • f := rfl
  rw [hb]
  simp only [map_add,map_sub,Pi.add_apply,Pi.sub_apply,LinearMap.add_apply,LinearMap.sub_apply]
  rw [injectionFourier_ambient_class,injectionFourier_retained_class]
  simp only [map_smul,Pi.smul_apply,LinearMap.smul_apply,excess,Int.cast_add,
    Int.cast_sub,Int.cast_natCast,contentInt_complex,hv]
  module


end
end WeldedPath.OrderedMatching


end

-- Solutions.WeldedPathInjectionKernelComplete
section

namespace WeldedPath.FiniteCharacterMultiplicity

noncomputable section
open Classical
open scoped BigOperators

variable {G I : Type*} [Group G] [Fintype G] [Fintype I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

def piEnd (F : ∀ i, Module.End ℂ (V i)) : Module.End ℂ ((i : I) → V i) :=
  LinearMap.pi (fun i => (F i).comp (LinearMap.proj i))

theorem piEnd_eq_sum (F : ∀ i, Module.End ℂ (V i)) :
    piEnd F=∑ i, (LinearMap.single ℂ V i).comp ((F i).comp (LinearMap.proj i)) := by
  apply LinearMap.ext
  intro v
  funext i
  simp [piEnd,LinearMap.single_apply]

theorem trace_piEnd (F : ∀ i, Module.End ℂ (V i)) :
    LinearMap.trace ℂ ((i : I) → V i) (piEnd F)=
      ∑ i, LinearMap.trace ℂ (V i) (F i) := by
  rw [piEnd_eq_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (LinearMap.single ℂ V i).comp ((F i).comp (LinearMap.proj i))=
      ((LinearMap.single ℂ V i).comp (F i)).comp (LinearMap.proj i) := rfl
  rw [he,LinearMap.trace_comp_comm']
  congr 1
  apply LinearMap.ext
  intro v
  simp

def piRepresentation (ρ : ∀ i, Representation ℂ G (V i)) :
    Representation ℂ G ((i : I) → V i) where
  toFun g := piEnd (fun i => ρ i g)
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    simp [piEnd]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    simp [piEnd,map_mul,Module.End.mul_apply]

theorem character_piRepresentation (ρ : ∀ i, Representation ℂ G (V i)) (g : G) :
    (piRepresentation ρ).character g=∑ i, (ρ i).character g :=
  trace_piEnd (fun i => ρ i g)

/-- The commutant dimension for a character expansion in inequivalent dual
irreducible characters, proved directly from character orthogonality. -/
theorem commutant_finrank (ρ : ∀ i, Representation ℂ G (V i))
    [∀ i, Representation.IsIrreducible (ρ i)]
    (hne : ∀ i k, i≠k → ¬ Nonempty (Representation.Equiv (ρ i) (ρ k)))
    (τ : Representation ℂ G W) (m : I → ℕ)
    (hχ : ∀ g, τ.character g=∑ i, (m i : ℂ)*(ρ i).character g⁻¹) :
    Module.finrank ℂ (Representation.IntertwiningMap τ τ)=∑ i, (m i)^2 := by
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  have horth (i k : I) :
      (Nat.card G : ℂ)⁻¹*(∑ g, (ρ k).character g*(ρ i).character g⁻¹)=
        if i=k then (1 : ℂ) else 0 := by
    rw [Representation.char_orthonormal]
    by_cases hik : i=k
    · subst k
      simp only [if_pos rfl]
      exact if_pos ⟨Representation.Equiv.refl _⟩
    · rw [if_neg hik,if_neg (hne i k hik)]
  have hsum :
      (Nat.card G : ℂ)⁻¹*(∑ g, τ.character g*τ.character g⁻¹)=
        ∑ i, (m i : ℂ)^2 := by
    simp_rw [hχ,inv_inv]
    calc
      _ = ∑ i, ∑ k, ((m i : ℂ)*m k)*
          ((Nat.card G : ℂ)⁻¹*∑ g, (ρ i).character g*(ρ k).character g⁻¹) := by
        simp only [Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ = _ := by
        simp_rw [horth]
        simp [pow_two]
  rw [Representation.card_inv_mul_sum_char_mul_char_eq_finrank] at hsum
  exact_mod_cast hsum

end
end WeldedPath.FiniteCharacterMultiplicity

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical YoungCounts SpechtPieri YoungStripContent OAI.PartialPermutation

lemma horizontalStrip_prependRow (n : ℕ) (ν : YoungDiagram) (hn : ν.rowLen 0 ≤ n) :
    HorizontalStrip ν (prependRow n ν hn) := by
  have hsub : ν ≤ prependRow n ν hn := by
    intro x hx
    apply (mem_prependRow n ν hn x).mpr
    by_cases hi : x.1=0
    · left
      have hj : x.2 < ν.rowLen 0 := by simpa only [hi] using ν.mem_iff_lt_rowLen.mp hx
      exact ⟨hi,hj.trans_le hn⟩
    · right
      exact ⟨hi,ν.up_left_mem (Nat.sub_le _ _) le_rfl hx⟩
  apply (horizontalStrip_interlacing hsub).mpr
  intro i
  rw [← rowTail_rowLen,rowTail_prependRow]

variable {j s : ℕ}

theorem pieri_tail_of_firstRow (hsmall : j ≤ s-j) (μ : DiagramCounting.Shape s)
    (hrow : μ.1.rowLen 0=s-j) (ν : PieriShape μ j) : ν.1.1=rowTail μ.1 := by
  have hν : ν.1.1.card=j := ν.1.2
  have hμ : μ.1.card=s := μ.2
  have hjs : j ≤ s := by omega
  have he := minimum_shape ν.2 (s-j) (by omega) (by simpa only [hν] using hsmall) hrow
  have ht := congrArg rowTail he
  rw [rowTail_prependRow] at ht
  exact ht.symm

theorem pieri_subsingleton_of_firstRow (hsmall : j ≤ s-j) (μ : DiagramCounting.Shape s)
    (hrow : μ.1.rowLen 0=s-j) : Subsingleton (PieriShape μ j) := by
  refine ⟨fun ν η => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (pieri_tail_of_firstRow hsmall μ hrow ν).trans
    (pieri_tail_of_firstRow hsmall μ hrow η).symm

theorem pieri_nonempty_of_firstRow (μ : DiagramCounting.Shape s)
    (hrow : μ.1.rowLen 0=s-j) (hjs : j ≤ s) : Nonempty (PieriShape μ j) := by
  have hc : (rowTail μ.1).card=j := by
    have hh := rowTail_card μ.1
    have hμ : μ.1.card=s := μ.2
    omega
  let ν : DiagramCounting.Shape j := ⟨rowTail μ.1,hc⟩
  refine ⟨⟨ν,?_⟩⟩
  change HorizontalStrip (rowTail μ.1) μ.1
  have hh := horizontalStrip_prependRow (μ.1.rowLen 0) (rowTail μ.1) (rowTail_rowLen_le μ.1)
  simpa only [prependRow_rowTail] using hh

abbrev ZeroChannel (j s : ℕ) :=
  {p : (Σ μ : DiagramCounting.Shape s, PieriShape μ j) // p.1.1.rowLen 0=s-j}

abbrev LevelShape (j s : ℕ) := {μ : DiagramCounting.Shape s // μ.1.rowLen 0=s-j}

def zeroChannelParent (p : ZeroChannel j s) : LevelShape j s := ⟨p.1.1,p.2⟩

def zeroChannelTail (p : ZeroChannel j s) : DiagramCounting.Shape j := p.1.2.1

theorem zeroChannelParent_injective (hsmall : j ≤ s-j) :
    Function.Injective (zeroChannelParent (j := j) (s := s)) := by
  rintro ⟨⟨μ,ν⟩,hp⟩ ⟨⟨lam,η⟩,hq⟩ he
  have hμ : μ=lam := congrArg Subtype.val he
  subst lam
  have hνη : ν=η := (pieri_subsingleton_of_firstRow hsmall μ hp).elim ν η
  subst η
  rfl

theorem zeroChannelParent_surjective (hjs : j ≤ s) :
    Function.Surjective (zeroChannelParent (j := j) (s := s)) := by
  intro μ
  obtain ⟨ν⟩ := pieri_nonempty_of_firstRow μ.1 μ.2 hjs
  exact ⟨⟨⟨μ.1,ν⟩,μ.2⟩,rfl⟩

def zeroChannelEquiv (hsmall : j ≤ s-j) : ZeroChannel j s ≃ LevelShape j s :=
  Equiv.ofBijective zeroChannelParent
    ⟨zeroChannelParent_injective hsmall,zeroChannelParent_surjective (by omega)⟩

theorem zeroChannelTail_injective (hsmall : j ≤ s-j) :
    Function.Injective (zeroChannelTail (j := j) (s := s)) := by
  intro p q he
  apply zeroChannelParent_injective hsmall
  apply Subtype.ext
  apply Subtype.ext
  have ht : rowTail p.1.1.1=rowTail q.1.1.1 := by
    rw [← pieri_tail_of_firstRow hsmall p.1.1 p.2 p.1.2,
      ← pieri_tail_of_firstRow hsmall q.1.1 q.2 q.1.2]
    exact congrArg Subtype.val he
  ext x
  change x ∈ p.1.1.1 ↔ x ∈ q.1.1.1
  have hlen : p.1.1.1.rowLen x.1=q.1.1.1.rowLen x.1 := by
    cases hx : x.1 with
    | zero => exact p.2.trans q.2.symm
    | succ i =>
      exact (rowTail_rowLen p.1.1.1 i).symm.trans
        ((congrArg (fun D : YoungDiagram => D.rowLen i) ht).trans (rowTail_rowLen q.1.1.1 i))
  rw [YoungDiagram.mem_iff_lt_rowLen,YoungDiagram.mem_iff_lt_rowLen,hlen]

end
end WeldedPath.OrderedMatching

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid SpechtPieri
open YoungStripContent
open scoped BigOperators

variable {j s : ℕ}

abbrev Channel (j s : ℕ) := Σ μ : DiagramCounting.Shape s, PieriShape μ j
abbrev ChannelSpace (p : Channel j s) :=
  (spechtSub p.2.1.1).toSubmodule →ₗ[ℂ] (spechtSub p.1.1).toSubmodule

def flatInjectionEquiv (h : j ≤ s) :
    (OrderedInjection j s → ℂ) ≃ₗ[ℂ] ((p : Channel j s) → ChannelSpace p) :=
  (injectionFourierEquiv h).trans
    (LinearEquiv.piCurry ℂ (fun (μ : DiagramCounting.Shape s) (ν : PieriShape μ j) =>
      (spechtSub ν.1.1).toSubmodule →ₗ[ℂ] (spechtSub μ.1).toSubmodule)).symm

theorem flatInjection_birth (h : j ≤ s) (f : OrderedInjection j s → ℂ) (p : Channel j s) :
    flatInjectionEquiv h (birthOperator j s f) p=
      (excess p.2.1.1 p.1.1 (s-j) : ℂ) • flatInjectionEquiv h f p :=
  injectionFourier_birth h f p.1 p.2

theorem channel_excess_zero_iff (hsmall : j ≤ s-j) (p : Channel j s) :
    (excess p.2.1.1 p.1.1 (s-j) : ℂ)=0 ↔ p.1.1.rowLen 0=s-j := by
  have hj : p.2.1.1.card=j := p.2.1.2
  have hs : p.1.1.card=s := p.1.2
  rw [Int.cast_eq_zero]
  exact (excess_gap p.2.2 (s-j) (by omega) (by simpa only [hj] using hsmall)).2.1

theorem birth_mem_ker_iff (hsmall : j ≤ s-j) (f : OrderedInjection j s → ℂ) :
    f ∈ (birthOperator j s).ker ↔
      flatInjectionEquiv (by omega : j ≤ s) f ∈
        DiagonalBlockSpace.supported (𝕜 := ℂ) (W := fun p : Channel j s => ChannelSpace p)
          (fun p : Channel j s => p.1.1.rowLen 0=s-j) := by
  rw [DiagonalBlockSpace.mem_kernel_iff (flatInjectionEquiv (by omega : j ≤ s))
    (birthOperator j s) (fun p => (excess p.2.1.1 p.1.1 (s-j) : ℂ))
    (flatInjection_birth (by omega : j ≤ s))]
  have hp : (fun p : Channel j s => (excess p.2.1.1 p.1.1 (s-j) : ℂ)=0)=
      (fun p : Channel j s => p.1.1.rowLen 0=s-j) :=
    funext (fun p => propext (channel_excess_zero_iff hsmall p))
  rw [hp]

def zeroInjectionEquiv (hsmall : j ≤ s-j) :
    (birthOperator j s).ker ≃ₗ[ℂ] ((p : ZeroChannel j s) → ChannelSpace p.1) :=
  DiagonalBlockSpace.blocksEquiv (flatInjectionEquiv (by omega : j ≤ s))
    (birthOperator j s).ker (fun p : Channel j s => p.1.1.rowLen 0=s-j)
    (birth_mem_ker_iff hsmall)

@[simp] theorem zeroInjectionEquiv_apply (hsmall : j ≤ s-j)
    (f : (birthOperator j s).ker) (p : ZeroChannel j s) :
    zeroInjectionEquiv hsmall f p=injectionFourierEquiv (by omega : j ≤ s) f.1 p.1.1 p.1.2 := rfl

theorem birth_commutes_retained (h : j ≤ s) (σ : Equiv.Perm (Fin j))
    (f : OrderedInjection j s → ℂ) :
    birthOperator j s (retainedAction σ f)=retainedAction σ (birthOperator j s f) := by
  apply (injectionFourierEquiv h).injective
  funext μ ν
  apply LinearMap.ext
  intro v
  rw [injectionFourier_birth]
  simp only [LinearMap.smul_apply,injectionFourier_right]
  rw [injectionFourier_birth]
  rfl

def birthKernelSubrepresentation (h : j ≤ s) : Subrepresentation (retainedRepresentation j s) where
  toSubmodule := (birthOperator j s).ker
  apply_mem_toSubmodule := by
    intro σ f hf
    change birthOperator j s (retainedAction σ f)=0
    rw [birth_commutes_retained h σ f,show birthOperator j s f=0 from hf,map_zero]

def zeroBlockRepresentation (p : ZeroChannel j s) :
    Representation ℂ (Equiv.Perm (Fin j)) (ChannelSpace p.1) :=
  Representation.linHom (SpechtActual.rep p.1.2.1)
    (Representation.trivial ℂ (Equiv.Perm (Fin j)) (spechtSub p.1.1.1).toSubmodule)

lemma zeroFamily_apply (σ : Equiv.Perm (Fin j))
    (F : (p : ZeroChannel j s) → ChannelSpace p.1) (p : ZeroChannel j s)
    (v : (spechtSub p.1.2.1.1).toSubmodule) :
    FiniteCharacterMultiplicity.piRepresentation (fun p : ZeroChannel j s => zeroBlockRepresentation p)
      σ F p v=F p (SpechtActual.rep p.1.2.1 σ⁻¹ v) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem zeroInjectionEquiv_action (hsmall : j ≤ s-j) (σ : Equiv.Perm (Fin j))
    (f : (birthKernelSubrepresentation (by omega : j ≤ s)).toSubmodule) :
    zeroInjectionEquiv hsmall ((birthKernelSubrepresentation (by omega : j ≤ s)).toRepresentation σ f)=
      FiniteCharacterMultiplicity.piRepresentation (fun p : ZeroChannel j s => zeroBlockRepresentation p)
        σ (zeroInjectionEquiv hsmall f) := by
  funext p
  apply LinearMap.ext
  intro v
  with_unfolding_all rw [zeroInjectionEquiv_apply,zeroFamily_apply,zeroInjectionEquiv_apply]
  exact injectionFourier_right (by omega : j ≤ s) σ f.1 p.1.1 p.1.2 v

def zeroRepresentationEquiv (hsmall : j ≤ s-j) :
    Representation.Equiv (birthKernelSubrepresentation (by omega : j ≤ s)).toRepresentation
      (FiniteCharacterMultiplicity.piRepresentation (fun p : ZeroChannel j s => zeroBlockRepresentation p)) where
  toLinearEquiv := zeroInjectionEquiv hsmall
  isIntertwining' σ := LinearMap.ext (zeroInjectionEquiv_action hsmall σ)

theorem birthKernel_character (hsmall : j ≤ s-j) (σ : Equiv.Perm (Fin j)) :
    (birthKernelSubrepresentation (by omega : j ≤ s)).toRepresentation.character σ=
      ∑ p : ZeroChannel j s, (Module.finrank ℂ (spechtSub p.1.1.1).toSubmodule : ℂ)*
        Representation.character (SpechtActual.rep p.1.2.1) σ⁻¹ := by
  rw [Representation.char_iso (zeroRepresentationEquiv hsmall),
    FiniteCharacterMultiplicity.character_piRepresentation]
  apply Finset.sum_congr rfl
  intro p _
  rw [zeroBlockRepresentation,Representation.char_linHom]
  have ht : (Representation.trivial ℂ (Equiv.Perm (Fin j))
      (spechtSub p.1.1.1).toSubmodule).character σ=
      (Module.finrank ℂ (spechtSub p.1.1.1).toSubmodule : ℂ) := by
    change LinearMap.trace ℂ (spechtSub p.1.1.1).toSubmodule
      (1 : Module.End ℂ (spechtSub p.1.1.1).toSubmodule)=_
    exact LinearMap.trace_one ℂ (spechtSub p.1.1.1).toSubmodule
  rw [ht,mul_comm]

theorem birthKernel_commutant_finrank (hsmall : j ≤ s-j) :
    Module.finrank ℂ (Representation.IntertwiningMap
      (birthKernelSubrepresentation (by omega : j ≤ s)).toRepresentation
      (birthKernelSubrepresentation (by omega : j ≤ s)).toRepresentation)=
        ∑ μ : LevelShape j s, (Module.finrank ℂ (spechtSub μ.1.1).toSubmodule)^2 := by
  have hne (p q : ZeroChannel j s) (hpq : p≠q) :
      ¬Nonempty (Representation.Equiv (SpechtActual.rep p.1.2.1) (SpechtActual.rep q.1.2.1)) := by
    rintro ⟨e⟩
    exact hpq (zeroChannelTail_injective hsmall (SpechtActual.rep_equiv_shape_eq _ _ e))
  rw [FiniteCharacterMultiplicity.commutant_finrank
    (fun p : ZeroChannel j s => SpechtActual.rep p.1.2.1) hne
    (birthKernelSubrepresentation (by omega : j ≤ s)).toRepresentation
    (fun p => Module.finrank ℂ (spechtSub p.1.1.1).toSubmodule) (birthKernel_character hsmall)]
  apply Fintype.sum_equiv (zeroChannelEquiv hsmall)
  intro p
  rfl

end
end WeldedPath.OrderedMatching


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





end WeldedPath.CompressedPrimitive

end

-- Solutions.CompressedPermutationInsertionBlock
section

namespace WeldedPath.CompressedPrimitive

open Classical HilbertSupport
open scoped BigOperators

noncomputable def insertionBlock (s : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none), ketBra (plusState I x) (ket I)


noncomputable def plusBlock (s : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none),
    ketBra (plusState I x) (plusState I x)

theorem insertionBlock_ket {s : ℕ} (x : Fin s) (I : InjDb s) :
    insertionBlock s x (ket I) = if I x = none then plusState I x else 0 := by
  simp [insertionBlock, ContinuousLinearMap.sum_apply, ketBra_apply, ket_inner]

theorem insertionBlock_adjoint (s : ℕ) (x : Fin s) :
    ContinuousLinearMap.adjoint (insertionBlock s x) =
      ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none), ketBra (ket I) (plusState I x) := by
  simp only [insertionBlock, map_sum, ketBra_eq_rankOne, InnerProductSpace.adjoint_rankOne]


theorem insertionBlock_adjoint_ket_added {s : ℕ} (x y : Fin s) (I : InjDb s)
    (hx : I x = none) (hy : I.symm y = none) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (ket (I.addPair x y)) =
      ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ) • ket I := by
  rw [insertionBlock_adjoint]
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  rw [Finset.sum_eq_single I]
  · rw [plus_inner_ket_added I I x y hx hx hy, if_pos rfl]
  · intro J hJ hJI
    rw [plus_inner_ket_added J I x y (Finset.mem_filter.mp hJ).2 hx hy,
      if_neg hJI, zero_smul]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)).elim


theorem insertionBlock_comp_adjoint (s : ℕ) (x : Fin s) :
    (insertionBlock s x).comp (ContinuousLinearMap.adjoint (insertionBlock s x)) = plusBlock s x := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [ContinuousLinearMap.comp_apply, insertionBlock_adjoint]
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply, map_sum, map_smul]
  change (∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none),
    inner ℂ (plusState I x) ψ • insertionBlock s x (ket I)) = _
  unfold plusBlock
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  apply Finset.sum_congr rfl
  intro I hI
  rw [insertionBlock_ket, if_pos (Finset.mem_filter.mp hI).2]






end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathCompletionExtension
section

namespace WeldedPath.CompletionLevels

open Classical InjDb
open scoped BigOperators

variable {s : ℕ}

theorem size_lt_of_unset (I : InjDb s) (x : Fin s) (hx : I x = none) : I.size < s := by
  have hproper : (Finset.univ.filter fun u => (I u).isSome) ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hm : x ∈ Finset.univ.filter (fun u => (I u).isSome) := by
      rw [he]
      exact Finset.mem_univ x
    simpa [hx] using hm
  simpa only [InjDb.size, Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hproper

theorem inv_sqrt_factorial_succ (m : ℕ) :
    (Real.sqrt (m.factorial : ℝ))⁻¹ =
      Real.sqrt ((m + 1 : ℕ) : ℝ) * (Real.sqrt ((m + 1).factorial : ℝ))⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]
  have hn : Real.sqrt ((m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hf : Real.sqrt (m.factorial : ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp

theorem completion_extension (I : InjDb s) (x : Fin s) (hx : I x = none) :
    ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), completion (I.addPair x y) =
      (Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ) • completion I := by
  let m := s - I.size - 1
  have hm : s - I.size = m + 1 := by
    have := size_lt_of_unset I x hx
    dsimp [m]
    omega
  have hsum : ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      completion (I.addPair x y) =
      ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) •
        ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), rawCompletion (I.addPair x y) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    change ((Real.sqrt ((s - (I.addPair x y).size).factorial : ℝ))⁻¹ : ℂ) • _ = _
    rw [size_addPair I x y hx (Finset.mem_filter.mp hy).2]
    have he : s - (I.size + 1) = m := by dsimp [m]; omega
    rw [he]
    rfl
  rw [hsum, ← rawCompletion_extension I x hx]
  change ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) • rawCompletion I =
    (Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ) •
      (((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℂ) • rawCompletion I)
  rw [smul_smul, hm]
  congr 1
  exact_mod_cast inv_sqrt_factorial_succ m

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathCoefficientStability
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]






end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathOrthogonalCollision
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι]



end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathControlledOperators
section

namespace WeldedPath.ControlledOperators

open Classical HilbertSupport EncodedOracleUnitary
open scoped BigOperators

variable {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq X]




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






end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathPolarSupport
section

namespace WeldedPath.OperatorPolar

open Classical

set_option maxHeartbeats 1000000

variable {X Y : Type*} [Fintype X] [Fintype Y]







end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathPolarProjection
section

namespace WeldedPath.OperatorPolar

open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]


end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathIntertwinerIsometry
section

namespace WeldedPath.IntertwinerIsometry

open Classical OperatorPolar CompletionLevels IntertwinerPartial HilbertSupport
open scoped BigOperators








end WeldedPath.IntertwinerIsometry

end

-- Solutions.WeldedPathIntertwinerLevels
section

namespace WeldedPath.IntertwinerIsometry

open Classical OperatorPolar CompletionLevels IntertwinerPartial HilbertSupport
open scoped BigOperators




end WeldedPath.IntertwinerIsometry

end

-- Solutions.WeldedPathCompletionZeroSum
section

namespace WeldedPath.CompletionLevels

open Classical InjDb IntertwinerPartial HilbertSupport
open scoped BigOperators

variable {s : ℕ}

theorem projLevel_completion_lower (r : ℕ) (I : InjDb s) (hI : I.size = r) :
    projLevel s (r + 1) (completion I) = 0 := by
  have hmem : completion I ∈ Hle s r := Submodule.subset_span ⟨I, hI, rfl⟩
  apply (Hlevel s (r + 1)).eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  rw [sub_zero]
  exact ((Hle s r).mem_orthogonal w).mp hw.2 (completion I) hmem

theorem Gam_adjoint_zero_sum (r : ℕ) (I : InjDb s) (hI : I.size = r)
    (x : Fin s) (hx : I x = none) (ψ : Hil (Equiv.Perm (Fin s))) :
    ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      ContinuousLinearMap.adjoint (Gam s (r + 1)) ψ (I.addPair x y) = 0 := by
  have hproj : ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      projLevel s (r + 1) (completion (I.addPair x y)) = 0 := by
    rw [← map_sum, completion_extension I x hx, map_smul,
      projLevel_completion_lower r I hI, smul_zero]
  calc
    _ = ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
        inner ℂ (projLevel s (r + 1) (completion (I.addPair x y))) ψ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← inner_ket (I.addPair x y), ContinuousLinearMap.adjoint_inner_right,
        Gam_ket, if_pos]
      rw [size_addPair I x y hx (Finset.mem_filter.mp hy).2, hI]
    _ = inner ℂ (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
        projLevel s (r + 1) (completion (I.addPair x y))) ψ := (sum_inner _ _ _).symm
    _ = 0 := by rw [hproj, inner_zero_left]

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathRegisterTransport
section

namespace WeldedPath.RegisterTransport

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open scoped BigOperators

variable {Ω C X : Type*} [Fintype Ω] [Fintype C] [Fintype X]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X]


theorem basisMap_ket {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : Ω → Y) (p : Ω) : basisMap f (ket p) = ket (f p) := by
  simp [basisMap, ketBra_apply, inner_ket, ket_apply]






end WeldedPath.RegisterTransport

end

-- Solutions.CompressedPermutationInverse
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb Supplement HilbertSupport RegisterTransport EncodedOracleUnitary
open scoped BigOperators

theorem addPair_symm {s : ℕ} (I : InjDb s) (x y : Fin s) :
    (I.addPair x y).symm = InjDb.addPair I.symm y x := by
  unfold InjDb.addPair
  by_cases h : I x = none ∧ I.symm y = none
  · have h' : I.symm y = none ∧ I.symm.symm x = none := ⟨h.2, h.1⟩
    rw [dif_pos h, dif_pos h']
    rfl
  · have h' : ¬(I.symm y = none ∧ I.symm.symm x = none) := fun hh => h ⟨hh.2, hh.1⟩
    rw [dif_neg h, dif_neg h']

theorem flipDb_ket {s : ℕ} (I : InjDb s) : flipDb s (ket I) = ket I.symm :=
  basisMap_ket _ _

theorem flipDb_flip {s : ℕ} (ψ : Hil (InjDb s)) : flipDb s (flipDb s ψ) = ψ := by
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul, flipDb_ket, PEquiv.symm_symm]

theorem flipDb_inner {s : ℕ} (u v : Hil (InjDb s)) :
    inner ℂ (flipDb s u) (flipDb s v) = inner ℂ u v :=
  ((flipDb s).inner_map_map_iff_adjoint_comp_self.mpr
    ((flipDb s).norm_map_iff_adjoint_comp_self.mp (flipDb_norm s))) u v








theorem flipDb_apply {s : ℕ} (ψ : Hil (InjDb s)) (I : InjDb s) :
    flipDb s ψ I = ψ I.symm := by
  have hf : Function.Involutive (fun I : InjDb s => I.symm) := PEquiv.symm_symm
  let e : InjDb s ≃ InjDb s := hf.toPerm (fun I : InjDb s => I.symm)
  exact basisMap_apply_equiv e ψ I.symm




end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathCompressionSelfAdjoint
section

namespace WeldedPath.CompletionLevels

open Classical InjDb IntertwinerPartial HilbertSupport
open scoped BigOperators

variable {s : ℕ}

theorem unused_preimage_of_extends (I : InjDb s) (y : Fin s) (hy : I.symm y = none)
    (φ : Equiv.Perm (Fin s)) (hφ : Extends φ I) : I (φ.symm y) = none := by
  cases hx : I (φ.symm y) with
  | none => rfl
  | some z =>
    have hz : y = z := by simpa only [Equiv.apply_symm_apply] using hφ _ z hx
    subst z
    have hi := (I.inv (φ.symm y) y).mpr hx
    change I.symm y = some (φ.symm y) at hi
    rw [hy] at hi
    cases hi

theorem rawCompletion_inverse_extension (I : InjDb s) (y : Fin s) (hy : I.symm y = none) :
    rawCompletion I = ∑ x ∈ Finset.univ.filter (fun x => I x = none),
      rawCompletion (I.addPair x y) := by
  ext φ
  simp only [WithLp.ofLp_sum, Finset.sum_apply, rawCompletion_apply]
  by_cases hφ : Extends φ I
  · rw [if_pos hφ]
    symm
    rw [Finset.sum_eq_single (φ.symm y)]
    · rw [if_pos ((extends_addPair_iff I (φ.symm y) y
        (unused_preimage_of_extends I y hy φ hφ) hy φ).mpr
        ⟨hφ,φ.apply_symm_apply y⟩)]
    · intro x hx hne
      apply if_neg
      intro he
      have heq := ((extends_addPair_iff I x y (Finset.mem_filter.mp hx).2 hy φ).mp he).2
      exact hne ((Equiv.eq_symm_apply φ).mpr heq)
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        unused_preimage_of_extends I y hy φ hφ⟩)).elim
  · rw [if_neg hφ]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    apply if_neg
    intro he
    exact hφ (((extends_addPair_iff I x y (Finset.mem_filter.mp hx).2 hy φ).mp he).1)

theorem completion_inverse_extension (I : InjDb s) (y : Fin s) (hy : I.symm y = none) :
    ∑ x ∈ Finset.univ.filter (fun x => I x = none), completion (I.addPair x y) =
      (Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ) • completion I := by
  let m := s - I.size - 1
  have hm : s - I.size = m + 1 := by
    have hi := size_lt_of_unset I.symm y hy
    rw [CompressedPrimitive.size_symm] at hi
    dsimp [m]
    omega
  have hsum : ∑ x ∈ Finset.univ.filter (fun x => I x = none),
      completion (I.addPair x y) =
      ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) •
        ∑ x ∈ Finset.univ.filter (fun x => I x = none), rawCompletion (I.addPair x y) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    change ((Real.sqrt ((s - (I.addPair x y).size).factorial : ℝ))⁻¹ : ℂ) • _ = _
    rw [size_addPair I x y (Finset.mem_filter.mp hx).2 hy]
    have he : s - (I.size + 1) = m := by dsimp [m]; omega
    rw [he]
    rfl
  rw [hsum, ← rawCompletion_inverse_extension I y hy]
  change ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) • rawCompletion I =
    (Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ) •
      (((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℂ) • rawCompletion I)
  rw [smul_smul, hm]
  congr 1
  exact_mod_cast inv_sqrt_factorial_succ m

theorem Gam_adjoint_inverse_zero_sum (r : ℕ) (I : InjDb s) (hI : I.size = r)
    (y : Fin s) (hy : I.symm y = none) (ψ : Hil (Equiv.Perm (Fin s))) :
    ∑ x ∈ Finset.univ.filter (fun x => I x = none),
      ContinuousLinearMap.adjoint (Gam s (r + 1)) ψ (I.addPair x y) = 0 := by
  have hproj : ∑ x ∈ Finset.univ.filter (fun x => I x = none),
      projLevel s (r + 1) (completion (I.addPair x y)) = 0 := by
    rw [← map_sum, completion_inverse_extension I y hy, map_smul,
      projLevel_completion_lower r I hI, smul_zero]
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x => I x = none),
        inner ℂ (projLevel s (r + 1) (completion (I.addPair x y))) ψ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← inner_ket (I.addPair x y), ContinuousLinearMap.adjoint_inner_right,
        Gam_ket, if_pos]
      rw [size_addPair I x y (Finset.mem_filter.mp hx).2 hy, hI]
    _ = inner ℂ (∑ x ∈ Finset.univ.filter (fun x => I x = none),
        projLevel s (r + 1) (completion (I.addPair x y))) ψ := (sum_inner _ _ _).symm
    _ = 0 := by rw [hproj, inner_zero_left]

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathIncidenceOperators
section

namespace WeldedPath.Incidence

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels
open scoped BigOperators

variable {s : ℕ}

def recordLevel (s j : ℕ) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  diagProj (fun I : InjDb s => I.size = j)

def domainMap (s j : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  (ContinuousLinearMap.adjoint (insertionBlock s x)).comp (recordLevel s j)

def imageMap (s j : ℕ) (y : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  (flipDb s).comp ((domainMap s j y).comp (flipDb s))

def laplacian (s j : ℕ) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  ∑ x : Fin s, ((ContinuousLinearMap.adjoint (domainMap s j x)).comp (domainMap s j x) +
    (ContinuousLinearMap.adjoint (imageMap s j x)).comp (imageMap s j x))

lemma insertionBlock_adjoint_apply (x : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    ContinuousLinearMap.adjoint (insertionBlock s x) a I =
      if I x = none then inner ℂ (plusState I x) a else 0 := by
  rw [insertionBlock_adjoint]
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, ket_apply]
  simp

lemma inner_plusState (x : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    inner ℂ (plusState I x) a = ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ) *
      ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), a (I.addPair x y) := by
  simp [plusState, inner_smul_left, sum_inner, inner_ket, mul_comm]

theorem insertionBlock_adjoint_ket_known (I : InjDb s) (x y : Fin s)
    (hxy : I x = some y) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (ket I) =
      ((Real.sqrt ((s-(eraseAt I x).size : ℕ) : ℝ))⁻¹ : ℂ) • ket (eraseAt I x) := by
  have he := insertionBlock_adjoint_ket_added x y (eraseAt I x)
    (eraseAt_self I x) (eraseAt_unused I x y hxy)
  rwa [eraseAt_add I x y hxy] at he

theorem insertionBlock_adjoint_ket_unset (I : InjDb s) (x : Fin s)
    (hx : I x = none) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (ket I) = 0 := by
  ext J
  rw [insertionBlock_adjoint_apply]
  by_cases hJ : J x = none
  · rw [if_pos hJ,← inner_conj_symm,ket_inner_plus_other I J x hx hJ]
    simp
  · rw [if_neg hJ]
    rfl

theorem plusBlock_ket_known (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    plusBlock s x (ket I) =
      ((Real.sqrt ((s-(eraseAt I x).size : ℕ) : ℝ))⁻¹ : ℂ) • plusState (eraseAt I x) x := by
  rw [← insertionBlock_comp_adjoint]
  change insertionBlock s x (ContinuousLinearMap.adjoint (insertionBlock s x) (ket I)) = _
  rw [insertionBlock_adjoint_ket_known I x y hxy,map_smul,insertionBlock_ket,
    if_pos (eraseAt_self I x)]

theorem plusBlock_ket_unset (I : InjDb s) (x : Fin s) (hx : I x=none) :
    plusBlock s x (ket I) = 0 := by
  rw [← insertionBlock_comp_adjoint]
  change insertionBlock s x (ContinuousLinearMap.adjoint (insertionBlock s x) (ket I)) = 0
  rw [insertionBlock_adjoint_ket_unset I x hx,map_zero]

lemma square_normalization (m : ℕ) :
    (((Real.sqrt (m : ℝ))⁻¹ : ℂ) * ((Real.sqrt (m : ℝ))⁻¹ : ℂ)) = (1/(m : ℂ)) := by
  have h : (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ = 1/(m : ℝ) := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg m),one_div]
  simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_one] using congrArg Complex.ofReal h

theorem plusBlock_ket_average (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    plusBlock s x (ket I) = (1/((s-I.size+1 : ℕ) : ℂ)) •
      ∑ z ∈ Finset.univ.filter (fun z => (eraseAt I x).symm z = none),
        ket ((eraseAt I x).addPair x z) := by
  rw [plusBlock_ket_known I x y hxy,plusState,smul_smul,square_normalization]
  have hs := eraseAt_size I x y hxy
  have hi := size_le I
  have he : s-(eraseAt I x).size=s-I.size+1 := by omega
  rw [he]

theorem domainMap_apply (j : ℕ) (x : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    domainMap s j x a I = if I.size+1=j ∧ I x=none then
      ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ) *
        ∑ y ∈ Finset.univ.filter (fun y => I.symm y=none), a (I.addPair x y)
      else 0 := by
  change ContinuousLinearMap.adjoint (insertionBlock s x) (recordLevel s j a) I = _
  rw [insertionBlock_adjoint_apply]
  by_cases hx : I x=none
  · rw [if_pos hx,inner_plusState]
    have he : (∑ y ∈ Finset.univ.filter (fun y => I.symm y=none),
        recordLevel s j a (I.addPair x y)) =
        if I.size+1=j then ∑ y ∈ Finset.univ.filter (fun y => I.symm y=none),
          a (I.addPair x y) else 0 := by
      by_cases hj : I.size+1=j
      · rw [if_pos hj]
        apply Finset.sum_congr rfl
        intro y hy
        rw [recordLevel,diagProj_apply,size_addPair I x y hx (Finset.mem_filter.mp hy).2,
          if_pos hj]
      · rw [if_neg hj]
        apply Finset.sum_eq_zero
        intro y hy
        rw [recordLevel,diagProj_apply,size_addPair I x y hx (Finset.mem_filter.mp hy).2,
          if_neg hj]
    rw [he]
    by_cases hj : I.size+1=j <;> simp [hj,hx]
  · simp [hx]

theorem imageMap_apply (j : ℕ) (y : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    imageMap s j y a I = if I.size+1=j ∧ I.symm y=none then
      ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ) *
        ∑ x ∈ Finset.univ.filter (fun x => I x=none), a (I.addPair x y)
      else 0 := by
  change flipDb s (domainMap s j y (flipDb s a)) I = _
  rw [flipDb_apply,domainMap_apply]
  simp only [size_symm,PEquiv.symm_symm,flipDb_apply,addPair_symm]
  rfl

theorem domainMap_Gam_adjoint_zero (j : ℕ) (x : Fin s)
    (v : Hil (Equiv.Perm (Fin s))) :
    domainMap s j x (ContinuousLinearMap.adjoint (Gam s j) v) = 0 := by
  ext I
  rw [domainMap_apply]
  by_cases h : I.size+1=j ∧ I x=none
  · rw [if_pos h,← h.1,Gam_adjoint_zero_sum I.size I rfl x h.2 v,mul_zero]
    rfl
  · rw [if_neg h]
    rfl

theorem imageMap_Gam_adjoint_zero (j : ℕ) (y : Fin s)
    (v : Hil (Equiv.Perm (Fin s))) :
    imageMap s j y (ContinuousLinearMap.adjoint (Gam s j) v) = 0 := by
  ext I
  rw [imageMap_apply]
  by_cases h : I.size+1=j ∧ I.symm y=none
  · rw [if_pos h,← h.1,Gam_adjoint_inverse_zero_sum I.size I rfl y h.2 v,mul_zero]
    rfl
  · rw [if_neg h]
    rfl

theorem laplacian_Gam_adjoint_zero (j : ℕ) (v : Hil (Equiv.Perm (Fin s))) :
    laplacian s j (ContinuousLinearMap.adjoint (Gam s j) v) = 0 := by
  simp only [laplacian,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,domainMap_Gam_adjoint_zero,imageMap_Gam_adjoint_zero,
    map_zero,add_zero,Finset.sum_const_zero]

lemma recordLevel_adjoint (s j : ℕ) :
    ContinuousLinearMap.adjoint (recordLevel s j) = recordLevel s j := by
  simp only [recordLevel,diagProj,map_sum,ketBra_eq_rankOne,InnerProductSpace.adjoint_rankOne]

theorem domainMap_square (s j : ℕ) (x : Fin s) :
    (ContinuousLinearMap.adjoint (domainMap s j x)).comp (domainMap s j x) =
      (recordLevel s j).comp ((plusBlock s x).comp (recordLevel s j)) := by
  simp only [domainMap,ContinuousLinearMap.adjoint_comp,recordLevel_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  rw [← insertionBlock_comp_adjoint]
  simp only [ContinuousLinearMap.comp_assoc]

theorem laplacian_positive (s j : ℕ) : (laplacian s j).IsPositive := by
  unfold laplacian
  apply ContinuousLinearMap.isPositive_sum
  intro x _
  exact (domainMap s j x).isPositive_adjoint_comp_self.add
    (imageMap s j x).isPositive_adjoint_comp_self

theorem laplacian_energy (j : ℕ) (a : Hil (InjDb s)) :
    (inner ℂ a (laplacian s j a)).re =
      ∑ x : Fin s, (‖domainMap s j x a‖^2 + ‖imageMap s j x a‖^2) := by
  simp only [laplacian,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,inner_sum,inner_add_right,Complex.re_sum,Complex.add_re,
    ContinuousLinearMap.adjoint_inner_right]
  change (∑ x : Fin s, (RCLike.re (inner ℂ (domainMap s j x a) (domainMap s j x a)) +
    RCLike.re (inner ℂ (imageMap s j x a) (imageMap s j x a)))) = _
  simp only [inner_self_eq_norm_sq]

end
end WeldedPath.Incidence

end

-- Solutions.CompressedPermutationClassInsertion
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb Supplement HilbertSupport RegisterTransport EncodedOracleUnitary
open scoped BigOperators ComplexConjugate

variable {s : ℕ}












theorem flipDb_adjoint (s : ℕ) : ContinuousLinearMap.adjoint (flipDb s) = flipDb s := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  have h := flipDb_inner (flipDb s u) v
  simpa only [flipDb_flip] using h.symm




end WeldedPath.CompressedPrimitive

end

-- Solutions.CompressedPermutationInverseInsertionBlock
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb Supplement HilbertSupport

variable {s : ℕ}

noncomputable def flipConj (T : Hil (InjDb s) →L[ℂ] Hil (InjDb s)) :
    Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  (flipDb s).comp (T.comp (flipDb s))




theorem flipConj_comp (T S : Hil (InjDb s) →L[ℂ] Hil (InjDb s)) :
    flipConj (T.comp S) = (flipConj T).comp (flipConj S) := by
  ext ψ
  simp only [flipConj,ContinuousLinearMap.comp_apply,flipDb_flip]

theorem flipConj_adjoint (T : Hil (InjDb s) →L[ℂ] Hil (InjDb s)) :
    flipConj (ContinuousLinearMap.adjoint T) = ContinuousLinearMap.adjoint (flipConj T) := by
  simp only [flipConj,ContinuousLinearMap.adjoint_comp,flipDb_adjoint]
  ext ψ
  rfl






end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathIncidenceAdjacency
section

namespace WeldedPath.Incidence

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels
open scoped BigOperators

variable {s : ℕ}

lemma eraseAt_symm_of_ne (I : InjDb s) (x y z : Fin s)
    (hxy : I x=some y) (hzy : z≠y) : (eraseAt I x).symm z=I.symm z := by
  cases hz : I.symm z with
  | none =>
    cases he : (eraseAt I x).symm z with
    | none => rfl
    | some u =>
      have hu := ((eraseAt I x).inv u z).mp he
      change eraseAt I x u = some z at hu
      rw [eraseAt_apply] at hu
      by_cases hux : u=x
      · rw [if_pos hux] at hu
        cases hu
      · rw [if_neg hux] at hu
        have hh := (I.inv u z).mpr hu
        change I.symm z=some u at hh
        rw [hz] at hh
        cases hh
  | some u =>
    apply ((eraseAt I x).inv u z).mpr
    change eraseAt I x u=some z
    have hu : I u=some z := (I.inv u z).mp hz
    have hux : u≠x := by
      intro he
      rw [he,hxy] at hu
      exact hzy (Option.some.inj hu).symm
    rw [eraseAt_apply,if_neg hux,hu]

lemma unused_erased (I : InjDb s) (x y : Fin s) (hxy : I x=some y) :
    Finset.univ.filter (fun z => (eraseAt I x).symm z=none) =
      insert y (Finset.univ.filter (fun z => I.symm z=none)) := by
  ext z
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  by_cases hzy : z=y
  · subst z
    simp [eraseAt_unused I x y hxy]
  · rw [eraseAt_symm_of_ne I x y z hxy hzy]
    simp only [hzy,false_or]

theorem plusBlock_ket_replacements (I : InjDb s) (x y : Fin s) (hxy : I x=some y) :
    plusBlock s x (ket I) = (1/((s-I.size+1 : ℕ) : ℂ)) •
      (ket I + ∑ z ∈ Finset.univ.filter (fun z => I.symm z=none),
        ket ((eraseAt I x).addPair x z)) := by
  rw [plusBlock_ket_average I x y hxy,unused_erased I x y hxy,Finset.sum_insert]
  · rw [eraseAt_add I x y hxy]
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    intro he
    have hh : I.symm y=some x := (I.inv x y).mpr hxy
    rw [hh] at he
    cases he

def imageReplacements (I : InjDb s) (x : Fin s) : Hil (InjDb s) :=
  match I x with
  | none => 0
  | some _ => ∑ z ∈ Finset.univ.filter (fun z => I.symm z=none), ket ((eraseAt I x).addPair x z)

def imageAdjacency (s : ℕ) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  ∑ I : InjDb s, ketBra (∑ x : Fin s, imageReplacements I x) (ket I)

def domainAdjacency (s : ℕ) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  flipConj (imageAdjacency s)

lemma imageAdjacency_ket (I : InjDb s) :
    imageAdjacency s (ket I)=∑ x : Fin s, imageReplacements I x := by
  simp [imageAdjacency,ketBra_apply,ket_inner]

lemma known_sum (I : InjDb s) :
    (∑ x : Fin s, if I x=none then (0 : Hil (InjDb s)) else ket I) = (I.size : ℂ) • ket I := by
  have he (x : Fin s) : (if I x=none then (0 : Hil (InjDb s)) else ket I) =
      if (I x).isSome then ket I else 0 := by cases I x <;> simp
  simp_rw [he]
  rw [← Finset.sum_filter,Finset.sum_const]
  exact Nat.cast_smul_eq_nsmul ℂ _ _ |>.symm

theorem sum_plusBlock_ket (I : InjDb s) :
    (∑ x : Fin s, plusBlock s x (ket I)) = (1/((s-I.size+1 : ℕ) : ℂ)) •
      ((I.size : ℂ) • ket I + imageAdjacency s (ket I)) := by
  have he (x : Fin s) : plusBlock s x (ket I) = (1/((s-I.size+1 : ℕ) : ℂ)) •
      ((if I x=none then 0 else ket I)+imageReplacements I x) := by
    cases hx : I x with
    | none => simp [plusBlock_ket_unset I x hx,imageReplacements,hx]
    | some y => simpa only [hx,Option.some_ne_none,if_false,imageReplacements] using
        plusBlock_ket_replacements I x y hx
  simp_rw [he]
  rw [← Finset.smul_sum,Finset.sum_add_distrib,known_sum,imageAdjacency_ket]

lemma recordLevel_ket (j : ℕ) (I : InjDb s) :
    recordLevel s j (ket I) = if I.size=j then ket I else 0 :=
  diagProj_ket _ _

lemma recordLevel_plusBlock (j : ℕ) (I : InjDb s) (hI : I.size=j) (x : Fin s) :
    recordLevel s j (plusBlock s x (ket I)) = plusBlock s x (ket I) := by
  cases hx : I x with
  | none => rw [plusBlock_ket_unset I x hx,map_zero]
  | some y =>
    rw [plusBlock_ket_average I x y hx,map_smul,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    rw [recordLevel_ket,if_pos]
    rw [size_addPair _ _ _ (eraseAt_self I x) (Finset.mem_filter.mp hz).2,
      eraseAt_size I x y hx,hI]

lemma domainMap_square_ket (j : ℕ) (I : InjDb s) (hI : I.size=j) (x : Fin s) :
    (ContinuousLinearMap.adjoint (domainMap s j x)) (domainMap s j x (ket I)) =
      plusBlock s x (ket I) := by
  have he := congrArg (fun T : Hil (InjDb s) →L[ℂ] Hil (InjDb s) => T (ket I))
    (domainMap_square s j x)
  simpa only [ContinuousLinearMap.comp_apply,recordLevel_ket,if_pos hI,
    recordLevel_plusBlock j I hI x] using he

lemma imageMap_square (s j : ℕ) (x : Fin s) :
    (ContinuousLinearMap.adjoint (imageMap s j x)).comp (imageMap s j x) =
      flipConj ((ContinuousLinearMap.adjoint (domainMap s j x)).comp (domainMap s j x)) := by
  rw [flipConj_comp,flipConj_adjoint]
  rfl

theorem laplacian_ket_adjacency (j : ℕ) (I : InjDb s) (hI : I.size=j) :
    laplacian s j (ket I) = (1/((s-j+1 : ℕ) : ℂ)) •
      ((2*j : ℂ) • ket I + imageAdjacency s (ket I) + domainAdjacency s (ket I)) := by
  have hsymm : InjDb.size I.symm=j := (size_symm I).trans hI
  have hi (x : Fin s) :
      (ContinuousLinearMap.adjoint (imageMap s j x)) (imageMap s j x (ket I)) =
        flipDb s (plusBlock s x (ket I.symm)) := by
    have he := congrArg (fun T : Hil (InjDb s) →L[ℂ] Hil (InjDb s) => T (ket I))
      (imageMap_square s j x)
    simpa only [ContinuousLinearMap.comp_apply,flipConj,flipDb_ket,
      domainMap_square_ket j I.symm hsymm x] using he
  simp only [laplacian,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,domainMap_square_ket j I hI,hi,Finset.sum_add_distrib]
  rw [← map_sum,sum_plusBlock_ket,sum_plusBlock_ket,map_smul,map_add,map_smul,
    flipDb_ket,PEquiv.symm_symm,size_symm,hI]
  change _ = _ • (_ + _ + flipDb s (imageAdjacency s (flipDb s (ket I))))
  rw [flipDb_ket,← smul_add]
  congr 1
  module

end
end WeldedPath.Incidence


end

-- Solutions.WeldedPathCompletionFrameRange
section

namespace WeldedPath.CompletionFrame

noncomputable section
open Classical HilbertSupport
open scoped BigOperators

variable {s : ℕ}

lemma synthesis_ket (r : ℕ) (I : InjDb s) :
    synthesis s r (ket I) = if I.size=r then completion I else 0 := by
  simp [synthesis,ketBra_apply,inner_ket,ket_apply]

lemma synthesis_adjoint_apply (r : ℕ) (v : Hil (Equiv.Perm (Fin s))) (I : InjDb s) :
    ContinuousLinearMap.adjoint (synthesis s r) v I =
      if I.size=r then inner ℂ (completion I) v else 0 := by
  rw [← inner_ket,ContinuousLinearMap.adjoint_inner_right,synthesis_ket]
  by_cases hI : I.size=r <;> simp only [hI,if_true,if_false,inner_zero_left]

theorem synthesis_range_eq (s r : ℕ) : (synthesis s r).range=Hle s r := by
  apply le_antisymm
  · rintro v ⟨w,rfl⟩
    change synthesis s r w ∈ Hle s r
    rw [synthesis_apply]
    apply Submodule.sum_mem
    intro I hI
    exact (Hle s r).smul_mem _ (Submodule.subset_span ⟨I,(Finset.mem_filter.mp hI).2,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨I,hI,rfl⟩
    refine ⟨ket I,?_⟩
    change synthesis s r (ket I)=completion I
    rw [synthesis_ket,if_pos hI]

theorem frame_eq_synthesis_comp_adjoint (s r : ℕ) :
    frame s r = (synthesis s r).comp (ContinuousLinearMap.adjoint (synthesis s r)) := by
  apply ContinuousLinearMap.ext
  intro v
  change frame s r v = synthesis s r (ContinuousLinearMap.adjoint (synthesis s r) v)
  rw [synthesis_apply]
  simp only [frame,ContinuousLinearMap.sum_apply,ketBra_apply]
  apply Finset.sum_congr rfl
  intro I hI
  rw [synthesis_adjoint_apply,if_pos (Finset.mem_filter.mp hI).2]

theorem frame_range_eq (s r : ℕ) : (frame s r).range=Hle s r := by
  have he := (synthesis s r).toLinearMap.range_self_comp_adjoint
  rw [ContinuousLinearMap.adjoint_toLinearMap] at he
  rw [frame_eq_synthesis_comp_adjoint]
  exact he.trans (synthesis_range_eq s r)

theorem frame_ker_eq (s r : ℕ) : (frame s r).ker=(Hle s r)ᗮ := by
  have hsym : (frame s r).toLinearMap.IsSymmetric := fun v w => frame_symmetric r v w
  have he := hsym.orthogonal_range
  rw [frame_range_eq] at he
  exact he.symm


end
end WeldedPath.CompletionFrame


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


/- The polynomial ring on exactly the occupied rows and columns (pp.2,6). -/
abbrev WeightPoly (lam : YoungDiagram) :=
  MvPolynomial (Sum (Fin (lam.colLen 0)) (Fin (lam.rowLen 0))) ℚ


/- Canonical tagged row/column indeterminates; unused out-of-range indices
are extended by zero and are never used in the displayed formulas (p.4). -/
def polyX (lam : YoungDiagram) (i : ℕ) : WeightPoly lam :=
  if h : i < lam.colLen 0 then MvPolynomial.X (Sum.inl ⟨i, h⟩) else 0

def polyY (lam : YoungDiagram) (j : ℕ) : WeightPoly lam :=
  if h : j < lam.rowLen 0 then MvPolynomial.X (Sum.inr ⟨j, h⟩) else 0



/- The single corner summand of the polynomial equation (4), p.4. -/

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

/- X_k is the sum of row weights, and Y_k the sum of column weights, over
equal-length blocks (p.9, Figure 4 and proof of Theorem 5). The prose on p.9
mistakenly says elements of U for both sums; the example fixes the intended meaning. -/


/- Zero-based rank of an actual corner, from top right to bottom left (p.9). -/

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

/- F_lambda, including the starting-square special labels (§2.2, p.4). -/

/- G_lambda with the source's special rules on the terminal row and column;
at a corner lambda'_s=r+1 and lambda_r=s+1 in zero-based coordinates (p.4). -/

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




















end WeldedPath.YoungCounts

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open WeldedPath.YoungCounts in

end
end

-- Accepted proof: ebf5ffa6-3bee-4d39-9ee8-cb962f91429e
section

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable







end WeldedPath.YoungCounts

end

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable









end WeldedPath.YoungCounts

end

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable










end WeldedPath.YoungCounts

end

noncomputable section

namespace WeldedPath.YoungCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable



end WeldedPath.YoungCounts

end

open WeldedPath.YoungCounts in
end

-- Accepted proof: 4981ef5f-6891-40d5-b93c-8eed1d9a3d0e
section

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace X6N26H

open WeldedPath.YoungCounts



end X6N26H

open X6N26H WeldedPath.YoungCounts in
end

namespace WeldedPath.YoungSpechtDimension
open OAI.PartialPermutation.YoungTabloid


end WeldedPath.YoungSpechtDimension


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









end
end WeldedPath.YoungCounts

namespace WeldedPath.YoungSpechtDimension
noncomputable section
open OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open YoungCounts
open scoped BigOperators


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







end
end WeldedPath.YoungCounts

namespace WeldedPath.YoungSpechtDimension
noncomputable section
open OAI.PartialPermutation.YoungTabloid
open YoungCounts



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



end
end WeldedPath.CompletionFrame
end




end

-- Solutions.WeldedPathFrameLevelSpectrum
section

namespace WeldedPath.CompletionFrame

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open CompletionLevels HilbertSupport YoungBranching
open scoped BigOperators MonoidAlgebra

variable {s : ℕ}





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




end Abstract




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


end
end WeldedPath.CompletionFrame

end

-- Solutions.WeldedPathCompletionDimension
section

namespace WeldedPath.CompletionDimension

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid
open CompletionFrame CompletionLevels YoungBranching
open scoped BigOperators

def hilbertFourier (s : ℕ) : Hil (Equiv.Perm (Fin s)) ≃ₗ[ℂ] FiniteFourier.SpechtFamily s :=
  (WithLp.linearEquiv 2 ℂ (Equiv.Perm (Fin s) → ℂ)).trans (FiniteFourier.spechtFourierEquiv s)


lemma hilbertFourier_translate {s : ℕ} (a : Equiv.Perm (Fin s))
    (v : Hil (Equiv.Perm (Fin s))) (μ : DiagramCounting.Shape s) :
    hilbertFourier s (translate a v) μ=SpechtActual.rep μ a*hilbertFourier s v μ :=
  FiniteFourier.fourier_left_translate (SpechtActual.rep μ) (fun g => v g) a

def scalar {s : ℕ} (r : ℕ) (μ : DiagramCounting.Shape s) : ℂ :=
  (s.choose r : ℂ)*(Module.finrank ℂ (initialRep μ (Nat.sub_le s r)).invariants : ℂ)/
    (Module.finrank ℂ (spechtSub μ.1).toSubmodule : ℂ)

lemma scalar_specht {s : ℕ} (r : ℕ) (hr : r  ≤  s) (μ : DiagramCounting.Shape s) :
    complexFourier (SpechtActual.rep μ) (centralKernel s r)=scalar r μ • 1 := by
  haveI : Nontrivial (spechtSub μ.1).toSubmodule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Equiv.Perm (Fin s)))
      (Representation.asModule (SpechtActual.rep μ))
  exact kernelRepresentation_scalar (SpechtActual.rep μ) r hr

lemma scalar_ne_zero_iff {s : ℕ} (r : ℕ) (hr : r  ≤  s) (μ : DiagramCounting.Shape s) :
    scalar r μ≠0 ↔ s-r  ≤  μ.1.rowLen 0 :=
  specht_frame_scalar_ne_zero_iff μ r hr (scalar r μ) (scalar_specht r hr μ)

theorem frame_diagonal {s : ℕ} (r : ℕ) (hr : r  ≤  s)
    (v : Hil (Equiv.Perm (Fin s))) (μ : DiagramCounting.Shape s) :
    hilbertFourier s (frame s r v) μ=scalar r μ • hilbertFourier s v μ := by
  rw [frame_eq_sum_translate]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,hilbertFourier_translate,
    ← smul_mul_assoc,← Finset.sum_mul]
  change complexFourier (SpechtActual.rep μ) (centralKernel s r)*hilbertFourier s v μ=_
  rw [scalar_specht r hr μ,smul_mul_assoc,one_mul]

theorem mem_Hle_iff {s : ℕ} (r : ℕ) (hr : r  ≤  s) (v : Hil (Equiv.Perm (Fin s))) :
    v∈Hle s r ↔ ∀ μ : DiagramCounting.Shape s, μ.1.rowLen 0<s-r → hilbertFourier s v μ=0 := by
  have he := DiagonalBlockSpace.mem_range_iff (hilbertFourier s) (frame s r).toLinearMap
    (scalar r) (frame_diagonal r hr) v
  change v∈(frame s r).range ↔
    (∀ μ : DiagramCounting.Shape s, ¬scalar r μ≠0 → hilbertFourier s v μ=0) at he
  rw [frame_range_eq] at he
  simpa only [scalar_ne_zero_iff r hr,not_le] using he

theorem frame_zero_iff {s : ℕ} (r : ℕ) (hr : r  ≤  s) (v : Hil (Equiv.Perm (Fin s))) :
    frame s r v=0 ↔ ∀ μ : DiagramCounting.Shape s, s-r  ≤  μ.1.rowLen 0 → hilbertFourier s v μ=0 := by
  have he := DiagonalBlockSpace.mem_kernel_iff (hilbertFourier s) (frame s r).toLinearMap
    (scalar r) (frame_diagonal r hr) v
  change frame s r v=0 ↔
    (∀ μ : DiagramCounting.Shape s, scalar r μ≠0 → hilbertFourier s v μ=0) at he
  simpa only [scalar_ne_zero_iff r hr] using he

theorem mem_Hlevel_iff {s : ℕ} (r : ℕ) (hr : r  ≤  s) (v : Hil (Equiv.Perm (Fin s))) :
    v∈Hlevel s r ↔
      hilbertFourier s v∈DiagonalBlockSpace.supported (𝕜 := ℂ)
        (W := fun μ : DiagramCounting.Shape s => Module.End ℂ (spechtSub μ.1).toSubmodule)
        (fun μ : DiagramCounting.Shape s => μ.1.rowLen 0=s-r) := by
  change v∈Hlevel s r ↔ ∀ μ : DiagramCounting.Shape s, μ.1.rowLen 0≠s-r → hilbertFourier s v μ=0
  cases r with
  | zero =>
    change v∈Hle s 0 ↔ _
    rw [mem_Hle_iff 0 hr]
    constructor
    · intro hv μ hμ
      have hc : μ.1.rowLen 0 ≤ s := by simpa only [μ.2] using DiagramCounting.rowLen_le_card μ.1 0
      exact hv μ (by omega)
    · intro hv μ hμ
      exact hv μ (by omega)
  | succ r =>
    change v∈Hle s (r+1) ∧ v∈(Hle s r)ᗮ ↔ _
    rw [← frame_ker_eq s r]
    change v∈Hle s (r+1) ∧ frame s r v=0 ↔ _
    rw [mem_Hle_iff (r+1) hr,frame_zero_iff r (by omega)]
    constructor
    · rintro ⟨hlo,hhi⟩ μ hμ
      by_cases hlow : μ.1.rowLen 0<s-(r+1)
      · exact hlo μ hlow
      · exact hhi μ (by omega)
    · intro hv
      constructor
      · intro μ hμ
        exact hv μ (by omega)
      · intro μ hμ
        exact hv μ (by omega)

def levelFourierEquiv (s r : ℕ) (hr : r  ≤  s) :
    Hlevel s r ≃ₗ[ℂ] ((μ : {μ : DiagramCounting.Shape s // μ.1.rowLen 0=s-r}) →
      Module.End ℂ (spechtSub μ.1.1).toSubmodule) :=
  DiagonalBlockSpace.blocksEquiv (hilbertFourier s) (Hlevel s r)
    (fun μ => μ.1.rowLen 0=s-r) (mem_Hlevel_iff r hr)

theorem Hlevel_finrank (s r : ℕ) (hr : r  ≤  s) :
    Module.finrank ℂ (Hlevel s r)=
      ∑ μ ∈ Finset.univ.filter (fun μ : DiagramCounting.Shape s => μ.1.rowLen 0=s-r),
        (Module.finrank ℂ (spechtSub μ.1).toSubmodule)^2 := by
  rw [(levelFourierEquiv s r hr).finrank_eq,Module.finrank_pi_fintype]
  simp only [Module.finrank_linearMap,← pow_two]
  exact (Finset.sum_subtype (Finset.univ.filter (fun μ : DiagramCounting.Shape s => μ.1.rowLen 0=s-r))
    (p := fun μ : DiagramCounting.Shape s => μ.1.rowLen 0=s-r) (by simp)
    (fun μ => (Module.finrank ℂ (spechtSub μ.1).toSubmodule)^2)).symm

end
end WeldedPath.CompletionDimension


end

-- Solutions.WeldedPathMatchingKernelComplete
section

namespace DiagonalAnticommutator

noncomputable section
open Classical
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem zero_iff_both_zero (E : V ≃ₗ[ℂ] ((i : ι) → W i))
    (B : Module.End ℂ V) (b : ι → ℝ)
    (hB : ∀ v i, E (B v) i=(b i : ℂ) • E v i) (hb : ∀ i, 0 ≤ b i)
    (T : Module.End ℂ V) : B*T+T*B=0 ↔ B*T=0 ∧ T*B=0 := by
  constructor
  · intro he
    have hcoef (i k : ι) (w : W k) :
        (((b i : ℂ)+(b k : ℂ))) • E (T (inclusion E k w)) i=0 := by
      have hh := congrArg (fun A : Module.End ℂ V => E (A (inclusion E k w)) i) he
      simp only [LinearMap.add_apply,Module.End.mul_apply,LinearMap.zero_apply,map_add,
        map_zero,Pi.add_apply,Pi.zero_apply,hB] at hh
      rw [eigen_inclusion E B (fun i => (b i : ℂ)) hB k w,map_smul,map_smul] at hh
      simpa only [add_smul,Pi.smul_apply] using hh
    have hleft : B*T=0 := by
      apply LinearMap.ext
      intro v
      apply E.injective
      funext i
      change E (B (T v)) i=E 0 i
      rw [hB,map_zero]
      by_cases hi : b i=0
      · simp [hi]
      · have hv : E (T v) i=0 := by
          rw [← sum_inclusion E v]
          simp only [map_sum,Finset.sum_apply]
          apply Finset.sum_eq_zero
          intro k _
          have hpos : 0 < b i+b k := by
            have hbi := hb i
            have hbk := hb k
            have : 0 < b i := lt_of_le_of_ne hbi (Ne.symm hi)
            linarith
          have hn : ((b i : ℂ)+(b k : ℂ))≠0 := by
            rw [← Complex.ofReal_add,Complex.ofReal_ne_zero]
            exact ne_of_gt hpos
          exact (smul_eq_zero.mp (hcoef i k (E v k))).resolve_left hn
        rw [hv,smul_zero]
        rfl
    refine ⟨hleft,?_⟩
    simpa only [hleft,zero_add] using he
  · rintro ⟨hl,hr⟩
    rw [hl,hr,add_zero]

end
end DiagonalAnticommutator

namespace WeldedPath.FiniteSupportedCommutant

noncomputable section
open Classical

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (S : Subrepresentation ρ)
  (P : Representation.IntertwiningMap ρ ρ)

def supported : Submodule ℂ (Module.End ℂ V) where
  carrier := {T | (∀ v, T v ∈ S.toSubmodule) ∧ T.comp P.toLinearMap=T ∧
    ∀ g, T.comp (ρ g)=(ρ g).comp T}
  zero_mem' := by
    refine ⟨fun _ => S.toSubmodule.zero_mem,rfl,?_⟩
    intro g
    simp
  add_mem' := by
    intro T U hT hU
    refine ⟨fun v => S.toSubmodule.add_mem (hT.1 v) (hU.1 v),?_,?_⟩
    · rw [LinearMap.add_comp]
      exact congrArg₂ (·+·) hT.2.1 hU.2.1
    · intro g
      rw [LinearMap.add_comp,LinearMap.comp_add]
      exact congrArg₂ (·+·) (hT.2.2 g) (hU.2.2 g)
  smul_mem' := by
    intro c T hT
    refine ⟨fun v => S.toSubmodule.smul_mem c (hT.1 v),?_,?_⟩
    · rw [LinearMap.smul_comp]
      exact congrArg (c • ·) hT.2.1
    · intro g
      rw [LinearMap.smul_comp,LinearMap.comp_smul]
      exact congrArg (c • ·) (hT.2.2 g)

def restrictMap (T : supported ρ S P) :
    Representation.IntertwiningMap S.toRepresentation S.toRepresentation where
  toLinearMap := (T.1.codRestrict S.toSubmodule T.2.1).comp S.toSubmodule.subtype
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (T.2.2.2 g) v.1

variable (hP : LinearMap.IsProj S.toSubmodule P.toLinearMap)

def extendMap (F : Representation.IntertwiningMap S.toRepresentation S.toRepresentation) :
    Module.End ℂ V :=
  S.toSubmodule.subtype.comp (F.toLinearMap.comp (P.toLinearMap.codRestrict S.toSubmodule hP.1))

theorem extendMap_mem (F : Representation.IntertwiningMap S.toRepresentation S.toRepresentation) :
    extendMap ρ S P hP F ∈ supported ρ S P := by
  refine ⟨fun v => (F ⟨P v,hP.1 v⟩).2,?_,?_⟩
  · apply LinearMap.ext
    intro v
    change (F ⟨P (P v),hP.1 (P v)⟩).1=(F ⟨P v,hP.1 v⟩).1
    apply congrArg (fun w : S.toSubmodule => (F w).1)
    exact Subtype.ext (hP.2 _ (hP.1 v))
  · intro g
    apply LinearMap.ext
    intro v
    change (F ⟨P (ρ g v),hP.1 (ρ g v)⟩).1=ρ g (F ⟨P v,hP.1 v⟩).1
    have harg : (⟨P (ρ g v),hP.1 (ρ g v)⟩ : S.toSubmodule)=
        S.toRepresentation g ⟨P v,hP.1 v⟩ :=
      Subtype.ext (Representation.IntertwiningMap.isIntertwining ρ ρ P g v)
    rw [harg,Representation.IntertwiningMap.isIntertwining S.toRepresentation S.toRepresentation F]
    rfl

/-- Restricting a two-sided supported commuting operator gives exactly an
endomorphism of the selected subrepresentation; extension uses its equivariant
projection. -/
def supportedEquiv : supported ρ S P ≃ₗ[ℂ]
    Representation.IntertwiningMap S.toRepresentation S.toRepresentation where
  toFun := restrictMap ρ S P
  invFun F := ⟨extendMap ρ S P hP F,extendMap_mem ρ S P hP F⟩
  left_inv T := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun T.2.2.1 v
  right_inv F := by
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    change (F ⟨P v.1,hP.1 v.1⟩).1=(F v).1
    have he : (⟨P v.1,hP.1 v.1⟩ : S.toSubmodule)=v := Subtype.ext (hP.2 v.1 v.2)
    rw [he]
  map_add' T U := by
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    rfl
  map_smul' c T := by
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    rfl

end
end WeldedPath.FiniteSupportedCommutant

namespace DiagonalBlockSpace

noncomputable section
open Classical

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*}
  {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module 𝕜 (W i)]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

def projection (E : V ≃ₗ[𝕜] ((i : ι) → W i)) (P : ι → Prop) : Module.End 𝕜 V :=
  E.symm.toLinearMap.comp ((LinearMap.pi (fun i => if P i then LinearMap.proj i else 0)).comp E.toLinearMap)

theorem projection_apply (E : V ≃ₗ[𝕜] ((i : ι) → W i)) (P : ι → Prop) (v : V) (i : ι) :
    E (projection E P v) i=if P i then E v i else 0 := by
  change E (E.symm ((LinearMap.pi (fun i => if P i then LinearMap.proj i else 0)) (E v))) i=_
  rw [LinearEquiv.apply_symm_apply]
  by_cases hi : P i
  · simp [hi]
  · simp [hi]

theorem projection_isProj (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i) :
    LinearMap.IsProj B.ker (projection E (fun i => b i=0)) := by
  constructor
  · intro v
    rw [mem_kernel_iff E B b hB]
    intro i hi
    rw [projection_apply,if_neg hi]
  · intro v hv
    apply E.injective
    funext i
    rw [projection_apply]
    by_cases hi : b i=0
    · rw [if_pos hi]
    · rw [if_neg hi]
      exact ((mem_kernel_iff E B b hB v).mp hv i hi).symm

theorem projection_comp_zero (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i) :
    (projection E (fun i => b i=0)).comp B=0 := by
  apply LinearMap.ext
  intro v
  apply E.injective
  funext i
  change E (projection E (fun i => b i=0) (B v)) i=E 0 i
  rw [projection_apply,map_zero]
  by_cases hi : b i=0
  · rw [if_pos hi,hB,hi,zero_smul]
    rfl
  · rw [if_neg hi]
    rfl

theorem complement_mem_range (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i) (v : V) :
    v-projection E (fun i => b i=0) v ∈ B.range := by
  rw [mem_range_iff E B b hB]
  intro i hi
  have hi' : b i=0 := not_not.mp hi
  rw [map_sub]
  change E v i-E (projection E (fun i => b i=0) v) i=0
  rw [projection_apply,if_pos hi',sub_self]

theorem throughProjection_iff (E : V ≃ₗ[𝕜] ((i : ι) → W i))
    (B : Module.End 𝕜 V) (b : ι → 𝕜)
    (hB : ∀ v i, E (B v) i=b i • E v i) (T : Module.End 𝕜 V) :
    T.comp (projection E (fun i => b i=0))=T ↔ T.comp B=0 := by
  constructor
  · intro hT
    calc
      T.comp B=(T.comp (projection E (fun i => b i=0))).comp B := by rw [hT]
      _ = T.comp ((projection E (fun i => b i=0)).comp B) := LinearMap.comp_assoc _ _ _
      _ = 0 := by rw [projection_comp_zero E B b hB,LinearMap.comp_zero]
  · intro hT
    apply LinearMap.ext
    intro v
    change T (projection E (fun i => b i=0) v)=T v
    obtain ⟨w,hw⟩ := complement_mem_range E B b hB v
    have he : T (v-projection E (fun i => b i=0) v)=0 := by
      rw [← hw]
      exact LinearMap.congr_fun hT w
    exact (sub_eq_zero.mp (by simpa only [map_sub] using he)).symm

end
end DiagonalBlockSpace

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical OAI.PartialPermutation OAI.PartialPermutation.YoungTabloid SpechtPieri YoungStripContent
open scoped BigOperators

variable {j s : ℕ}

def anticommutator (B : Module.End ℂ (OrderedInjection j s → ℂ)) :
    Module.End ℂ (Module.End ℂ (OrderedInjection j s → ℂ)) where
  toFun T := B*T+T*B
  map_add' T U := by simp only [mul_add,add_mul]; abel
  map_smul' c T := by simp only [mul_smul_comm,smul_mul_assoc,smul_add,RingHom.id_apply]

def matchingHarmonic (j s : ℕ) : Submodule ℂ (Module.End ℂ (OrderedInjection j s → ℂ)) :=
  (anticommutator (birthOperator j s)).ker ⊓ retainedCommutant j s

def birthProjection (h : j ≤ s) : Module.End ℂ (OrderedInjection j s → ℂ) :=
  DiagonalBlockSpace.projection (flatInjectionEquiv h)
    (fun p : Channel j s => (excess p.2.1.1 p.1.1 (s-j) : ℂ)=0)

theorem flatInjection_right (h : j ≤ s) (σ : Equiv.Perm (Fin j))
    (f : OrderedInjection j s → ℂ) (p : Channel j s)
    (v : (spechtSub p.2.1.1).toSubmodule) :
    flatInjectionEquiv h (retainedAction σ f) p v=
      flatInjectionEquiv h f p (SpechtActual.rep p.2.1 σ⁻¹ v) :=
  injectionFourier_right h σ f p.1 p.2 v

theorem birthProjection_commutes (h : j ≤ s) (σ : Equiv.Perm (Fin j))
    (f : OrderedInjection j s → ℂ) :
    birthProjection h (retainedAction σ f)=retainedAction σ (birthProjection h f) := by
  apply (flatInjectionEquiv h).injective
  funext p
  apply LinearMap.ext
  intro v
  rw [flatInjection_right]
  change flatInjectionEquiv h (DiagonalBlockSpace.projection (flatInjectionEquiv h)
    (fun p : Channel j s => (excess p.2.1.1 p.1.1 (s-j) : ℂ)=0) (retainedAction σ f)) p v=
      flatInjectionEquiv h (DiagonalBlockSpace.projection (flatInjectionEquiv h)
        (fun p : Channel j s => (excess p.2.1.1 p.1.1 (s-j) : ℂ)=0) f) p
          (SpechtActual.rep p.2.1 σ⁻¹ v)
  rw [DiagonalBlockSpace.projection_apply,DiagonalBlockSpace.projection_apply]
  by_cases hp : (excess p.2.1.1 p.1.1 (s-j) : ℂ)=0
  · rw [if_pos hp,if_pos hp]
    exact flatInjection_right h σ f p v
  · rw [if_neg hp,if_neg hp]
    rfl

def birthProjectionIntertwiner (h : j ≤ s) :
    Representation.IntertwiningMap (retainedRepresentation j s) (retainedRepresentation j s) where
  toLinearMap := birthProjection h
  isIntertwining' σ := LinearMap.ext (birthProjection_commutes h σ)

theorem birthProjection_isProj (h : j ≤ s) :
    LinearMap.IsProj (birthKernelSubrepresentation h).toSubmodule
      (birthProjectionIntertwiner h).toLinearMap :=
  DiagonalBlockSpace.projection_isProj (flatInjectionEquiv h) (birthOperator j s)
    (fun p => (excess p.2.1.1 p.1.1 (s-j) : ℂ)) (flatInjection_birth h)

theorem birth_excess_nonneg (hsmall : j ≤ s-j) (p : Channel j s) :
    (0 : ℝ) ≤ (excess p.2.1.1 p.1.1 (s-j) : ℝ) := by
  have hj : p.2.1.1.card=j := p.2.1.2
  have hs : p.1.1.card=s := p.1.2
  exact_mod_cast (excess_gap p.2.2 (s-j) (by omega) (by simpa only [hj] using hsmall)).1

theorem birth_anticommutator_zero (hsmall : j ≤ s-j)
    (T : Module.End ℂ (OrderedInjection j s → ℂ)) :
    birthOperator j s*T+T*birthOperator j s=0 ↔
      birthOperator j s*T=0 ∧ T*birthOperator j s=0 := by
  apply DiagonalAnticommutator.zero_iff_both_zero (flatInjectionEquiv (by omega : j ≤ s))
    (birthOperator j s) (fun p : Channel j s => (excess p.2.1.1 p.1.1 (s-j) : ℝ))
    ?_ (birth_excess_nonneg hsmall) T
  intro f p
  simpa only [Complex.ofReal_intCast] using flatInjection_birth (by omega : j ≤ s) f p

theorem matchingHarmonic_eq_supported (hsmall : j ≤ s-j) :
    matchingHarmonic j s=FiniteSupportedCommutant.supported (retainedRepresentation j s)
      (birthKernelSubrepresentation (by omega : j ≤ s))
      (birthProjectionIntertwiner (by omega : j ≤ s)) := by
  ext T
  change ((birthOperator j s*T+T*birthOperator j s=0) ∧
    (∀ σ, T.comp (retainedAction σ)=(retainedAction σ).comp T)) ↔
      (∀ v, T v ∈ (birthOperator j s).ker) ∧ T.comp (birthProjection (by omega : j ≤ s))=T ∧
        (∀ σ, T.comp (retainedAction σ)=(retainedAction σ).comp T)
  rw [birth_anticommutator_zero hsmall]
  constructor
  · rintro ⟨⟨hl,hr⟩,hc⟩
    refine ⟨fun v => LinearMap.congr_fun hl v,?_,hc⟩
    exact (DiagonalBlockSpace.throughProjection_iff (flatInjectionEquiv (by omega : j ≤ s))
      (birthOperator j s) (fun p => (excess p.2.1.1 p.1.1 (s-j) : ℂ))
      (flatInjection_birth (by omega : j ≤ s)) T).mpr hr
  · rintro ⟨hl,hr,hc⟩
    refine ⟨⟨LinearMap.ext hl,?_⟩,hc⟩
    exact (DiagonalBlockSpace.throughProjection_iff (flatInjectionEquiv (by omega : j ≤ s))
      (birthOperator j s) (fun p => (excess p.2.1.1 p.1.1 (s-j) : ℂ))
      (flatInjection_birth (by omega : j ≤ s)) T).mp hr

theorem matchingHarmonic_finrank (hsmall : j ≤ s-j) :
    Module.finrank ℂ (matchingHarmonic j s)=
      ∑ μ : LevelShape j s, (Module.finrank ℂ (spechtSub μ.1.1).toSubmodule)^2 := by
  rw [matchingHarmonic_eq_supported hsmall,
    (FiniteSupportedCommutant.supportedEquiv (retainedRepresentation j s)
      (birthKernelSubrepresentation (by omega : j ≤ s))
      (birthProjectionIntertwiner (by omega : j ≤ s)) (birthProjection_isProj _)).finrank_eq]
  exact birthKernel_commutant_finrank hsmall

end
end WeldedPath.OrderedMatching

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive Incidence
open scoped BigOperators

variable {j s : ℕ}

theorem database_symm (u v : OrderedInjection j s) : (database u v).symm=database v u := by
  symm
  apply database_ext
  intro y x
  change (database u v).invFun y=some x ↔ _
  rw [(database u v).inv x y]
  change database u v x=some y ↔ _
  rw [database_record_iff]
  exact exists_congr (fun i => and_comm)

theorem database_none_iff (u v : OrderedInjection j s) (x : Fin s) :
    database u v x=none ↔ x ∈ unused u := by
  rw [mem_unused]
  constructor
  · intro hx i he
    have hh := database_record u v i
    rw [he,hx] at hh
    cases hh
  · intro hx
    cases he : database u v x with
    | none => rfl
    | some y =>
      obtain ⟨i,hi,_⟩ := (database_record_iff u v x y).mp he
      exact (hx i hi).elim

theorem database_unused_image (u v : OrderedInjection j s) :
    Finset.univ.filter (fun z => (database u v).symm z=none)=unused v := by
  ext z
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,database_symm,database_none_iff]

theorem database_replace_image (u v : OrderedInjection j s) (i : Fin j)
    (z : Fin s) (hz : z ∈ unused v) :
    database u (permute (Equiv.swap (v i) z) v)=
      (eraseAt (database u v) (u i)).addPair (u i) z := by
  have hzi : z≠v i := ((mem_unused v z).mp hz i).symm
  have hfree : (eraseAt (database u v) (u i)).symm z=none := by
    rw [eraseAt_symm_of_ne _ _ _ _ (database_record u v i) hzi,database_symm]
    exact (database_none_iff v u z).mpr hz
  apply database_ext
  intro x y
  by_cases hx : x=u i
  · subst x
    rw [addPair_apply_self _ _ _ (eraseAt_self _ _) hfree]
    constructor
    · intro hy
      refine ⟨i,rfl,?_⟩
      simpa only [permute_apply,Equiv.swap_apply_left] using Option.some.inj hy
    · rintro ⟨k,hk,hy⟩
      have hki : k=i := u.injective hk
      subst k
      simpa only [permute_apply,Equiv.swap_apply_left] using congrArg some hy
  · rw [addPair_apply_other _ _ _ _ (eraseAt_self _ _) hfree hx,
      eraseAt_apply,if_neg hx,database_record_iff]
    apply exists_congr
    intro k
    constructor
    · rintro ⟨hk,hy⟩
      have hki : k≠i := fun he => hx (he ▸ hk).symm
      refine ⟨hk,?_⟩
      rw [permute_apply,Equiv.swap_apply_of_ne_of_ne (fun he => hki (v.injective he))
        ((mem_unused v z).mp hz k)]
      exact hy
    · rintro ⟨hk,hy⟩
      have hki : k≠i := fun he => hx (he ▸ hk).symm
      refine ⟨hk,?_⟩
      rw [permute_apply,Equiv.swap_apply_of_ne_of_ne (fun he => hki (v.injective he))
        ((mem_unused v z).mp hz k)] at hy
      exact hy

theorem inner_imageAdjacency_database (u v : OrderedInjection j s) (ψ : Hil (InjDb s)) :
    inner ℂ (imageAdjacency s (ket (database u v))) ψ=
      replacementSum (fun w => ψ (database u w)) v := by
  rw [imageAdjacency_ket,sum_inner,sum_split_injection u]
  have hfree : (∑ x ∈ unused u, inner ℂ (imageReplacements (database u v) x) ψ)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [imageReplacements,(database_none_iff u v x).mpr hx,inner_zero_left]
  rw [hfree,add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [imageReplacements,database_record,database_unused_image,sum_inner,inner_ket]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← database_replace_image u v i z hz]

theorem inner_domainAdjacency_database (u v : OrderedInjection j s) (ψ : Hil (InjDb s)) :
    inner ℂ (domainAdjacency s (ket (database u v))) ψ=
      replacementSum (fun w => ψ (database w v)) u := by
  change inner ℂ (flipDb s (imageAdjacency s (flipDb s (ket (database u v))))) ψ=_
  rw [flipDb_ket,database_symm,← flipDb_adjoint s,
    ContinuousLinearMap.adjoint_inner_left,inner_imageAdjacency_database]
  simp only [replacementSum,flipDb_apply,database_symm]

theorem laplacian_adjoint (s j : ℕ) :
    ContinuousLinearMap.adjoint (laplacian s j)=laplacian s j :=
  (laplacian_positive s j).isSelfAdjoint

/-- The literal database incidence Laplacian acts by the two ordered-injection
replacement operators, with the original normalization. -/
theorem laplacian_database_apply (u v : OrderedInjection j s) (ψ : Hil (InjDb s)) :
    laplacian s j ψ (database u v)=1/((s-j+1 : ℕ) : ℂ)*
      ((2*j : ℂ)*ψ (database u v)+
        replacementSum (fun w => ψ (database u w)) v+
        replacementSum (fun w => ψ (database w v)) u) := by
  rw [← inner_ket,← laplacian_adjoint s j,ContinuousLinearMap.adjoint_inner_right,
    laplacian_ket_adjacency j (database u v) (database_size u v)]
  simp only [inner_smul_left,inner_add_left,inner_ket,inner_imageAdjacency_database,
    inner_domainAdjacency_database,map_div₀,map_one,map_natCast,map_mul,map_ofNat]

end
end WeldedPath.OrderedMatching

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical YoungTranspositionContent
open scoped BigOperators

section SymmetricKernel
variable (X : Type*) [Fintype X]

def symmetricKernel : Submodule ℂ (Module.End ℂ (X → ℂ)) where
  carrier := {T | ∀ u v, T (Pi.single v 1) u=T (Pi.single u 1) v}
  zero_mem' := by intro u v; rfl
  add_mem' := by
    intro T U hT hU u v
    exact congrArg₂ (·+·) (hT u v) (hU u v)
  smul_mem' := by
    intro c T hT u v
    exact congrArg (c*·) (hT u v)

theorem one_mem_symmetricKernel : (1 : Module.End ℂ (X → ℂ)) ∈ symmetricKernel X := by
  intro u v
  simp only [Module.End.one_apply,Pi.single_apply,eq_comm]

theorem permutation_mem_symmetricKernel (T : Module.End ℂ (X → ℂ)) (e : X → X)
    (he : Function.Involutive e) (hT : ∀ f x, T f x=f (e x)) :
    T ∈ symmetricKernel X := by
  intro u v
  rw [hT,hT]
  have hiff : e u=v ↔ e v=u := by
    constructor
    · intro h; rw [← h,he]
    · intro h; rw [← h,he]
  simp only [Pi.single_apply,hiff]

theorem sum_single_basis (g : X → ℂ) : (∑ w, g w • Pi.single w 1)=g := by
  funext x
  simp [Pi.single_apply]

theorem linear_apply_eq_sum (T : Module.End ℂ (X → ℂ)) (g : X → ℂ) (x : X) :
    T g x=∑ w, g w*T (Pi.single w 1) x := by
  conv_lhs => rw [← sum_single_basis X g]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem kernel_mul_left (B T : Module.End ℂ (X → ℂ)) (u v : X) :
    (kernelEquiv X).symm (B*T) (u,v)=B (fun w => (kernelEquiv X).symm T (w,v)) u := rfl

theorem kernel_mul_right (B T : Module.End ℂ (X → ℂ)) (hB : B ∈ symmetricKernel X)
    (u v : X) :
    (kernelEquiv X).symm (T*B) (u,v)=B (fun w => (kernelEquiv X).symm T (u,w)) v := by
  change T (B (Pi.single v 1)) u=B (fun w => T (Pi.single w 1) u) v
  rw [linear_apply_eq_sum X T,linear_apply_eq_sum X B]
  apply Finset.sum_congr rfl
  intro w _
  rw [hB w v,mul_comm]

end SymmetricKernel

variable {j s : ℕ}

theorem ambient_swap_symmetric (x y : Fin s) :
    ambientAction (j := j) (Equiv.swap x y) ∈ symmetricKernel (OrderedInjection j s) := by
  apply permutation_mem_symmetricKernel _ _ (permute (Equiv.swap x y))
  · intro u
    apply Function.Embedding.ext
    intro i
    exact Equiv.swap_apply_self x y (u i)
  · intro f u
    change f (permute (Equiv.swap x y)⁻¹ u)=_
    rw [Equiv.swap_inv]

theorem retained_swap_symmetric (x y : Fin j) :
    retainedAction (s := s) (Equiv.swap x y) ∈ symmetricKernel (OrderedInjection j s) := by
  apply permutation_mem_symmetricKernel _ _ (fun u => reindex u (Equiv.swap x y))
  · intro u
    apply Function.Embedding.ext
    intro i
    exact congrArg u (Equiv.swap_apply_self x y i)
  · intros; rfl

theorem birth_symmetric (j s : ℕ) :
    birthOperator j s ∈ symmetricKernel (OrderedInjection j s) := by
  have hA : orderedSwapSum (ambientRepresentation j s) ∈ symmetricKernel (OrderedInjection j s) := by
    apply Submodule.sum_mem
    intro x _
    apply Submodule.sum_mem
    intro y _
    by_cases he : x=y
    · rw [if_pos he]; exact Submodule.zero_mem _
    · rw [if_neg he]; exact ambient_swap_symmetric x y
  have hR : orderedSwapSum (retainedRepresentation j s) ∈ symmetricKernel (OrderedInjection j s) := by
    apply Submodule.sum_mem
    intro x _
    apply Submodule.sum_mem
    intro y _
    by_cases he : x=y
    · rw [if_pos he]; exact Submodule.zero_mem _
    · rw [if_neg he]; exact retained_swap_symmetric x y
  exact (symmetricKernel _).sub_mem
    ((symmetricKernel _).sub_mem
      ((symmetricKernel _).add_mem
        ((symmetricKernel _).smul_mem _ (one_mem_symmetricKernel _))
        ((symmetricKernel _).smul_mem _ hA))
      ((symmetricKernel _).smul_mem _ hR))
    ((symmetricKernel _).smul_mem _ (one_mem_symmetricKernel _))

theorem kernel_birth_anticommutator (T : Module.End ℂ (OrderedInjection j s → ℂ))
    (u v : OrderedInjection j s) :
    (kernelEquiv (OrderedInjection j s)).symm
      (birthOperator j s*T+T*birthOperator j s) (u,v)=
      (2*j : ℂ)*(kernelEquiv _).symm T (u,v)+
        replacementSum (fun w => (kernelEquiv _).symm T (u,w)) v+
        replacementSum (fun w => (kernelEquiv _).symm T (w,v)) u := by
  rw [map_add]
  change (kernelEquiv _).symm (birthOperator j s*T) (u,v)+
    (kernelEquiv _).symm (T*birthOperator j s) (u,v)=_
  rw [kernel_mul_left,kernel_mul_right _ _ _ (birth_symmetric j s),
    birthOperator_apply,birthOperator_apply]
  ring

end
end WeldedPath.OrderedMatching

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive Incidence
open scoped BigOperators

variable {j s : ℕ}

def recordSpace (s j : ℕ) : Submodule ℂ (Hil (InjDb s)) where
  carrier := {ψ | ∀ I, I.size≠j → ψ I=0}
  zero_mem' := by intro I hI; rfl
  add_mem' := by
    intro ψ φ hψ hφ I hI
    change ψ I+φ I=0
    rw [hψ I hI,hφ I hI,add_zero]
  smul_mem' := by
    intro c ψ hψ I hI
    change c*ψ I=0
    rw [hψ I hI,mul_zero]

theorem mem_recordSpace_iff (ψ : Hil (InjDb s)) :
    ψ∈recordSpace s j ↔ recordLevel s j ψ=ψ := by
  constructor
  · intro hψ
    ext I
    rw [recordLevel,diagProj_apply]
    by_cases hI : I.size=j
    · rw [if_pos hI]
    · rw [if_neg hI,hψ I hI]
  · intro hψ I hI
    have he := congrArg (fun v : Hil (InjDb s) => v I) hψ
    simpa only [recordLevel,diagProj_apply,if_neg hI] using he.symm

def levelFunctionEquiv (s j : ℕ) : recordSpace s j ≃ₗ[ℂ] (MatchingLevel s j → ℂ) where
  toFun ψ I := ψ.1 I.1
  invFun f := ⟨WithLp.toLp 2 (fun I => if h : I.size=j then f ⟨I,h⟩ else 0),by
    intro I hI
    exact dif_neg hI⟩
  left_inv ψ := by
    apply Subtype.ext
    ext I
    change (if h : I.size=j then ψ.1 I else 0)=ψ.1 I
    by_cases hI : I.size=j
    · rw [dif_pos hI]
    · rw [dif_neg hI,ψ.2 I hI]
  right_inv f := by funext I; exact dif_pos I.2
  map_add' ψ φ := rfl
  map_smul' c ψ := rfl

def databaseCommutantEquiv (s j : ℕ) : recordSpace s j ≃ₗ[ℂ] retainedCommutant j s :=
  (levelFunctionEquiv s j).trans (matchingCommutantEquiv j s)

def databaseOperator (ψ : Hil (InjDb s)) : Module.End ℂ (OrderedInjection j s → ℂ) :=
  kernelEquiv (OrderedInjection j s) (fun p => ψ (database p.1 p.2))

theorem databaseOperator_zero (s j : ℕ) : databaseOperator (j := j) (0 : Hil (InjDb s))=0 :=
  map_zero (kernelEquiv (OrderedInjection j s))

theorem databaseOperator_smul (c : ℂ) (ψ : Hil (InjDb s)) :
    databaseOperator (j := j) (c • ψ)=c • databaseOperator (j := j) ψ :=
  map_smul (kernelEquiv (OrderedInjection j s)) c _


theorem databaseOperator_injective_on_level (ψ φ : Hil (InjDb s))
    (hψ : ψ∈recordSpace s j) (hφ : φ∈recordSpace s j)
    (he : databaseOperator (j := j) ψ=databaseOperator (j := j) φ) : ψ=φ := by
  have hh : databaseCommutantEquiv s j ⟨ψ,hψ⟩=databaseCommutantEquiv s j ⟨φ,hφ⟩ :=
    Subtype.ext he
  exact congrArg Subtype.val ((databaseCommutantEquiv s j).injective hh)

theorem laplacian_ket_zero (I : InjDb s) (hI : I.size≠j) :
    laplacian s j (ket I)=0 := by
  have hd (x : Fin s) : domainMap s j x (ket I)=0 := by
    simp only [domainMap,ContinuousLinearMap.comp_apply,recordLevel_ket,if_neg hI,map_zero]
  have hi (x : Fin s) : imageMap s j x (ket I)=0 := by
    have hh : domainMap s j x (ket I.symm)=0 := by
      simp only [domainMap,ContinuousLinearMap.comp_apply,recordLevel_ket,size_symm,
        if_neg hI,map_zero]
    simpa only [imageMap,ContinuousLinearMap.comp_apply,flipDb_ket,hh,map_zero]
  simp only [laplacian,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,hd,hi,map_zero,add_zero,Finset.sum_const_zero]

theorem laplacian_mem_recordSpace (ψ : Hil (InjDb s)) :
    laplacian s j ψ ∈ recordSpace s j := by
  intro I hI
  rw [← inner_ket,← laplacian_adjoint s j,ContinuousLinearMap.adjoint_inner_right,
    laplacian_ket_zero I hI,inner_zero_left]

theorem databaseOperator_laplacian (ψ : Hil (InjDb s)) :
    databaseOperator (j := j) (laplacian s j ψ)=
      (1/((s-j+1 : ℕ) : ℂ)) •
        (birthOperator j s*databaseOperator (j := j) ψ+
          databaseOperator (j := j) ψ*birthOperator j s) := by
  apply (kernelEquiv (OrderedInjection j s)).symm.injective
  funext p
  obtain ⟨u,v⟩ := p
  rw [map_smul]
  change (kernelEquiv _).symm (databaseOperator (j := j) (laplacian s j ψ)) (u,v)=
    (1/((s-j+1 : ℕ) : ℂ))*((kernelEquiv _).symm
      (birthOperator j s*databaseOperator (j := j) ψ+
        databaseOperator (j := j) ψ*birthOperator j s) (u,v))
  rw [kernel_birth_anticommutator]
  simp only [databaseOperator,LinearEquiv.symm_apply_apply]
  exact laplacian_database_apply u v ψ

theorem laplacian_zero_iff (ψ : Hil (InjDb s)) :
    laplacian s j ψ=0 ↔
      birthOperator j s*databaseOperator (j := j) ψ+
        databaseOperator (j := j) ψ*birthOperator j s=0 := by
  have hc : (1/((s-j+1 : ℕ) : ℂ))≠0 := by
    exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
  constructor
  · intro hψ
    have he := databaseOperator_laplacian (j := j) ψ
    rw [hψ] at he
    have hz : databaseOperator (j := j) (0 : Hil (InjDb s))=0 := by
      unfold databaseOperator
      exact map_zero _
    rw [hz] at he
    exact (smul_eq_zero.mp he.symm).resolve_left hc
  · intro hψ
    apply databaseOperator_injective_on_level _ _ (laplacian_mem_recordSpace ψ)
      (recordSpace s j).zero_mem
    rw [databaseOperator_laplacian,hψ,smul_zero]
    symm
    unfold databaseOperator
    exact map_zero _

def databaseHarmonic (s j : ℕ) : Submodule ℂ (Hil (InjDb s)) :=
  recordSpace s j ⊓ (laplacian s j).toLinearMap.ker

def databaseHarmonicEquiv (s j : ℕ) : databaseHarmonic s j ≃ₗ[ℂ] matchingHarmonic j s where
  toFun ψ := ⟨databaseOperator (j := j) ψ.1,
    (laplacian_zero_iff ψ.1).mp ψ.2.2,(databaseCommutantEquiv s j ⟨ψ.1,ψ.2.1⟩).2⟩
  invFun T := ⟨((databaseCommutantEquiv s j).symm ⟨T.1,T.2.2⟩).1,by
    refine ⟨((databaseCommutantEquiv s j).symm ⟨T.1,T.2.2⟩).2,?_⟩
    apply (laplacian_zero_iff _).mpr
    have he : databaseOperator (j := j) (((databaseCommutantEquiv s j).symm ⟨T.1,T.2.2⟩).1)=T.1 :=
      congrArg Subtype.val ((databaseCommutantEquiv s j).apply_symm_apply ⟨T.1,T.2.2⟩)
    rw [he]
    exact T.2.1⟩
  left_inv ψ := by
    apply Subtype.ext
    change (((databaseCommutantEquiv s j).symm
      (databaseCommutantEquiv s j ⟨ψ.1,ψ.2.1⟩)).1 : Hil (InjDb s))=ψ.1
    exact congrArg (fun v : recordSpace s j => v.1)
      ((databaseCommutantEquiv s j).symm_apply_apply ⟨ψ.1,ψ.2.1⟩)
  right_inv T := by
    apply Subtype.ext
    change (databaseCommutantEquiv s j
      ((databaseCommutantEquiv s j).symm ⟨T.1,T.2.2⟩)).1=T.1
    exact congrArg (fun U : retainedCommutant j s => U.1)
      ((databaseCommutantEquiv s j).apply_symm_apply ⟨T.1,T.2.2⟩)
  map_add' ψ φ := by
    apply Subtype.ext
    exact map_add (kernelEquiv _) _ _
  map_smul' c ψ := by
    apply Subtype.ext
    exact map_smul (kernelEquiv _) c _

theorem databaseHarmonic_finrank (hsmall : j ≤ s-j) :
    Module.finrank ℂ (databaseHarmonic s j)=Module.finrank ℂ (Hlevel s j) := by
  rw [(databaseHarmonicEquiv s j).finrank_eq,matchingHarmonic_finrank hsmall,
    CompletionDimension.Hlevel_finrank s j (by omega)]
  exact (Finset.sum_subtype (Finset.univ.filter
    (fun μ : OAI.PartialPermutation.DiagramCounting.Shape s => μ.1.rowLen 0=s-j))
    (p := fun μ : OAI.PartialPermutation.DiagramCounting.Shape s => μ.1.rowLen 0=s-j)
    (by simp) (fun μ => (Module.finrank ℂ (OAI.PartialPermutation.YoungTabloid.spechtSub μ.1).toSubmodule)^2)).symm

theorem Gam_adjoint_range_le_harmonic (s j : ℕ) :
    (ContinuousLinearMap.adjoint (Gam s j)).range ≤ databaseHarmonic s j := by
  rintro ψ ⟨v,rfl⟩
  exact ⟨fun I hI => IntertwinerPartial.Gam_adjoint_support s j v I hI,
    laplacian_Gam_adjoint_zero j v⟩

/-- The common zero space of the domain/image incidence maps, within the actual
size-j database sector, is exactly the completion-adjoint range. -/
theorem databaseHarmonic_eq_Gam_adjoint_range (hsmall : j ≤ s-j) :
    databaseHarmonic s j=(ContinuousLinearMap.adjoint (Gam s j)).range := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (Gam_adjoint_range_le_harmonic s j)
  rw [databaseHarmonic_finrank hsmall]
  have he := LinearMap.finrank_range_adjoint (Gam s j).toLinearMap
  rw [ContinuousLinearMap.adjoint_toLinearMap] at he
  exact he.trans (congrArg
    (fun K : Submodule ℂ (Hil (Equiv.Perm (Fin s))) => Module.finrank ℂ K)
    (CompletionLevels.Gam_range_eq s j))

end
end WeldedPath.OrderedMatching

namespace WeldedPath.OrderedMatching

noncomputable section
open Classical InjDb Incidence YoungStripContent

variable {j s : ℕ}

theorem birth_excess_gap (hsmall : j ≤ s-j) (p : Channel j s) :
    0 ≤ (excess p.2.1.1 p.1.1 (s-j) : ℝ) ∧
      ((excess p.2.1.1 p.1.1 (s-j) : ℝ)=0 ∨
        ((s-j : ℕ) : ℝ)-j+1 ≤ (excess p.2.1.1 p.1.1 (s-j) : ℝ)) := by
  have hj : p.2.1.1.card=j := p.2.1.2
  have hs : p.1.1.card=s := p.1.2
  obtain ⟨hn,hzero,hgap⟩ := excess_gap p.2.2 (s-j) (by omega) (by simpa only [hj] using hsmall)
  constructor
  · exact_mod_cast hn
  · by_cases hrow : p.1.1.rowLen 0=s-j
    · left
      exact_mod_cast hzero.mpr hrow
    · right
      have he := hgap hrow
      rw [hj] at he
      exact_mod_cast he

/-- Every nonzero eigenvalue of the literal incidence Laplacian on the actual
size-j database space is at least one half. -/
theorem incidence_eigenvalue_gap (hsmall : 3*j ≤ s+1)
    (ψ : Hil (InjDb s)) (hψ : ψ∈recordSpace s j) (hne : ψ≠0)
    (c : ℝ) (he : laplacian s j ψ=(c : ℂ) • ψ) :
    0 ≤ c ∧ (c=0 ∨ (1/2 : ℝ) ≤ c) := by
  have hjs : j ≤ s := by omega
  have hhalf : j ≤ s-j := by omega
  let T := databaseOperator (j := j) ψ
  have hT : T≠0 := by
    intro hz
    apply hne
    exact databaseOperator_injective_on_level ψ 0 hψ (recordSpace s j).zero_mem
      (hz.trans (databaseOperator_zero s j).symm)
  have hd : ((s-j+1 : ℕ) : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hdR : (0 : ℝ) < ((s-j+1 : ℕ) : ℝ) := by positivity
  have hh := databaseOperator_laplacian (j := j) ψ
  rw [he,databaseOperator_smul] at hh
  have hanti : birthOperator j s*T+T*birthOperator j s=
      ((((s-j+1 : ℕ) : ℝ)*c : ℝ) : ℂ) • T := by
    have ha := congrArg (fun A : Module.End ℂ (OrderedInjection j s → ℂ) =>
      ((s-j+1 : ℕ) : ℂ) • A) hh
    rw [smul_smul,smul_smul,mul_one_div_cancel hd,one_smul] at ha
    simpa only [Complex.ofReal_mul,Complex.ofReal_natCast] using ha.symm
  have hg := DiagonalAnticommutator.real_eigenvalue_gap
    (flatInjectionEquiv hjs) (birthOperator j s)
    (fun p : Channel j s => (excess p.2.1.1 p.1.1 (s-j) : ℝ))
    (fun f p => by simpa only [Complex.ofReal_intCast] using flatInjection_birth hjs f p)
    (((s-j : ℕ) : ℝ)-j+1) (birth_excess_gap hhalf) T hT
    (((s-j+1 : ℕ) : ℝ)*c) hanti
  have htwice : (2 : ℝ)*j ≤ ((s-j : ℕ) : ℝ)+1 := by
    exact_mod_cast (show 2*j ≤ s-j+1 by omega)
  have hdcast : ((s-j+1 : ℕ) : ℝ)=((s-j : ℕ) : ℝ)+1 := by norm_cast
  constructor
  · nlinarith [hg.1]
  · rcases hg.2 with hz | hgap
    · left
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hdR)
    · right
      nlinarith

end
end WeldedPath.OrderedMatching





end

-- Solutions.FiniteSpectralGap
section

namespace WeldedPath.FiniteSpectralGap

noncomputable section
open Classical
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem coercive_on_kernel_orthogonal (T : Module.End ℂ E) (hT : T.IsSymmetric) (δ : ℝ)
    (hgap : ∀ (c : ℝ) (v : E),v≠0 → T v=(c : ℂ) • v → c=0 ∨ δ ≤ c)
    (v : E) (hv : v∈(LinearMap.ker T)ᗮ) :
    δ*‖v‖^2 ≤ (inner ℂ v (T v)).re := by
  let b := hT.eigenvectorBasis rfl
  let c := hT.eigenvalues rfl
  have he (i : Fin (Module.finrank ℂ E)) : T (b i)=(c i : ℂ) • b i :=
    hT.apply_eigenvectorBasis rfl i
  have hg (i : Fin (Module.finrank ℂ E)) : c i=0 ∨ δ ≤ c i :=
    hgap (c i) (b i) (b.toBasis.ne_zero i) (he i)
  have hz (i : Fin (Module.finrank ℂ E)) (hi : c i=0) : b.repr v i=0 := by
    rw [b.repr_apply_apply]
    apply ((LinearMap.ker T).mem_orthogonal v).mp hv
    change T (b i)=0
    rw [he,hi,Complex.ofReal_zero,zero_smul]
  have hdiag (i : Fin (Module.finrank ℂ E)) :
      b.repr (T v) i=(c i : ℂ)*b.repr v i := hT.eigenvectorBasis_apply_self_apply rfl v i
  rw [← b.repr.norm_map v,EuclideanSpace.norm_sq_eq,Finset.mul_sum,
    ← b.repr.inner_map_map v (T v),PiLp.inner_apply,Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hdiag]
  have hi : (inner ℂ (b.repr v i) ((c i : ℂ)*b.repr v i)).re=c i*‖b.repr v i‖^2 := by
    change (inner ℂ (b.repr v i) ((c i : ℂ) • b.repr v i)).re=_
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    change ((c i : ℂ)*(‖b.repr v i‖ : ℂ)^2).re=_
    simp [pow_two]
  rw [hi]
  rcases hg i with hzero | hpos
  · rw [hz i hzero]
    simp
  · exact mul_le_mul_of_nonneg_right hpos (sq_nonneg _)


end
end WeldedPath.FiniteSpectralGap


end

-- Solutions.WeldedPathIncidenceGap
section

namespace WeldedPath.Incidence

noncomputable section
open Classical OrderedMatching HilbertSupport
open scoped BigOperators

variable {s j : ℕ}

theorem laplacian_recordLevel (ψ : Hil (InjDb s)) :
    laplacian s j (recordLevel s j ψ)=laplacian s j ψ := by
  rw [← sum_basis ψ]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  rw [recordLevel_ket]
  by_cases hI : I.size=j
  · rw [if_pos hI]
  · rw [if_neg hI,map_zero,laplacian_ket_zero I hI]

theorem laplacian_eigenvalue_gap (hsmall : 3*j ≤ s+1) (c : ℝ) (v : Hil (InjDb s))
    (hne : v≠0) (he : laplacian s j v=(c : ℂ) • v) :
    c=0 ∨ (1/2 : ℝ) ≤ c := by
  by_cases hc : c=0
  · exact Or.inl hc
  have hv : v∈recordSpace s j := by
    intro I hI
    have hz := laplacian_mem_recordSpace v I hI
    have hi := congrArg (fun w : Hil (InjDb s) => w I) he
    change laplacian s j v I=(c : ℂ)*v I at hi
    rw [hz] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left (Complex.ofReal_ne_zero.mpr hc)
  exact (incidence_eigenvalue_gap hsmall v hv hne c he).2

theorem incidence_coercive (hsmall : 3*j ≤ s+1) (ψ : Hil (InjDb s))
    (hψ : ψ∈recordSpace s j)
    (horth : ψ∈(ContinuousLinearMap.adjoint (Gam s j)).rangeᗮ) :
    (1/2 : ℝ)*‖ψ‖^2 ≤ (inner ℂ ψ (laplacian s j ψ)).re := by
  have hv : ψ∈(laplacian s j).toLinearMap.kerᗮ := by
    apply ((laplacian s j).toLinearMap.ker.mem_orthogonal _).mpr
    intro w hw
    have hw' : recordLevel s j w∈databaseHarmonic s j := by
      constructor
      · intro I hI
        rw [recordLevel,diagProj_apply,if_neg hI]
      · change laplacian s j (recordLevel s j w)=0
        rw [laplacian_recordLevel]
        exact hw
    rw [databaseHarmonic_eq_Gam_adjoint_range (by omega)] at hw'
    have hz := (((ContinuousLinearMap.adjoint (Gam s j)).range).mem_orthogonal ψ).mp
      horth (recordLevel s j w) hw'
    have hi := ContinuousLinearMap.adjoint_inner_left (recordLevel s j) ψ w
    rw [recordLevel_adjoint,(mem_recordSpace_iff ψ).mp hψ,hz] at hi
    exact hi.symm
  exact FiniteSpectralGap.coercive_on_kernel_orthogonal (laplacian s j).toLinearMap
    (laplacian_positive s j).toLinearMap.isSymmetric (1/2)
    (laplacian_eigenvalue_gap hsmall) ψ hv

/-- The actual domain/image incidence energy controls squared distance from the
completion-adjoint range, with the source's dimension-free factor two. -/
theorem incidence_distance_bound (hsmall : 3*j ≤ s+1) (ψ : Hil (InjDb s))
    (hψ : ψ∈recordSpace s j) :
    ‖ψ-((ContinuousLinearMap.adjoint (Gam s j)).range).starProjection ψ‖^2 ≤
      2*∑ x : Fin s, (‖domainMap s j x ψ‖^2+‖imageMap s j x ψ‖^2) := by
  let K := (ContinuousLinearMap.adjoint (Gam s j)).range
  have hp : K.starProjection ψ∈databaseHarmonic s j :=
    Gam_adjoint_range_le_harmonic s j (K.starProjection_apply_mem ψ)
  have hzero : laplacian s j (K.starProjection ψ)=0 := hp.2
  have hinner : inner ℂ (K.starProjection ψ) (laplacian s j ψ)=0 := by
    have hi := (laplacian_positive s j).inner_left_eq_inner_right (K.starProjection ψ) ψ
    rw [hzero,inner_zero_left] at hi
    exact hi.symm
  have h := incidence_coercive hsmall (ψ-K.starProjection ψ)
    ((recordSpace s j).sub_mem hψ hp.1) (K.sub_starProjection_mem_orthogonal ψ)
  simp only [map_sub,hzero,sub_zero,inner_sub_left,hinner,zero_sub,neg_zero,sub_zero] at h
  rw [laplacian_energy] at h
  nlinarith


end
end WeldedPath.Incidence


end

open Classical WeldedPath
open scoped BigOperators

theorem solution (s j : ℕ) (hsmall : 3*j ≤ s+1)
    (ψ : Hil (InjDb s)) (hsupport : ∀ I : InjDb s, I.size ≠ j → ψ I=0) :
    let D : Fin s → Hil (InjDb s) →L[ℂ] Hil (InjDb s) := fun x =>
      ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x=none),
        ketBra (ket I) (plusState I x)
    ((∀ x : Fin s, D x ψ=0 ∧ D x (flipDb s ψ)=0) ↔
      ψ∈(ContinuousLinearMap.adjoint (Gam s j)).range) ∧
    ‖ψ-((ContinuousLinearMap.adjoint (Gam s j)).range).starProjection ψ‖^2 ≤
      2*∑ x : Fin s, (‖D x ψ‖^2+‖D x (flipDb s ψ)‖^2) := by
  let D : Fin s → Hil (InjDb s) →L[ℂ] Hil (InjDb s) := fun x =>
    ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x=none),
      ketBra (ket I) (plusState I x)
  change ((∀ x : Fin s, D x ψ=0 ∧ D x (flipDb s ψ)=0) ↔
    ψ∈(ContinuousLinearMap.adjoint (Gam s j)).range) ∧ _
  have hp : ψ∈OrderedMatching.recordSpace s j := hsupport
  have hf : flipDb s ψ∈OrderedMatching.recordSpace s j := by
    intro I hI
    rw [CompressedPrimitive.flipDb_apply]
    exact hsupport I.symm (by simpa only [CompressedPrimitive.size_symm] using hI)
  have hD (x : Fin s) (v : Hil (InjDb s)) (hv : v∈OrderedMatching.recordSpace s j) :
      D x v=Incidence.domainMap s j x v := by
    change (∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x=none),
      ketBra (ket I) (plusState I x)) v=
      ContinuousLinearMap.adjoint (CompressedPrimitive.insertionBlock s x)
        (Incidence.recordLevel s j v)
    rw [← CompressedPrimitive.insertionBlock_adjoint,
      (OrderedMatching.mem_recordSpace_iff v).mp hv]
  have hI (x : Fin s) : Incidence.imageMap s j x ψ=flipDb s (D x (flipDb s ψ)) := by
    change flipDb s (Incidence.domainMap s j x (flipDb s ψ))=_
    rw [← hD x (flipDb s ψ) hf]
  constructor
  · constructor
    · intro hz
      have hzero : Incidence.laplacian s j ψ=0 := by
        simp only [Incidence.laplacian,ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
          ← hD _ ψ hp,hI,(hz _).1,(hz _).2,map_zero,add_zero,Finset.sum_const_zero]
      rw [← OrderedMatching.databaseHarmonic_eq_Gam_adjoint_range (by omega : j ≤ s-j)]
      exact ⟨hp,hzero⟩
    · rintro ⟨v,hv⟩ x
      have hd : Incidence.domainMap s j x ψ=0 := by
        rw [← hv]
        exact Incidence.domainMap_Gam_adjoint_zero j x v
      have hi : Incidence.imageMap s j x ψ=0 := by
        rw [← hv]
        exact Incidence.imageMap_Gam_adjoint_zero j x v
      refine ⟨(hD x ψ hp).trans hd,?_⟩
      rw [hI] at hi
      have hh := congrArg (flipDb s) hi
      simpa only [CompressedPrimitive.flipDb_flip,map_zero] using hh
  · have hb := Incidence.incidence_distance_bound hsmall ψ hp
    simpa only [← hD _ ψ hp,hI,EncodedOracleUnitary.flipDb_norm] using hb
