-- Prove2me | solution 1 for TwoReLULayers.DepthCollapse.max_rational_network
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:23:01.755036+00:00
-- url     : https://prove2.me/submissions/2f4a4c80-8102-4731-97ca-c1536cf3bf73

import Mathlib
import Definitions.Def_TwoReLULayers_DepthCollapse_Model
import Theorems.Thm_TwoReLULayers_DepthCollapse_network_linear_combination

-- Adapted from kilianar/two-layer-formalization, commit a275280,
-- with rational coefficient preservation and mission evaluator bridges.

-- Source module: Solutions/AuthorDefs.lean


/-!
# Basic definitions

This file collects the definitions shared by the formalization of the statement that
`max(x₁, …, xₙ)` can be computed by a ReLU network with two hidden layers.

* `relu`: the rectified linear unit.
* `reluNet ι k`: the space of functions `(ι → ℝ) → ℝ` computed by ReLU networks with `k` hidden
  layers.
* `supportFun K`: the support function `x ↦ sup_{p ∈ K} ⟪p, x⟫` of a set `K`.
* `maxLin W`, `maxSpan ι k`: maxima of finitely many linear forms, and the span of those maxima
  involving at most `k` linear forms.
* `Constraint ι`, `hpoly cs`: affine half-spaces and polytopes in the hyperplane `∑ pᵢ = 1`
  given by finitely many such half-spaces.
* `facetPoly v cs`, `pyr v cs`: polytopes in the facet hyperplane `{∑ pᵢ = 1, p_v = 0}` and the
  pyramids over them with apex `e_v`.
-/

open Finset

namespace AuthorReal

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The rectified linear unit. -/
def relu (x : ℝ) : ℝ := max x 0

/-- The functions `(ι → ℝ) → ℝ` computable by ReLU networks with `k` hidden layers
(written `ReLU_{n,k}` in the paper).

* `reluNet ι 0` is the space of affine functions, spanned by the constant function `1` and the
  linear forms `x ↦ ⟪a, x⟫`;
* `reluNet ι (k + 1)` is spanned by the constant function `1` and the functions `relu ∘ g` with
  `g ∈ reluNet ι k`.

Taking spans at every level accounts for the affine maps between the layers and for the
affine output map; see `reluNet.exists_twoLayerNet` for the explicit form when `k = 2`. -/
def reluNet (ι : Type*) [Fintype ι] : ℕ → Submodule ℝ ((ι → ℝ) → ℝ)
  | 0 => Submodule.span ℝ (insert (fun _ ↦ 1) (Set.range fun (a : ι → ℝ) (x : ι → ℝ) ↦ a ⬝ᵥ x))
  | k + 1 =>
    Submodule.span ℝ (insert (fun _ ↦ 1) {f | ∃ g ∈ reluNet ι k, f = fun x ↦ relu (g x)})

/-- The support function `x ↦ sup_{p ∈ K} ⟪p, x⟫` of a set `K`.
It is only meaningful for bounded nonempty `K`; for `K = ∅` it is `0`. -/
def supportFun (K : Set (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  sSup ((fun p ↦ p ⬝ᵥ x) '' K)

/-- The maximum of the linear forms `x ↦ ⟪w, x⟫` for `w ∈ W` (and `0` if `W = ∅`). -/
def maxLin (W : Finset (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  if h : W.Nonempty then W.sup' h (· ⬝ᵥ x) else 0

/-- The span of all maxima of at most `k` linear forms. -/
def maxSpan (ι : Type*) [Fintype ι] (k : ℕ) : Submodule ℝ ((ι → ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ W : Finset (ι → ℝ), W.Nonempty ∧ W.card ≤ k ∧ f = maxLin W}

/-- An affine half-space `{p | ⟪a, p⟫ ≤ b}`. -/
@[ext]
structure Constraint (ι : Type*) where
  /-- The normal vector. -/
  a : ι → ℝ
  /-- The right hand side. -/
  b : ℝ

instance : DecidableEq (Constraint ι) := Classical.decEq _

/-- A constraint is nonconstant on the hyperplane `∑ pᵢ = 1` iff its normal vector is not
a multiple of the all-ones vector. -/
def Constraint.IsNonconst (c : Constraint ι) : Prop :=
  ∃ i j, c.a i ≠ c.a j

/-- The polytope `{p | ∑ pᵢ = 1, ⟪c.a, p⟫ ≤ c.b for all c ∈ cs}`. -/
def hpoly (cs : Finset (Constraint ι)) : Set (ι → ℝ) :=
  {p | ∑ i, p i = 1 ∧ ∀ c ∈ cs, c.a ⬝ᵥ p ≤ c.b}

/-- The polytope `{p | ∑ pᵢ = 1, p_v = 0, ⟪c.a, p⟫ ≤ c.b for all c ∈ cs}` in a facet hyperplane. -/
def facetPoly (v : ι) (cs : Finset (Constraint ι)) : Set (ι → ℝ) :=
  {p | ∑ i, p i = 1 ∧ p v = 0 ∧ ∀ c ∈ cs, c.a ⬝ᵥ p ≤ c.b}

variable [DecidableEq ι]

/-- Homogenization of a facet constraint with respect to the apex `e_v`:
`⟪a, p⟫ ≤ b` on `{p_v = 0}` becomes `∑_{i ≠ v} aᵢ pᵢ ≤ b (1 - p_v)`. -/
def Constraint.homog (v : ι) (c : Constraint ι) : Constraint ι :=
  ⟨Function.update c.a v c.b, c.b⟩

/-- The constraints of the pyramid with apex `e_v` over `facetPoly v cs`. -/
def pyrCons (v : ι) (cs : Finset (Constraint ι)) : Finset (Constraint ι) :=
  insert ⟨-Pi.single v 1, 0⟩ (insert ⟨Pi.single v 1, 1⟩ (cs.image (Constraint.homog v)))

/-- The pyramid with apex `e_v` over `facetPoly v cs`. -/
def pyr (v : ι) (cs : Finset (Constraint ι)) : Set (ι → ℝ) :=
  hpoly (pyrCons v cs)

/-! ### The concrete polytopes of the proof -/

/-- The constraints `pᵢ ≥ 0` of the standard simplex. -/
def simplexCons : Finset (Constraint ι) :=
  univ.image fun i ↦ ⟨-Pi.single i 1, 0⟩

/-- The standard simplex `Δ = conv {e_i}`. -/
def simplex : Set (ι → ℝ) :=
  hpoly (simplexCons : Finset (Constraint ι))

/-- The constraints of `T_v = pyr_{q_C}(Δ_{-v})`, i.e. `p ∈ Δ` and `p_v ≤ p_w` for `w ∈ C`. -/
def tCons (C : Finset ι) (v : ι) : Finset (Constraint ι) :=
  simplexCons ∪ (C.erase v).image fun w ↦ ⟨Pi.single v 1 - Pi.single w 1, 0⟩

/-- The constraints of the dilated facet `Q_{v,R}`: `pᵢ ≥ 0` for `i ∈ R` and `pᵢ ≥ -1` for the
remaining `i ≠ v`. -/
def qCons (v : ι) (R : Finset ι) : Finset (Constraint ι) :=
  (univ.erase v).image fun i ↦ if i ∈ R then ⟨-Pi.single i 1, 0⟩ else ⟨-Pi.single i 1, 1⟩

/-- The indicator vector of a finite set. -/
def indVec (S : Finset ι) : ι → ℝ :=
  fun i ↦ if i ∈ S then 1 else 0

/-- The orderings of a finite set, as lists. -/
def orderings (X : Finset ι) : Finset (List ι) :=
  X.toList.permutations.toFinset

/-- The constraints of the parallelepiped `B_{π,M}` read along the list `x :: l`, where `pre` is
the set of coordinates already visited: if `x ∈ M` we require `0 ≤ ∑_{pre} p ≤ 1`, otherwise
`-1 ≤ p_x ≤ 0`. -/
def boxCons (M : Finset ι) : Finset ι → List ι → Finset (Constraint ι)
  | _, [] => ∅
  | pre, x :: l =>
    (if x ∈ M then {⟨-indVec pre, 0⟩, ⟨indVec pre, 1⟩}
      else {⟨-Pi.single x 1, 1⟩, ⟨Pi.single x 1, 0⟩}) ∪ boxCons M (insert x pre) l

/-- The constraints of the parallelepiped `B_{π,M}` for the ordering `π = l`. -/
def boxConsL (M : Finset ι) : List ι → Finset (Constraint ι)
  | [] => ∅
  | h :: t => boxCons M {h} t

/-- The admissible markings `M` for the ordering `l`: subsets of the positions after the first. -/
def markings (l : List ι) : Finset (Finset ι) :=
  l.tail.toFinset.powerset

/-- The hyperplanes in the facet `{p_v = 0}` that a point has to avoid in order to be generic for
the thermostat lemma: `pᵢ = 0`, `pᵢ = -1` and `∑_{S} p = 0`, `∑_{S} p = 1` for nonempty proper
subsets `S` of the coordinates `≠ v`. -/
def facetGen (v : ι) : Finset (Constraint ι) :=
  ((univ.erase v).image fun i ↦ (⟨Pi.single i 1, 0⟩ : Constraint ι)) ∪
  ((univ.erase v).image fun i ↦ (⟨Pi.single i 1, -1⟩ : Constraint ι)) ∪
  (((univ.erase v).powerset.filter fun S ↦ S.Nonempty ∧ S ≠ univ.erase v).image
    fun S ↦ (⟨indVec S, 0⟩ : Constraint ι)) ∪
  (((univ.erase v).powerset.filter fun S ↦ S.Nonempty ∧ S ≠ univ.erase v).image
    fun S ↦ (⟨indVec S, 1⟩ : Constraint ι))

/-- The signed number `(-1)^(s-1) s! (m-s)!` of thermostat walks. -/
def psi (m s : ℕ) : ℝ :=
  (-1) ^ (s - 1) * (s.factorial : ℝ) * ((m - s).factorial : ℝ)

end

end AuthorReal

-- Source module: Solutions/AuthorNetwork.lean


/-!
# ReLU networks with `k` hidden layers

We prove closure properties of the hierarchy `reluNet ι k` of functions computable by ReLU
networks with `k` hidden layers:

* `reluNet.mono`: `reluNet ι k ≤ reluNet ι l` for `k ≤ l`;
* `reluNet.relu_mem`, `reluNet.max_mem`: applying `relu`, or taking the maximum of two functions,
  costs one hidden layer;
* `reluNet.comp_linearMap`: the hierarchy is closed under precomposition with linear maps.

Finally, `reluNet.exists_twoLayerNet` shows that every function in `reluNet ι 2` is computed by an
explicit network `x ↦ w₃ ⬝ᵥ relu (W₂ *ᵥ relu (W₁ *ᵥ x + b₁) + b₂) + b₃`.
-/

open Finset Matrix

namespace AuthorReal

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

namespace reluNet

theorem one_mem (k : ℕ) : (fun _ ↦ (1 : ℝ)) ∈ reluNet ι k := by
  cases k <;> exact Submodule.subset_span (Set.mem_insert _ _)

/-- Constant functions are computed by ReLU networks of any depth. -/
theorem const_mem (k : ℕ) (c : ℝ) : (fun _ ↦ c) ∈ reluNet ι k := by
  convert Submodule.smul_mem _ c (one_mem (ι := ι) k) using 1
  funext x
  simp

/-- Applying `relu` costs one hidden layer. -/
theorem relu_mem {k : ℕ} {g : (ι → ℝ) → ℝ} (hg : g ∈ reluNet ι k) :
    (fun x ↦ relu (g x)) ∈ reluNet ι (k + 1) :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨g, hg, rfl⟩)

/-- Linear forms are computed without hidden layers. -/
theorem linear_mem_zero (a : ι → ℝ) : (fun x ↦ a ⬝ᵥ x) ∈ reluNet ι 0 :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨a, rfl⟩)

/-- Affine functions are computed without hidden layers. -/
theorem affine_mem_zero (a : ι → ℝ) (b : ℝ) : (fun x ↦ a ⬝ᵥ x + b) ∈ reluNet ι 0 :=
  add_mem (linear_mem_zero a) (const_mem 0 b)

theorem relu_sub_relu_neg (y : ℝ) : relu y - relu (-y) = y := by
  simp only [relu]
  rcases le_total y 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

/-- A function computed with `k` hidden layers is also computed with `k + 1` hidden layers. -/
theorem le_succ (k : ℕ) : reluNet ι k ≤ reluNet ι (k + 1) := by
  induction k with
  | zero =>
    refine Submodule.span_le.2 ?_
    rintro f (rfl | ⟨a, rfl⟩)
    · exact one_mem 1
    · have h := sub_mem (relu_mem (linear_mem_zero a)) (relu_mem (linear_mem_zero (-a)))
      have he : ((fun x ↦ relu (a ⬝ᵥ x)) - fun x ↦ relu (-a ⬝ᵥ x)) = fun x ↦ a ⬝ᵥ x := by
        funext x
        simp only [Pi.sub_apply, neg_dotProduct, relu_sub_relu_neg]
      rw [he] at h
      exact h
  | succ k ih =>
    refine Submodule.span_le.2 ?_
    rintro f (rfl | ⟨g, hg, rfl⟩)
    · exact one_mem _
    · exact relu_mem (ih hg)

/-- The hierarchy `reluNet ι k` is monotone in the number `k` of hidden layers. -/
theorem mono : Monotone (reluNet ι) :=
  monotone_nat_of_le_succ le_succ

/-- Affine functions are computed by ReLU networks of any depth. -/
theorem affine_mem (k : ℕ) (a : ι → ℝ) (b : ℝ) : (fun x ↦ a ⬝ᵥ x + b) ∈ reluNet ι k :=
  mono (Nat.zero_le k) (affine_mem_zero a b)

/-- Linear forms are computed by ReLU networks of any depth. -/
theorem linear_mem (k : ℕ) (a : ι → ℝ) : (fun x ↦ a ⬝ᵥ x) ∈ reluNet ι k :=
  mono (Nat.zero_le k) (linear_mem_zero a)

/-- A single ReLU neuron is computed with one hidden layer. -/
theorem relu_affine_mem (a : ι → ℝ) (b : ℝ) : (fun x ↦ relu (a ⬝ᵥ x + b)) ∈ reluNet ι 1 :=
  relu_mem (affine_mem_zero a b)

/-- The maximum of two functions computed with `k` hidden layers is computed with `k + 1`
hidden layers, via `max g h = h + relu (g - h)`. -/
theorem max_mem {k : ℕ} {g h : (ι → ℝ) → ℝ} (hg : g ∈ reluNet ι k) (hh : h ∈ reluNet ι k) :
    (fun x ↦ max (g x) (h x)) ∈ reluNet ι (k + 1) := by
  convert add_mem (le_succ k hh) (relu_mem (sub_mem hg hh)) using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, relu]
  rw [← max_add_add_left, add_zero, add_sub_cancel]

/-- Precomposition with a linear map preserves the number of hidden layers. -/
theorem comp_linearMap (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) {k : ℕ} {f : (κ → ℝ) → ℝ}
    (hf : f ∈ reluNet κ k) : f ∘ A ∈ reluNet ι k := by
  classical
  induction k generalizing f with
  | zero =>
    induction hf using Submodule.span_induction with
    | mem f hf =>
      rcases hf with rfl | ⟨a, rfl⟩
      · exact one_mem 0
      · convert linear_mem_zero (a ᵥ* LinearMap.toMatrix' A) using 1
        funext x
        simp [← dotProduct_mulVec, LinearMap.toMatrix'_mulVec]
    | zero => exact zero_mem _
    | add f g _ _ hf hg => exact add_mem hf hg
    | smul r f _ hf => exact Submodule.smul_mem _ r hf
  | succ k ih =>
    induction hf using Submodule.span_induction with
    | mem f hf =>
      rcases hf with rfl | ⟨g, hg, rfl⟩
      · exact one_mem _
      · exact relu_mem (ih hg)
    | zero => exact zero_mem _
    | add f g _ _ hf hg => exact add_mem hf hg
    | smul r f _ hf => exact Submodule.smul_mem _ r hf

/-- Every function computed without hidden layers is affine. -/
theorem exists_affine {g : (ι → ℝ) → ℝ} (hg : g ∈ reluNet ι 0) :
    ∃ (a : ι → ℝ) (c : ℝ), g = fun x ↦ a ⬝ᵥ x + c := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨a, rfl⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨a, 0, by simp⟩
  | zero => exact ⟨0, 0, by funext x; simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨a, c, rfl⟩ := hf
    obtain ⟨a', c', rfl⟩ := hg
    refine ⟨a + a', c + c', ?_⟩
    funext x
    simp only [Pi.add_apply, add_dotProduct]
    ring
  | smul r f _ hf =>
    obtain ⟨a, c, rfl⟩ := hf
    refine ⟨r • a, r * c, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, smul_dotProduct, mul_add]

/-- Every function computed with one hidden layer is an explicit finite linear combination of
ReLU neurons plus a constant. -/
theorem exists_sum {g : (ι → ℝ) → ℝ} (hg : g ∈ reluNet ι 1) :
    ∃ (k : ℕ) (a : Fin k → ι → ℝ) (b d : Fin k → ℝ) (c : ℝ),
      g = fun x ↦ ∑ j, d j * relu (a j ⬝ᵥ x + b j) + c := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨g, hg, rfl⟩
    · exact ⟨0, ![], ![], ![], 1, by simp⟩
    · obtain ⟨a, b, rfl⟩ := exists_affine hg
      exact ⟨1, ![a], ![b], ![1], 0, by simp⟩
  | zero => exact ⟨0, ![], ![], ![], 0, by funext x; simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨k, a, b, d, c, rfl⟩ := hf
    obtain ⟨k', a', b', d', c', rfl⟩ := hg
    refine ⟨k + k', Fin.append a a', Fin.append b b', Fin.append d d', c + c', ?_⟩
    funext x
    simp only [Pi.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    ring
  | smul r f _ hf =>
    obtain ⟨k, a, b, d, c, rfl⟩ := hf
    refine ⟨k, a, b, r • d, r * c, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, mul_sum, mul_assoc]

end reluNet

/-- The function computed by a ReLU network with two hidden layers of widths `k₁` and `k₂`. -/
def twoLayerNet {k₁ k₂ : ℕ} (W₁ : Matrix (Fin k₁) ι ℝ) (b₁ : Fin k₁ → ℝ)
    (W₂ : Matrix (Fin k₂) (Fin k₁) ℝ) (b₂ : Fin k₂ → ℝ) (w₃ : Fin k₂ → ℝ) (b₃ : ℝ)
    (x : ι → ℝ) : ℝ :=
  w₃ ⬝ᵥ (fun j ↦ relu ((W₂ *ᵥ fun i ↦ relu ((W₁ *ᵥ x) i + b₁ i)) j + b₂ j)) + b₃


/-- Running two networks in parallel and adding their outputs. -/
theorem twoLayerNet_add {k₁ k₂ k₁' k₂' : ℕ} (W₁ : Matrix (Fin k₁) ι ℝ) (b₁ : Fin k₁ → ℝ)
    (W₂ : Matrix (Fin k₂) (Fin k₁) ℝ) (b₂ : Fin k₂ → ℝ) (w₃ : Fin k₂ → ℝ) (b₃ : ℝ)
    (W₁' : Matrix (Fin k₁') ι ℝ) (b₁' : Fin k₁' → ℝ)
    (W₂' : Matrix (Fin k₂') (Fin k₁') ℝ) (b₂' : Fin k₂' → ℝ) (w₃' : Fin k₂' → ℝ) (b₃' : ℝ) :
    twoLayerNet W₁ b₁ W₂ b₂ w₃ b₃ + twoLayerNet W₁' b₁' W₂' b₂' w₃' b₃' =
      twoLayerNet (Matrix.of (Fin.append W₁ W₁')) (Fin.append b₁ b₁')
        (Matrix.of (Fin.append (fun j ↦ Fin.append (W₂ j) 0) (fun j ↦ Fin.append 0 (W₂' j))))
        (Fin.append b₂ b₂') (Fin.append w₃ w₃') (b₃ + b₃') := by
  funext x
  simp only [twoLayerNet, dotProduct, mulVec, Pi.add_apply, Fin.sum_univ_add, Matrix.of_apply,
    Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, sum_const_zero, add_zero,
    zero_add]
  have h₁ (i : Fin k₁) : Fin.append W₁ W₁' (Fin.castAdd k₁' i) = W₁ i := Fin.append_left _ _ _
  have h₂ (i : Fin k₁') : Fin.append W₁ W₁' (Fin.natAdd k₁ i) = W₁' i := Fin.append_right _ _ _
  simp only [h₁, h₂]
  ring

/-- Every function computed with two hidden layers is computed by an explicit network
`twoLayerNet`. -/
theorem reluNet.exists_twoLayerNet {f : (ι → ℝ) → ℝ} (hf : f ∈ reluNet ι 2) :
    ∃ (k₁ k₂ : ℕ) (W₁ : Matrix (Fin k₁) ι ℝ) (b₁ : Fin k₁ → ℝ) (W₂ : Matrix (Fin k₂) (Fin k₁) ℝ)
      (b₂ : Fin k₂ → ℝ) (w₃ : Fin k₂ → ℝ) (b₃ : ℝ), f = twoLayerNet W₁ b₁ W₂ b₂ w₃ b₃ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨g, hg, rfl⟩
    · exact ⟨0, 0, 0, 0, 0, 0, 0, 1, by funext x; simp [twoLayerNet]⟩
    · obtain ⟨k, a, b, d, c, rfl⟩ := reluNet.exists_sum hg
      refine ⟨k, 1, Matrix.of a, b, Matrix.of fun _ ↦ d, fun _ ↦ c, fun _ ↦ 1, 0, ?_⟩
      funext x
      simp [twoLayerNet, dotProduct, mulVec]
  | zero => exact ⟨0, 0, 0, 0, 0, 0, 0, 0, by funext x; simp [twoLayerNet]⟩
  | add f g _ _ hf hg =>
    obtain ⟨k₁, k₂, W₁, b₁, W₂, b₂, w₃, b₃, rfl⟩ := hf
    obtain ⟨k₁', k₂', W₁', b₁', W₂', b₂', w₃', b₃', rfl⟩ := hg
    exact ⟨_, _, _, _, _, _, _, _, twoLayerNet_add W₁ b₁ W₂ b₂ w₃ b₃ W₁' b₁' W₂' b₂' w₃' b₃'⟩
  | smul r f _ hf =>
    obtain ⟨k₁, k₂, W₁, b₁, W₂, b₂, w₃, b₃, rfl⟩ := hf
    refine ⟨k₁, k₂, W₁, b₁, W₂, b₂, r • w₃, r * b₃, ?_⟩
    funext x
    simp only [twoLayerNet, Pi.smul_apply, smul_eq_mul, smul_dotProduct, mul_add]

end

end AuthorReal

-- Source module: Solutions/AuthorSupport.lean


/-!
# Support functions

Basic properties of `supportFun`, and the valuation property for a single hyperplane cut:
for a compact convex set `K` and a hyperplane `{⟪a, p⟫ = b}`,
`h_K = h_{K ∩ {⟪a,p⟫ ≤ b}} + h_{K ∩ {⟪a,p⟫ ≥ b}} - h_{K ∩ {⟪a,p⟫ = b}}`.
-/

open Finset

namespace AuthorReal

noncomputable section

variable {ι : Type*} [Fintype ι]

@[simp]
theorem supportFun_empty : supportFun (∅ : Set (ι → ℝ)) = 0 := by
  funext x; simp [supportFun]

/-- The linear form `p ↦ ⟪p, x⟫` is continuous. -/
theorem continuous_dotProduct_left (x : ι → ℝ) : Continuous fun p : ι → ℝ ↦ p ⬝ᵥ x :=
  continuous_id.dotProduct continuous_const

/-- A bounded set has a bounded-above image under `p ↦ ⟪p, x⟫`. -/
theorem bddAbove_image_dotProduct {K : Set (ι → ℝ)} (hK : Bornology.IsBounded K)
    (x : ι → ℝ) : BddAbove ((fun p ↦ p ⬝ᵥ x) '' K) :=
  ((hK.isCompact_closure.image (continuous_dotProduct_left x)).bddAbove).mono
    (Set.image_mono subset_closure)

/-- Every point of a bounded set is bounded by the support function. -/
theorem le_supportFun {K : Set (ι → ℝ)} (hK : Bornology.IsBounded K) {p : ι → ℝ} (hp : p ∈ K)
    (x : ι → ℝ) : p ⬝ᵥ x ≤ supportFun K x :=
  le_csSup (bddAbove_image_dotProduct hK x) ⟨p, hp, rfl⟩

/-- An upper bound on a nonempty set bounds its support function. -/
theorem supportFun_le {K : Set (ι → ℝ)} (hK : K.Nonempty) {x : ι → ℝ} {c : ℝ}
    (h : ∀ p ∈ K, p ⬝ᵥ x ≤ c) : supportFun K x ≤ c :=
  csSup_le (hK.image _) (by rintro _ ⟨p, hp, rfl⟩; exact h p hp)

/-- On a nonempty compact set, the supremum defining the support function is attained. -/
theorem IsCompact.exists_supportFun_eq {K : Set (ι → ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (x : ι → ℝ) : ∃ p ∈ K, supportFun K x = p ⬝ᵥ x := by
  obtain ⟨p, hp, h⟩ := (hK.image (continuous_dotProduct_left x)).sSup_mem (hne.image _)
  exact ⟨p, hp, h.symm⟩

/-- Support function of a dilated and translated set. -/
theorem supportFun_image_smul_add {K : Set (ι → ℝ)} (hK : Bornology.IsBounded K)
    (hne : K.Nonempty) {r : ℝ} (hr : 0 < r) (t x : ι → ℝ) :
    supportFun ((fun p ↦ r • p + t) '' K) x = r * supportFun K x + t ⬝ᵥ x := by
  have key : ∀ p, (r • p + t) ⬝ᵥ x = r * (p ⬝ᵥ x) + t ⬝ᵥ x := fun p ↦ by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hK' : Bornology.IsBounded ((fun p ↦ r • p + t) '' K) := by
    have hc : Continuous fun p : ι → ℝ ↦ r • p + t := by fun_prop
    exact (hK.isCompact_closure.image hc).isBounded.subset (Set.image_mono subset_closure)
  apply le_antisymm
  · refine supportFun_le (hne.image _) ?_
    rintro _ ⟨p, hp, rfl⟩
    rw [key]
    gcongr
    exact le_supportFun hK hp x
  · have : supportFun K x ≤ (supportFun ((fun p ↦ r • p + t) '' K) x - t ⬝ᵥ x) / r := by
      refine supportFun_le hne fun p hp ↦ ?_
      rw [le_div_iff₀ hr, le_sub_iff_add_le, mul_comm, ← key]
      exact le_supportFun hK' ⟨p, hp, rfl⟩ x
    rw [le_div_iff₀ hr] at this
    linarith

/-- If `p, q ∈ K` lie on opposite sides of the hyperplane `{⟪a, ·⟫ = b}`, then the segment
`[p, q]` meets the hyperplane in a point `z` with `⟪z, x⟫ ≥ min ⟪p, x⟫ ⟪q, x⟫`. -/
theorem exists_mem_cut_le {K : Set (ι → ℝ)} (hconv : Convex ℝ K) {a : ι → ℝ} {b : ℝ}
    {p q : ι → ℝ} (hp : p ∈ K) (hq : q ∈ K) (hpa : a ⬝ᵥ p ≤ b) (hqa : b ≤ a ⬝ᵥ q) (x : ι → ℝ) :
    ∃ z ∈ K ∩ {p | a ⬝ᵥ p = b}, min (p ⬝ᵥ x) (q ⬝ᵥ x) ≤ z ⬝ᵥ x := by
  rcases hpa.eq_or_lt with hpa | hpa
  · exact ⟨p, ⟨hp, hpa⟩, min_le_left _ _⟩
  set t := (b - a ⬝ᵥ p) / (a ⬝ᵥ q - a ⬝ᵥ p)
  have hd : 0 < a ⬝ᵥ q - a ⬝ᵥ p := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  have hlin : ∀ y : ι → ℝ, y ⬝ᵥ ((1 - t) • p + t • q) = (1 - t) * (y ⬝ᵥ p) + t * (y ⬝ᵥ q) :=
    fun y ↦ by rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨(1 - t) • p + t • q, ⟨hconv hp hq (by linarith) ht0 (by ring), ?_⟩, ?_⟩
  · change a ⬝ᵥ _ = b
    rw [hlin]
    have : t * (a ⬝ᵥ q - a ⬝ᵥ p) = b - a ⬝ᵥ p := div_mul_cancel₀ _ hd.ne'
    linear_combination this
  · rw [dotProduct_comm ((1 - t) • p + t • q) x, hlin, dotProduct_comm x p, dotProduct_comm x q]
    have h1 := min_le_left (p ⬝ᵥ x) (q ⬝ᵥ x)
    have h2 := min_le_right (p ⬝ᵥ x) (q ⬝ᵥ x)
    nlinarith

/-- The valuation property of support functions for a single hyperplane cut. -/
theorem supportFun_cut {K : Set (ι → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (a : ι → ℝ) (b : ℝ) :
    supportFun K = supportFun (K ∩ {p | a ⬝ᵥ p ≤ b}) + supportFun (K ∩ {p | b ≤ a ⬝ᵥ p}) -
      supportFun (K ∩ {p | a ⬝ᵥ p = b}) := by
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  set L := K ∩ {p | a ⬝ᵥ p ≤ b}
  set U := K ∩ {p | b ≤ a ⬝ᵥ p}
  set Z := K ∩ {p | a ⬝ᵥ p = b}
  have hc : Continuous fun p : ι → ℝ ↦ a ⬝ᵥ p := continuous_const.dotProduct continuous_id
  have hL : IsCompact L := hK.inter_right (isClosed_le hc continuous_const)
  have hU : IsCompact U := hK.inter_right (isClosed_le continuous_const hc)
  have hZL : Z ⊆ L := fun p hp ↦ ⟨hp.1, hp.2.le⟩
  have hZU : Z ⊆ U := fun p hp ↦ ⟨hp.1, hp.2.ge⟩
  rcases L.eq_empty_or_nonempty with hL0 | hLne
  · have hZ0 : Z = ∅ := Set.subset_eq_empty hZL hL0
    have hUK : U = K := Set.inter_eq_left.2 fun p hp ↦ by
      by_contra h
      have : p ∈ L := ⟨hp, by simp only [Set.mem_ofPred_eq] at h ⊢; linarith⟩
      simp [hL0] at this
    rw [hL0, hZ0, hUK]
    simp
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · have hZ0 : Z = ∅ := Set.subset_eq_empty hZU hU0
    have hLK : L = K := Set.inter_eq_left.2 fun p hp ↦ by
      by_contra h
      have : p ∈ U := ⟨hp, by simp only [Set.mem_ofPred_eq] at h ⊢; linarith⟩
      simp [hU0] at this
    rw [hU0, hZ0, hLK]
    simp
  obtain ⟨p, hpL, hp⟩ := IsCompact.exists_supportFun_eq hL hLne x
  obtain ⟨q, hqU, hq⟩ := IsCompact.exists_supportFun_eq hU hUne x
  obtain ⟨z, hzZ, hz⟩ := exists_mem_cut_le hconv hpL.1 hqU.1 hpL.2 hqU.2 x
  have hmax : supportFun K x = max (supportFun L x) (supportFun U x) := by
    apply le_antisymm
    · refine supportFun_le (hLne.mono Set.inter_subset_left) fun r hr ↦ ?_
      rcases le_total (a ⬝ᵥ r) b with h | h
      · exact (le_supportFun hL.isBounded ⟨hr, h⟩ x).trans (le_max_left _ _)
      · exact (le_supportFun hU.isBounded ⟨hr, h⟩ x).trans (le_max_right _ _)
    · rw [hp, hq]
      exact max_le (le_supportFun hK.isBounded hpL.1 x) (le_supportFun hK.isBounded hqU.1 x)
  have hmin : supportFun Z x = min (supportFun L x) (supportFun U x) := by
    apply le_antisymm
    · exact supportFun_le ⟨z, hzZ⟩ fun r hr ↦
        le_min (le_supportFun hL.isBounded (hZL hr) x) (le_supportFun hU.isBounded (hZU hr) x)
    · rw [hp, hq]
      exact hz.trans (le_supportFun (hL.isBounded.subset hZL) hzZ x)
  rw [hmax, hmin]
  linarith [min_add_max (supportFun L x) (supportFun U x)]

end

end AuthorReal

-- Source module: Solutions/AuthorMaxSpan.lean


/-!
# Maxima of linear forms

If `W` is a finite set of points lying in an affine subspace of dimension `d`, then
`x ↦ max_{w ∈ W} ⟪w, x⟫` is a linear combination of maxima of at most `d + 1` linear forms.
The proof uses Radon's theorem: if `W` is affinely dependent and `I` is a Radon partition, then
`max_W = ∑_{∅ ≠ S ⊆ I} (-1)^{|S|+1} max_{W \ S}`.
-/

open Finset

namespace AuthorReal

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The maximum over the empty set is `0` by convention. -/
theorem maxLin_empty : maxLin (∅ : Finset (ι → ℝ)) = 0 := by
  funext x; simp [maxLin]

/-- The maximum of a single linear form is that linear form. -/
theorem maxLin_singleton (t : ι → ℝ) : maxLin {t} = fun x ↦ t ⬝ᵥ x := by
  funext x; simp [maxLin]

/-- Unfolding `maxLin` for a nonempty set. -/
theorem maxLin_eq_sup' {W : Finset (ι → ℝ)} (hW : W.Nonempty) (x : ι → ℝ) :
    maxLin W x = W.sup' hW (· ⬝ᵥ x) := by
  simp [maxLin, hW]

/-- A maximum of at most `k` linear forms lies in `maxSpan ι k`. -/
theorem maxLin_mem_maxSpan_of_card_le {W : Finset (ι → ℝ)} (hW : W.Nonempty) {k : ℕ}
    (hk : W.card ≤ k) : maxLin W ∈ maxSpan ι k :=
  Submodule.subset_span ⟨W, hW, hk, rfl⟩

/-- Linear forms lie in `maxSpan ι k` for `k ≥ 1`. -/
theorem linear_mem_maxSpan (t : ι → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (fun x ↦ t ⬝ᵥ x) ∈ maxSpan ι k := by
  rw [← maxLin_singleton]
  exact maxLin_mem_maxSpan_of_card_le (singleton_nonempty t) (by simpa using hk)

/-- Removing a point does not change the maximum if another point is at least as large. -/
theorem maxLin_erase_apply [DecidableEq (ι → ℝ)] {V : Finset (ι → ℝ)} {i j : ι → ℝ} {x : ι → ℝ}
    (hj : j ∈ V) (hji : j ≠ i) (h : i ⬝ᵥ x ≤ j ⬝ᵥ x) : maxLin (V.erase i) x = maxLin V x := by
  have hne : (V.erase i).Nonempty := ⟨j, mem_erase.2 ⟨hji, hj⟩⟩
  rw [maxLin_eq_sup' hne, maxLin_eq_sup' (hne.mono (erase_subset i V))]
  refine le_antisymm (sup'_mono _ (erase_subset i V) hne) (sup'_le _ _ fun v hv ↦ ?_)
  by_cases hvi : v = i
  · subst hvi
    exact h.trans (le_sup' (· ⬝ᵥ x) (mem_erase.2 ⟨hji, hj⟩))
  · exact le_sup' (· ⬝ᵥ x) (mem_erase.2 ⟨hvi, hv⟩)

/-- The inclusion–exclusion identity for a Radon partition `W = I ∪ (W \ I)`. -/
theorem maxLin_eq_neg_sum_of_radon [DecidableEq (ι → ℝ)] {W I : Finset (ι → ℝ)}
    {z : ι → ℝ} (hz₁ : z ∈ convexHull ℝ (I : Set (ι → ℝ)))
    (hz₂ : z ∈ convexHull ℝ ((W \ I : Finset (ι → ℝ)) : Set (ι → ℝ))) :
    maxLin W = -∑ S ∈ I.powerset.erase ∅, (-1 : ℝ) ^ S.card • maxLin (W \ S) := by
  funext x
  have hne : (W \ I).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [h] at hz₂
  set M := maxLin (W \ I) x
  have hlin : IsLinearMap ℝ fun p : ι → ℝ ↦ p ⬝ᵥ x :=
    ⟨fun p q ↦ add_dotProduct p q x, fun c p ↦ smul_dotProduct c p x⟩
  obtain ⟨i₀, hi₀I, hi₀⟩ : ∃ i₀ ∈ I, i₀ ⬝ᵥ x ≤ M := by
    by_contra! h
    have h₁ : z ⬝ᵥ x ≤ M :=
      convexHull_min (fun w hw ↦ (le_sup' (· ⬝ᵥ x) hw).trans_eq (maxLin_eq_sup' hne x).symm)
        (convex_halfSpace_le hlin M) hz₂
    have h₂ : M < z ⬝ᵥ x := convexHull_min (fun w hw ↦ h w hw) (convex_halfSpace_gt hlin M) hz₁
    linarith
  obtain ⟨j, hj, hjM⟩ := exists_mem_eq_sup' hne (· ⬝ᵥ x)
  rw [← maxLin_eq_sup'] at hjM
  have hji : j ≠ i₀ := fun h ↦ (mem_sdiff.1 hj).2 (h ▸ hi₀I)
  have hsum : ∑ S ∈ I.powerset, (-1 : ℝ) ^ S.card * maxLin (W \ S) x = 0 := by
    rw [← insert_erase hi₀I, sum_powerset_insert (notMem_erase i₀ I), ← sum_add_distrib]
    refine sum_eq_zero fun t ht ↦ ?_
    have hti : i₀ ∉ t := fun h ↦ notMem_erase i₀ I (mem_powerset.1 ht h)
    have htI : t ⊆ I := (mem_powerset.1 ht).trans (erase_subset _ _)
    have hjt : j ∈ W \ t := mem_sdiff.2 ⟨(mem_sdiff.1 hj).1, fun h ↦ (mem_sdiff.1 hj).2 (htI h)⟩
    rw [card_insert_of_notMem hti, pow_succ, sdiff_insert,
      maxLin_erase_apply hjt hji (hjM ▸ hi₀)]
    ring
  rw [← add_sum_erase _ _ (empty_mem_powerset I)] at hsum
  simp only [card_empty, pow_zero, one_mul, sdiff_empty] at hsum
  rw [Pi.neg_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

/-- If `W` lies in an affine subspace of dimension at most `d`, then `max_{w ∈ W} ⟪w, ·⟫` is a
linear combination of maxima of at most `d + 1` linear forms. -/
theorem maxLin_mem_maxSpan (W : Finset (ι → ℝ)) (A : AffineSubspace ℝ (ι → ℝ))
    (hW : (W : Set (ι → ℝ)) ⊆ A) {d : ℕ} (hA : Module.finrank ℝ A.direction ≤ d) :
    maxLin W ∈ maxSpan ι (d + 1) := by
  classical
  induction W using Finset.strongInduction with
  | H W ih =>
  rcases W.eq_empty_or_nonempty with rfl | hne
  · rw [maxLin_empty]; exact zero_mem _
  by_cases hai : AffineIndependent ℝ ((↑) : W → ι → ℝ)
  · refine maxLin_mem_maxSpan_of_card_le hne ?_
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hne.card_pos.ne'
    have h₁ := hai.finrank_vectorSpan (n := n) (by simpa using hn)
    have h₂ : vectorSpan ℝ (Set.range ((↑) : W → ι → ℝ)) ≤ A.direction := by
      rw [Subtype.range_coe_subtype]
      exact vectorSpan_mono ℝ hW
    have h₃ := Submodule.finrank_mono h₂
    omega
  obtain ⟨I, z, hz₁, hz₂⟩ := Convex.radon_partition hai
  set I' : Finset (ι → ℝ) := W.filter fun w ↦ ∃ h : w ∈ W, (⟨w, h⟩ : W) ∈ I
  have hI' : ((↑) : W → ι → ℝ) '' I = I' := by
    ext w; simp [I']
  have hI'c : ((↑) : W → ι → ℝ) '' Iᶜ = ↑(W \ I') := by
    ext w
    simp only [Set.mem_image, Set.mem_compl_iff, Subtype.exists, exists_and_right,
      exists_eq_right, coe_sdiff, coe_filter, and_exists_self, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_ofPred_eq, not_exists, I']
    exact ⟨fun ⟨h, h'⟩ ↦ ⟨h, fun _ ↦ h'⟩, fun ⟨h, h'⟩ ↦ ⟨h, h' h⟩⟩
  rw [hI'] at hz₁
  rw [hI'c] at hz₂
  rw [maxLin_eq_neg_sum_of_radon hz₁ hz₂]
  refine neg_mem (sum_mem fun S hS ↦
    Submodule.smul_mem _ _ (ih _ ?_ ((coe_subset.2 sdiff_subset).trans hW)))
  obtain ⟨hS0, hS⟩ := mem_erase.1 hS
  exact sdiff_ssubset ((mem_powerset.1 hS).trans (filter_subset _ _)) (nonempty_iff_ne_empty.2 hS0)

end

end AuthorReal

-- Source module: Solutions/AuthorHPolytope.lean


/-!
# Polytopes given by inequalities and the transfer principle

For polytopes `hpoly cs` in the hyperplane `∑ pᵢ = 1` we prove:

* `supportFun_mem_maxSpan_of_subset`: a bounded polytope lying in a hyperplane `{⟪a,p⟫ = b}`
  which is not parallel to `∑ pᵢ = 1` has a support function in `maxSpan ι (card ι - 1)`.
  (Its extreme points are finitely many and span an affine space of dimension `card ι - 2`.)
* `transfer`: if a signed sum of indicator functions of polytopes vanishes at all generic points,
  then the corresponding signed sum of support functions lies in `maxSpan ι (card ι - 1)`.
-/

open Finset Filter Topology

namespace AuthorReal

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem convex_hpoly (cs : Finset (Constraint ι)) : Convex ℝ (hpoly cs) := by
  intro p hp q hq s t hs ht hst
  refine ⟨?_, fun c hc ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.1, hq.1,
      mul_one, hst]
  · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    calc s * (c.a ⬝ᵥ p) + t * (c.a ⬝ᵥ q) ≤ s * c.b + t * c.b := by
          gcongr
          exacts [hp.2 c hc, hq.2 c hc]
      _ = c.b := by rw [← add_mul, hst, one_mul]

theorem isClosed_hpoly (cs : Finset (Constraint ι)) : IsClosed (hpoly cs) := by
  have h1 : IsClosed {p : ι → ℝ | ∑ i, p i = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have h2 : IsClosed {p : ι → ℝ | ∀ c ∈ cs, c.a ⬝ᵥ p ≤ c.b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_biInter fun c _ ↦
      isClosed_le (continuous_const.dotProduct continuous_id) continuous_const
  exact h1.inter h2

theorem isCompact_hpoly {cs : Finset (Constraint ι)} (hb : Bornology.IsBounded (hpoly cs)) :
    IsCompact (hpoly cs) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_hpoly cs) hb

/-- Distinct extreme points of `hpoly cs` have distinct sets of tight constraints. -/
theorem eq_of_extremePoints_of_tight_eq {cs : Finset (Constraint ι)} {p q : ι → ℝ}
    (hp : p ∈ (hpoly cs).extremePoints ℝ) (hq : q ∈ (hpoly cs).extremePoints ℝ)
    (h : ∀ c ∈ cs, c.a ⬝ᵥ p = c.b ↔ c.a ⬝ᵥ q = c.b) : q = p := by
  have hpK := hp.1
  have hqK := hq.1
  set φ : ℝ → ι → ℝ := fun ε ↦ p - ε • (q - p) with hφ
  have hcont : Continuous φ := by fun_prop
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ φ ε ∈ hpoly cs := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ c ∈ cs, c.a ⬝ᵥ p ≠ c.b → c.a ⬝ᵥ φ ε < c.b := by
      rw [eventually_all_finset]
      intro c hc
      by_cases hcp : c.a ⬝ᵥ p = c.b
      · exact Eventually.of_forall fun _ h ↦ absurd hcp h
      · have hlt : c.a ⬝ᵥ φ 0 < c.b := by
          simp only [hφ, zero_smul, sub_zero]
          exact lt_of_le_of_ne (hpK.2 c hc) hcp
        have hc' : Continuous fun ε ↦ c.a ⬝ᵥ φ ε := continuous_const.dotProduct hcont
        filter_upwards [hc'.continuousAt.eventually_lt continuousAt_const hlt] with ε hε
        exact fun _ ↦ hε
    filter_upwards [h1, nhdsWithin_le_nhds h2] with ε hε1 hε2
    refine ⟨hε1, ?_, fun c hc ↦ ?_⟩
    · simp only [hφ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sum_sub_distrib, ← mul_sum,
        hpK.1, hqK.1, sub_self, mul_zero, sub_zero]
    · by_cases hcp : c.a ⬝ᵥ p = c.b
      · have hcq := (h c hc).1 hcp
        simp only [hφ, dotProduct_sub, dotProduct_smul, hcp, hcq, sub_self, smul_zero, sub_zero,
          le_refl]
      · exact (hε2 c hc hcp).le
  obtain ⟨ε, hε0, hεK⟩ := hev.exists
  have hseg : p ∈ openSegment ℝ (φ ε) q := by
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, by field_simp, ?_⟩
    simp only [hφ]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  exact ((mem_extremePoints.1 hp).2 _ hεK _ hqK hseg).2

theorem finite_extremePoints_hpoly (cs : Finset (Constraint ι)) :
    ((hpoly cs).extremePoints ℝ).Finite := by
  classical
  let T : (ι → ℝ) → Finset (Constraint ι) := fun p ↦ cs.filter fun c ↦ c.a ⬝ᵥ p = c.b
  refine Set.Finite.of_finite_image (f := T) ((cs.powerset.finite_toSet).subset ?_) ?_
  · rintro _ ⟨p, -, rfl⟩
    simp only [T, coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_filter]
    exact fun c hc ↦ hc.1
  · intro p hp q hq hpq
    refine (eq_of_extremePoints_of_tight_eq hp hq fun c hc ↦ ?_).symm
    have := congrArg (c ∈ ·) hpq
    simpa [T, hc] using this

/-- The support function of a compact convex set with finitely many extreme points is the
maximum of the linear forms given by its extreme points. -/
theorem supportFun_eq_maxLin_of_finite {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hfin : (K.extremePoints ℝ).Finite) :
    supportFun K = maxLin hfin.toFinset := by
  have hKM := closure_convexHull_extremePoints hK hconv
  have hEne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hK.extremePoints_nonempty hne
  ext x
  simp only [maxLin, hEne, ↓reduceDIte]
  apply le_antisymm
  · refine supportFun_le hne fun p hp ↦ ?_
    rw [← hKM] at hp
    have hhalf : Convex ℝ {q : ι → ℝ | q ⬝ᵥ x ≤ hfin.toFinset.sup' hEne (· ⬝ᵥ x)} :=
      convex_halfSpace_le ⟨fun _ _ ↦ add_dotProduct _ _ _, fun _ _ ↦ smul_dotProduct _ _ _⟩ _
    have hcl : IsClosed {q : ι → ℝ | q ⬝ᵥ x ≤ hfin.toFinset.sup' hEne (· ⬝ᵥ x)} :=
      isClosed_le (continuous_id.dotProduct continuous_const) continuous_const
    refine closure_minimal (convexHull_min (fun q hq ↦ ?_) hhalf) hcl hp
    exact le_sup' (· ⬝ᵥ x) (by simpa using hq)
  · obtain ⟨e, he, heq⟩ := exists_mem_eq_sup' hEne (· ⬝ᵥ x)
    rw [heq]
    exact le_supportFun hK.isBounded (extremePoints_subset (by simpa using he)) x

theorem supportFun_mem_maxSpan_of_subset {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) {g : Constraint ι} (hg : g.IsNonconst)
    (hsub : hpoly cs ⊆ {p | g.a ⬝ᵥ p = g.b}) :
    supportFun (hpoly cs) ∈ maxSpan ι (Fintype.card ι - 1) := by
  classical
  rcases (hpoly cs).eq_empty_or_nonempty with hemp | ⟨p₀, hp₀⟩
  · rw [hemp, supportFun_empty]
    exact zero_mem _
  obtain ⟨i, j, hij⟩ := hg
  have hij' : i ≠ j := fun h ↦ hij (h ▸ rfl)
  have hcard : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.2 ⟨i, j, hij'⟩
  let L : (ι → ℝ) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun d ↦ (∑ k, d k, g.a ⬝ᵥ d)
      map_add' := fun d e ↦ by simp [sum_add_distrib, dotProduct_add]
      map_smul' := fun r d ↦ by simp [mul_sum, dotProduct_smul] }
  have hL : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨s, t⟩
    have hne : g.a i - g.a j ≠ 0 := sub_ne_zero.2 hij
    refine ⟨s • Pi.single i 1 + ((t - s * g.a i) / (g.a i - g.a j)) •
      (Pi.single i 1 - Pi.single j 1), ?_⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq]
    constructor
    · simp [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    · simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, dotProduct_single, smul_eq_mul]
      field_simp
      ring
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [hL, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hrank
  let A : AffineSubspace ℝ (ι → ℝ) := AffineSubspace.mk' p₀ (LinearMap.ker L)
  have hK := isCompact_hpoly hb
  have hfin := finite_extremePoints_hpoly cs
  rw [supportFun_eq_maxLin_of_finite hK (convex_hpoly cs) ⟨p₀, hp₀⟩ hfin]
  have hEA : (hfin.toFinset : Set (ι → ℝ)) ⊆ A := by
    intro e he
    have heK : e ∈ hpoly cs := extremePoints_subset (by simpa using he)
    have h1 : g.a ⬝ᵥ e = g.b := hsub heK
    have h2 : g.a ⬝ᵥ p₀ = g.b := hsub hp₀
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', LinearMap.mem_ker]
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, vsub_eq_sub, Pi.sub_apply, sum_sub_distrib,
      heK.1, hp₀.1, sub_self, dotProduct_sub, h1, h2, Prod.mk_zero_zero]
  have hdim : Module.finrank ℝ A.direction ≤ Fintype.card ι - 2 := by
    rw [AffineSubspace.direction_mk']
    omega
  have := maxLin_mem_maxSpan _ A hEA hdim
  rwa [show Fintype.card ι - 2 + 1 = Fintype.card ι - 1 by omega] at this


/-! ### Cells of a hyperplane arrangement -/

/-- The reversed constraint `⟪a, p⟫ ≥ b`. -/
def Constraint.rev (c : Constraint ι) : Constraint ι :=
  ⟨-c.a, -c.b⟩

theorem Constraint.rev_le_iff (c : Constraint ι) (p : ι → ℝ) :
    c.rev.a ⬝ᵥ p ≤ c.rev.b ↔ c.b ≤ c.a ⬝ᵥ p := by
  simp [Constraint.rev, neg_dotProduct]

/-- The constraints of the cell of the arrangement `F` on the side `≤` of the constraints in `S`
and on the side `≥` of the constraints in `F \ S`. -/
def cellCons (F S : Finset (Constraint ι)) : Finset (Constraint ι) :=
  S ∪ (F \ S).image Constraint.rev

/-- The (closed) cell of the arrangement `F` on the side `≤` of the constraints in `S` and on the
side `≥` of the remaining constraints of `F`. -/
def cell (F S : Finset (Constraint ι)) : Set (ι → ℝ) :=
  {p | (∀ c ∈ S, c.a ⬝ᵥ p ≤ c.b) ∧ ∀ c ∈ F, c ∉ S → c.b ≤ c.a ⬝ᵥ p}

theorem hpoly_union_cellCons (cs F S : Finset (Constraint ι)) :
    hpoly (cs ∪ cellCons F S) = hpoly cs ∩ cell F S := by
  ext p
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, fun c hc ↦ h2 c (mem_union_left _ hc)⟩,
      fun c hc ↦ h2 c (mem_union_right _ (mem_union_left _ hc)), fun c hc hcS ↦ ?_⟩
    refine (c.rev_le_iff p).1 (h2 _ (mem_union_right _ (mem_union_right _ ?_)))
    exact mem_image_of_mem _ (mem_sdiff.2 ⟨hc, hcS⟩)
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, fun c hc ↦ ?_⟩
    rcases mem_union.1 hc with hc | hc
    · exact h2 c hc
    rcases mem_union.1 hc with hc | hc
    · exact h3 c hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hc
    exact (d.rev_le_iff p).2 (h4 d (mem_sdiff.1 hd).1 (mem_sdiff.1 hd).2)

theorem hpoly_union_pair_rev (cs : Finset (Constraint ι)) (g : Constraint ι) :
    hpoly (cs ∪ {g, g.rev}) = hpoly cs ∩ {p | g.a ⬝ᵥ p = g.b} := by
  ext p
  simp only [hpoly, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_union, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun c hc ↦ h2 c (Or.inl hc)⟩, le_antisymm (h2 g (Or.inr (Or.inl rfl)))
      ((g.rev_le_iff p).1 (h2 _ (Or.inr (Or.inr rfl))))⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    rintro c (hc | rfl | rfl)
    exacts [h2 c hc, h3.le, (g.rev_le_iff p).2 h3.ge]

theorem convex_hpoly_inter_cell (cs F S : Finset (Constraint ι)) :
    Convex ℝ (hpoly cs ∩ cell F S) := by
  rw [← hpoly_union_cellCons]
  exact convex_hpoly _

theorem isCompact_hpoly_inter_cell {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) (F S : Finset (Constraint ι)) :
    IsCompact (hpoly cs ∩ cell F S) := by
  rw [← hpoly_union_cellCons]
  exact isCompact_hpoly (by rw [hpoly_union_cellCons]; exact hb.subset Set.inter_subset_left)

theorem supportFun_inter_cell_mem_maxSpan {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) {F S : Finset (Constraint ι)} {g : Constraint ι}
    (hg : g.IsNonconst) (hsub : hpoly cs ∩ cell F S ⊆ {p | g.a ⬝ᵥ p = g.b}) :
    supportFun (hpoly cs ∩ cell F S) ∈ maxSpan ι (Fintype.card ι - 1) := by
  rw [← hpoly_union_cellCons] at hsub ⊢
  exact supportFun_mem_maxSpan_of_subset
    (by rw [hpoly_union_cellCons]; exact hb.subset Set.inter_subset_left) hg hsub

theorem cell_empty_empty : cell (∅ : Finset (Constraint ι)) ∅ = Set.univ := by
  ext p
  simp [cell]

theorem cell_insert_of_notMem {F S : Finset (Constraint ι)} {g : Constraint ι} (hgS : g ∉ S) :
    cell (insert g F) S = cell F S ∩ {p | g.b ≤ g.a ⬝ᵥ p} := by
  ext p
  simp only [cell, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_mem_insert]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, h2 hgS⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨h1, fun _ ↦ h2, h3⟩

theorem cell_insert_insert {F S : Finset (Constraint ι)} {g : Constraint ι} (hgF : g ∉ F) :
    cell (insert g F) (insert g S) = cell F S ∩ {p | g.a ⬝ᵥ p ≤ g.b} := by
  ext p
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun c hc ↦ h1 c (mem_insert_of_mem hc), fun c hc hcS ↦ ?_⟩,
      h1 g (mem_insert_self g S)⟩
    refine h2 c (mem_insert_of_mem hc) ?_
    rw [mem_insert, not_or]
    exact ⟨fun h ↦ hgF (h ▸ hc), hcS⟩
  · rintro ⟨⟨h1, h2⟩, hg1⟩
    refine ⟨fun c hc ↦ ?_, fun c hc hcS ↦ ?_⟩
    · rcases mem_insert.1 hc with rfl | hc
      exacts [hg1, h1 c hc]
    · rw [mem_insert, not_or] at hcS
      rcases mem_insert.1 hc with rfl | hc
      exacts [(hcS.1 rfl).elim, h2 c hc hcS.2]

/-- Iterated cut: the support function of a bounded polytope agrees, modulo
`maxSpan ι (card ι - 1)`, with the sum of the support functions of its intersections with the
cells of an arrangement of nonconstant hyperplanes. -/
theorem supportFun_sub_sum_cell_mem_maxSpan {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) (F : Finset (Constraint ι))
    (hF : ∀ g ∈ F, g.IsNonconst) :
    supportFun (hpoly cs) - ∑ S ∈ F.powerset, supportFun (hpoly cs ∩ cell F S) ∈
      maxSpan ι (Fintype.card ι - 1) := by
  induction F using Finset.induction_on with
  | empty => simp [cell_empty_empty]
  | insert g F hgF ih =>
    have ih := ih fun g' hg' ↦ hF g' (mem_insert_of_mem hg')
    have hg := hF g (mem_insert_self g F)
    rw [sum_powerset_insert hgF]
    have key : ∀ S ∈ F.powerset, supportFun (hpoly cs ∩ cell (insert g F) S) +
        supportFun (hpoly cs ∩ cell (insert g F) (insert g S)) =
        supportFun (hpoly cs ∩ cell F S) +
          supportFun (hpoly cs ∩ cell F S ∩ {p | g.a ⬝ᵥ p = g.b}) := by
      intro S hS
      have hgS : g ∉ S := fun h ↦ hgF (mem_powerset.1 hS h)
      have hcut := supportFun_cut (isCompact_hpoly_inter_cell hb F S)
        (convex_hpoly_inter_cell cs F S) g.a g.b
      rw [cell_insert_of_notMem hgS, cell_insert_insert hgF, ← Set.inter_assoc,
        ← Set.inter_assoc, hcut]
      abel
    have hmem : ∑ S ∈ F.powerset, supportFun (hpoly cs ∩ cell F S ∩ {p | g.a ⬝ᵥ p = g.b}) ∈
        maxSpan ι (Fintype.card ι - 1) := by
      refine sum_mem fun S _ ↦ ?_
      rw [← hpoly_union_cellCons, ← hpoly_union_pair_rev]
      refine supportFun_mem_maxSpan_of_subset ?_ hg ?_
      · rw [hpoly_union_pair_rev, hpoly_union_cellCons]
        exact hb.subset (Set.inter_subset_left.trans Set.inter_subset_left)
      · rw [hpoly_union_pair_rev]
        exact Set.inter_subset_right
    rw [← sum_add_distrib, sum_congr rfl key, sum_add_distrib]
    convert sub_mem ih hmem using 1
    abel

/-- A convex set on which each of finitely many affine functions is not identically zero
contains a point at which none of them vanishes. -/
theorem exists_forall_ne_of_convex {C : Set (ι → ℝ)} (hC : Convex ℝ C) (hne : C.Nonempty)
    (G : Finset (Constraint ι)) (hG : ∀ g ∈ G, ∃ q ∈ C, g.a ⬝ᵥ q ≠ g.b) :
    ∃ p ∈ C, ∀ g ∈ G, g.a ⬝ᵥ p ≠ g.b := by
  classical
  induction G using Finset.induction_on with
  | empty =>
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, by simp⟩
  | insert g G hgG ih =>
    obtain ⟨z, hzC, hz⟩ := ih fun g' hg' ↦ hG g' (mem_insert_of_mem hg')
    obtain ⟨q, hqC, hq⟩ := hG g (mem_insert_self g G)
    by_cases hgz : g.a ⬝ᵥ z = g.b
    · set φ : ℝ → ι → ℝ := fun t ↦ z + t • (q - z) with hφ
      have hcont : Continuous φ := by fun_prop
      have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ f ∈ G, f.a ⬝ᵥ φ t ≠ f.b := by
        rw [eventually_all_finset]
        intro f hf
        have : f.a ⬝ᵥ φ 0 ≠ f.b := by simpa [hφ] using hz f hf
        exact ((continuous_const.dotProduct hcont).tendsto 0).eventually_ne this
      have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := eventually_lt_nhds one_pos
      have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
      obtain ⟨t, ht1, ht2, ht3⟩ :=
        (h3.and ((h1.filter_mono nhdsWithin_le_nhds).and
          (h2.filter_mono nhdsWithin_le_nhds))).exists
      refine ⟨φ t, ?_, ?_⟩
      · have := hC hzC hqC (sub_nonneg.2 ht3.le) ht1.le (by ring)
        convert this using 1
        simp only [hφ]
        module
      · rw [forall_mem_insert]
        refine ⟨?_, ht2⟩
        simp only [hφ, dotProduct_add, dotProduct_smul, dotProduct_sub, hgz, smul_eq_mul]
        intro h
        have : t * (g.a ⬝ᵥ q - g.b) = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · exact ht1.ne' h'
        · exact hq (sub_eq_zero.1 h')
    · exact ⟨z, hzC, by rw [forall_mem_insert]; exact ⟨hgz, hz⟩⟩

/-- The transfer principle restricted to a single cell of the arrangement `G`. -/
theorem sum_smul_supportFun_inter_cell_mem_maxSpan {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (cs : κ → Finset (Constraint ι)) (G : Finset (Constraint ι)) (hG : ∀ g ∈ G, g.IsNonconst)
    (hcs : ∀ i ∈ s, cs i ⊆ G) (hbdd : ∀ i ∈ s, Bornology.IsBounded (hpoly (cs i)))
    (hgen : ∀ p : ι → ℝ, ∑ j, p j = 1 → (∀ g ∈ G, g.a ⬝ᵥ p ≠ g.b) →
      ∑ i ∈ s, c i * (hpoly (cs i)).indicator 1 p = 0) (S : Finset (Constraint ι)) :
    ∑ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) ∈ maxSpan ι (Fintype.card ι - 1) := by
  by_cases hz : ∃ z ∈ hpoly ∅ ∩ cell G S, ∀ g ∈ G, g.a ⬝ᵥ z ≠ g.b
  · obtain ⟨z, ⟨hzH, hzc⟩, hzg⟩ := hz
    have hsum := hgen z hzH.1 hzg
    have key : ∀ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) -
        (c i * (hpoly (cs i)).indicator 1 z) • supportFun (hpoly ∅ ∩ cell G S) ∈
          maxSpan ι (Fintype.card ι - 1) := by
      intro i hi
      by_cases hzi : z ∈ hpoly (cs i)
      · have heq : hpoly (cs i) ∩ cell G S = hpoly ∅ ∩ cell G S := by
          ext p
          constructor
          · rintro ⟨hp, hpc⟩
            exact ⟨⟨hp.1, by simp⟩, hpc⟩
          · rintro ⟨hp, hpc⟩
            refine ⟨⟨hp.1, fun d hd ↦ ?_⟩, hpc⟩
            have hdG := hcs i hi hd
            have hdS : d ∈ S := by
              by_contra hdS
              exact hzg d hdG (le_antisymm (hzi.2 d hd) (hzc.2 d hdG hdS))
            exact hpc.1 d hdS
        rw [heq, Set.indicator_of_mem hzi, Pi.one_apply, mul_one, sub_self]
        exact zero_mem _
      · rw [Set.indicator_of_notMem hzi, mul_zero, zero_smul, sub_zero]
        refine Submodule.smul_mem _ _ ?_
        have : ∃ d ∈ cs i, d.b < d.a ⬝ᵥ z := by
          by_contra! h
          exact hzi ⟨hzH.1, h⟩
        obtain ⟨d, hd, hdz⟩ := this
        have hdG := hcs i hi hd
        have hdS : d ∉ S := fun h ↦ (hzc.1 d h).not_gt hdz
        refine supportFun_inter_cell_mem_maxSpan (hbdd i hi) (hG d hdG) ?_
        rintro p ⟨hp, hpc⟩
        exact le_antisymm (hp.2 d hd) (hpc.2 d hdG hdS)
    have := sum_mem key
    rwa [sum_sub_distrib, ← sum_smul, hsum, zero_smul, sub_zero] at this
  · push Not at hz
    refine sum_mem fun i hi ↦ Submodule.smul_mem _ _ ?_
    rcases (hpoly (cs i) ∩ cell G S).eq_empty_or_nonempty with hemp | hne
    · rw [hemp, supportFun_empty]
      exact zero_mem _
    · have : ∃ g ∈ G, ∀ q ∈ hpoly (cs i) ∩ cell G S, g.a ⬝ᵥ q = g.b := by
        by_contra! h
        obtain ⟨p, ⟨hp, hpc⟩, hpg⟩ :=
          exists_forall_ne_of_convex (convex_hpoly_inter_cell _ _ _) hne G h
        obtain ⟨g, hg, hgp⟩ := hz p ⟨⟨hp.1, by simp⟩, hpc⟩
        exact hpg g hg hgp
      obtain ⟨g, hg, hgq⟩ := this
      exact supportFun_inter_cell_mem_maxSpan (hbdd i hi) (hG g hg) hgq

/-- **Transfer principle.** Let `G` be a finite set of hyperplanes, none parallel to
`∑ pᵢ = 1`, containing all constraints of the bounded polytopes `hpoly (cs i)`. If
`∑ i, c i * 1_{hpoly (cs i)}` vanishes at every point of `∑ pᵢ = 1` off the hyperplanes in `G`,
then `∑ i, c i • h_{hpoly (cs i)}` is a linear combination of maxima of `card ι - 1` linear forms.
-/
theorem transfer {κ : Type*} (s : Finset κ) (c : κ → ℝ) (cs : κ → Finset (Constraint ι))
    (G : Finset (Constraint ι)) (hG : ∀ g ∈ G, g.IsNonconst) (hcs : ∀ i ∈ s, cs i ⊆ G)
    (hbdd : ∀ i ∈ s, Bornology.IsBounded (hpoly (cs i)))
    (hgen : ∀ p : ι → ℝ, ∑ j, p j = 1 → (∀ g ∈ G, g.a ⬝ᵥ p ≠ g.b) →
      ∑ i ∈ s, c i * (hpoly (cs i)).indicator 1 p = 0) :
    ∑ i ∈ s, c i • supportFun (hpoly (cs i)) ∈ maxSpan ι (Fintype.card ι - 1) := by
  have h1 := sum_mem fun i hi ↦
    Submodule.smul_mem _ (c i) (supportFun_sub_sum_cell_mem_maxSpan (hbdd i hi) G hG)
  have h2 : ∑ S ∈ G.powerset, ∑ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) ∈
      maxSpan ι (Fintype.card ι - 1) :=
    sum_mem fun S _ ↦ sum_smul_supportFun_inter_cell_mem_maxSpan s c cs G hG hcs hbdd hgen S
  convert add_mem h1 h2 using 1
  simp only [smul_sub, sum_sub_distrib, smul_sum]
  rw [sum_comm (s := s)]
  abel

end

end AuthorReal

-- Source module: Solutions/AuthorPyramid.lean


/-!
# Pyramids over facet polytopes

For a polytope `B = facetPoly v cs` in the facet hyperplane `{∑ pᵢ = 1, p_v = 0}` we study the
pyramid `pyr v cs = conv ({e_v} ∪ B)`, given by homogenized inequalities. We show:

* `pyr_eq`: `pyr v cs = {t e_v + (1 - t) q | t ∈ [0, 1], q ∈ B}` if `B` is bounded and nonempty;
* `supportFun_pyr`: `h_{pyr v cs}(x) = max (x_v, h_B(x))`;
* `pyr_generic`: an identity of indicator functions at generic points of the facet transfers to
  the pyramids (coning).
-/

open Finset

namespace AuthorReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem isClosed_facetPoly (v : ι) (cs : Finset (Constraint ι)) : IsClosed (facetPoly v cs) := by
  have hdot : ∀ a : ι → ℝ, Continuous fun p : ι → ℝ ↦ a ⬝ᵥ p := fun a ↦ by
    unfold dotProduct; fun_prop
  have : facetPoly v cs = {p | ∑ i, p i = 1} ∩ ({p | p v = 0} ∩
      ⋂ c ∈ cs, {p | c.a ⬝ᵥ p ≤ c.b}) := by
    ext p; simp [facetPoly]
  rw [this]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
    (IsClosed.inter (isClosed_eq (continuous_apply v) continuous_const)
    (isClosed_biInter fun c _ ↦ isClosed_le (hdot c.a) continuous_const))

/-- The normal vector of a homogenized constraint, evaluated at any point. -/
theorem Constraint.homog_a_dotProduct (v : ι) (c : Constraint ι) (p : ι → ℝ) :
    (c.homog v).a ⬝ᵥ p = c.a ⬝ᵥ p + (c.b - c.a v) * p v := by
  have : (c.homog v).a = c.a + Pi.single v (c.b - c.a v) := by
    funext i
    by_cases h : i = v
    · subst h; simp [Constraint.homog]
    · simp [Constraint.homog, h]
  rw [this, add_dotProduct, single_dotProduct]

/-- The normal vector of a homogenized constraint, evaluated at a point of the cone over the
facet. -/
theorem Constraint.homog_a_dotProduct_cone (v : ι) (c : Constraint ι) (t : ℝ) {q : ι → ℝ}
    (hq : q v = 0) :
    (c.homog v).a ⬝ᵥ (t • Pi.single v 1 + (1 - t) • q) = c.b * t + (1 - t) * (c.a ⬝ᵥ q) := by
  rw [Constraint.homog_a_dotProduct]
  simp only [dotProduct_add, dotProduct_smul, dotProduct_single, Pi.add_apply, Pi.smul_apply,
    Pi.single_eq_same, hq, smul_eq_mul]
  ring

theorem mem_pyr_iff {v : ι} {cs : Finset (Constraint ι)} {p : ι → ℝ} :
    p ∈ pyr v cs ↔ ∑ i, p i = 1 ∧ 0 ≤ p v ∧ p v ≤ 1 ∧
      ∀ c ∈ cs, (c.homog v).a ⬝ᵥ p ≤ c.b := by
  simp only [pyr, hpoly, pyrCons, Set.mem_ofPred_eq, Finset.forall_mem_insert,
    Finset.forall_mem_image, neg_dotProduct, single_dotProduct, one_mul, neg_nonpos]
  exact Iff.rfl

/-- Writing a point with `p v ≠ 1` as a point of the cone over the facet `{p_v = 0}`. -/
theorem exists_cone_decomp {v : ι} {p : ι → ℝ} (hp : p v ≠ 1) :
    ∃ q : ι → ℝ, q v = 0 ∧ (∑ i, p i = 1 → ∑ i, q i = 1) ∧
      p = p v • Pi.single v 1 + (1 - p v) • q := by
  have h1 : 1 - p v ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  refine ⟨(1 - p v)⁻¹ • (p - p v • Pi.single v 1), by simp, fun hs ↦ ?_, ?_⟩
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ,
      ite_true, hs, mul_one]
    field_simp
  · rw [smul_smul, mul_inv_cancel₀ h1, one_smul]; abel

/-- Membership in the pyramid for a point of the cone over the facet below the apex. -/
theorem mem_pyr_iff_of_cone {v : ι} {cs : Finset (Constraint ι)} {t : ℝ} {q : ι → ℝ}
    (hq : q v = 0) (hqs : ∑ i, q i = 1) (ht : t < 1) :
    t • Pi.single v 1 + (1 - t) • q ∈ pyr v cs ↔ 0 ≤ t ∧ q ∈ facetPoly v cs := by
  have ht' : 0 < 1 - t := sub_pos.mpr ht
  have hsum : ∑ i, (t • Pi.single v 1 + (1 - t) • q : ι → ℝ) i = 1 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ, ite_true, hqs]
    ring
  have hv : (t • Pi.single v 1 + (1 - t) • q : ι → ℝ) v = t := by simp [hq]
  rw [mem_pyr_iff, hv]
  simp only [hsum, true_and, facetPoly, Set.mem_ofPred_eq, hqs, hq,
    Constraint.homog_a_dotProduct_cone v _ t hq, ht.le]
  refine and_congr_right fun _ ↦ forall₂_congr fun c _ ↦ ?_
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem pyr_eq {v : ι} {cs : Finset (Constraint ι)} (hne : (facetPoly v cs).Nonempty)
    (hb : Bornology.IsBounded (facetPoly v cs)) :
    pyr v cs = {p | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ q ∈ facetPoly v cs,
      p = t • Pi.single v 1 + (1 - t) • q} := by
  ext p
  constructor
  · intro hp
    obtain ⟨hs, h0, h1, hc⟩ := mem_pyr_iff.mp hp
    rcases h1.lt_or_eq with h1 | h1
    · obtain ⟨q, hqv, hqs, hpq⟩ := exists_cone_decomp h1.ne
      have := (mem_pyr_iff_of_cone (cs := cs) hqv (hqs hs) h1).mp (by rw [← hpq]; exact hp)
      exact ⟨_, ⟨h0, h1.le⟩, q, this.2, hpq⟩
    · -- `p v = 1`: the direction `d = p - e_v` is a recession direction of the facet polytope
      obtain ⟨q₀, hq₀⟩ := hne
      set d := p - Pi.single v 1 with hd
      have hdv : d v = 0 := by simp [hd, h1]
      have hds : ∑ i, d i = 0 := by
        simp [hd, Finset.sum_sub_distrib, hs]
      have hdc : ∀ c ∈ cs, c.a ⬝ᵥ d ≤ 0 := by
        intro c hcs
        have := hc c hcs
        rw [Constraint.homog_a_dotProduct, h1] at this
        simp only [hd, dotProduct_sub, dotProduct_single, mul_one]
        linarith
      have hmem : ∀ s : ℝ, 0 ≤ s → q₀ + s • d ∈ facetPoly v cs := by
        intro s hs0
        obtain ⟨h1', h2', h3'⟩ := hq₀
        refine ⟨?_, ?_, fun c hcs ↦ ?_⟩
        · simp [Finset.sum_add_distrib, ← Finset.mul_sum, h1', hds]
        · simp [h2', hdv]
        · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
          nlinarith [h3' c hcs, hdc c hcs]
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
      have hd0 : d = 0 := by
        by_contra hne0
        have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hne0
        set s := (C + ‖q₀‖ + 1) / ‖d‖
        have hs0 : 0 ≤ s := by
          have : 0 ≤ C := (norm_nonneg _).trans (hC _ (hmem 0 le_rfl))
          positivity
        have h := hC _ (hmem s hs0)
        have h2 : ‖s • d‖ ≤ ‖q₀ + s • d‖ + ‖q₀‖ := by
          have := norm_sub_le (q₀ + s • d) q₀
          simpa using this
        rw [norm_smul, Real.norm_of_nonneg hs0, div_mul_cancel₀ _ hpos.ne'] at h2
        linarith
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, q₀, hq₀, ?_⟩
      rw [sub_self, zero_smul, add_zero, one_smul]
      exact sub_eq_zero.mp hd0
  · rintro ⟨t, ⟨h0, h1⟩, q, ⟨hqs, hqv, hqc⟩, rfl⟩
    rcases h1.lt_or_eq with h1 | rfl
    · exact (mem_pyr_iff_of_cone hqv hqs h1).mpr ⟨h0, hqs, hqv, hqc⟩
    · rw [sub_self, zero_smul, add_zero, one_smul, mem_pyr_iff]
      refine ⟨by simp [Finset.sum_pi_single'], by simp, by simp, fun c _ ↦ ?_⟩
      rw [Constraint.homog_a_dotProduct]
      simp

theorem isBounded_pyr {v : ι} {cs : Finset (Constraint ι)} (hne : (facetPoly v cs).Nonempty)
    (hb : Bornology.IsBounded (facetPoly v cs)) : Bornology.IsBounded (pyr v cs) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  refine isBounded_iff_forall_norm_le.mpr ⟨‖(Pi.single v 1 : ι → ℝ)‖ + C, ?_⟩
  rw [pyr_eq hne hb]
  rintro _ ⟨t, ⟨h0, h1⟩, q, hq, rfl⟩
  have h1' : 0 ≤ 1 - t := sub_nonneg.mpr h1
  calc ‖t • Pi.single v 1 + (1 - t) • q‖
      ≤ ‖t • (Pi.single v 1 : ι → ℝ)‖ + ‖(1 - t) • q‖ := norm_add_le _ _
    _ = t * ‖(Pi.single v 1 : ι → ℝ)‖ + (1 - t) * ‖q‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h0, Real.norm_of_nonneg h1']
    _ ≤ 1 * ‖(Pi.single v 1 : ι → ℝ)‖ + 1 * C := by
        have hC0 : 0 ≤ C := (norm_nonneg q).trans (hC q hq)
        have ha := mul_le_mul_of_nonneg_right h1 (norm_nonneg (Pi.single v 1 : ι → ℝ))
        have hb := mul_le_mul_of_nonneg_left (hC q hq) h1'
        have hc := mul_le_mul_of_nonneg_right (by linarith : 1 - t ≤ 1) hC0
        linarith
    _ = _ := by ring

theorem supportFun_pyr {v : ι} {cs : Finset (Constraint ι)} (hne : (facetPoly v cs).Nonempty)
    (hb : Bornology.IsBounded (facetPoly v cs)) (x : ι → ℝ) :
    supportFun (pyr v cs) x = max (x v) (supportFun (facetPoly v cs) x) := by
  have hpb := isBounded_pyr hne hb
  have heq := pyr_eq hne hb
  obtain ⟨q₀, hq₀⟩ := hne
  have hapex : Pi.single v 1 ∈ pyr v cs := by
    rw [heq]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, q₀, hq₀, by simp⟩
  have hsub : ∀ q ∈ facetPoly v cs, q ∈ pyr v cs := fun q hq ↦ by
    rw [heq]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, q, hq, by simp⟩
  refine le_antisymm (supportFun_le ⟨_, hapex⟩ fun p hp ↦ ?_) (max_le ?_ ?_)
  · rw [heq] at hp
    obtain ⟨t, ⟨h0, h1⟩, q, hq, rfl⟩ := hp
    have hq' := le_supportFun hb hq x
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, single_dotProduct, one_mul,
      smul_eq_mul, smul_eq_mul]
    have h1' : 0 ≤ 1 - t := sub_nonneg.mpr h1
    calc t * x v + (1 - t) * (q ⬝ᵥ x)
        ≤ t * max (x v) (supportFun (facetPoly v cs) x) +
          (1 - t) * max (x v) (supportFun (facetPoly v cs) x) := by
          gcongr
          · exact le_max_left _ _
          · exact hq'.trans (le_max_right _ _)
      _ = _ := by ring
  · simpa [single_dotProduct] using le_supportFun hpb hapex x
  · exact supportFun_le ⟨q₀, hq₀⟩ fun q hq ↦ le_supportFun hpb (hsub q hq) x

omit [Fintype ι] in
theorem pyrCons_mono {v : ι} {cs cs' : Finset (Constraint ι)} (h : cs ⊆ cs') :
    pyrCons v cs ⊆ pyrCons v cs' :=
  Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image h))

/-- The constraints of a pyramid are nonconstant if the facet constraints are nonconstant
on the coordinates different from the apex. -/
theorem isNonconst_of_mem_pyrCons {v : ι} {G : Finset (Constraint ι)}
    (hG : ∀ g ∈ G, ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j) (hn : 2 ≤ Fintype.card ι) :
    ∀ g ∈ pyrCons v G, g.IsNonconst := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hn v
  intro g hg
  simp only [pyrCons, Finset.mem_insert, Finset.mem_image] at hg
  rcases hg with rfl | rfl | ⟨c, hc, rfl⟩
  · exact ⟨v, w, by simp [hw]⟩
  · exact ⟨v, w, by simp [hw]⟩
  · obtain ⟨i, j, hi, hj, hij⟩ := hG c hc
    exact ⟨i, j, by simpa [Constraint.homog, Function.update_of_ne hi,
      Function.update_of_ne hj] using hij⟩

/-- **Coning.** An identity between indicator functions of facet polytopes at generic points of
the facet gives the same identity for the pyramids at generic points of `∑ pᵢ = 1`. -/
theorem pyr_generic {κ : Type*} (v : ι) (s : Finset κ) (c : κ → ℝ)
    (cs : κ → Finset (Constraint ι)) (G : Finset (Constraint ι))
    (hgen : ∀ q : ι → ℝ, ∑ j, q j = 1 → q v = 0 → (∀ g ∈ G, g.a ⬝ᵥ q ≠ g.b) →
      ∑ i ∈ s, c i * (facetPoly v (cs i)).indicator 1 q = 0)
    (p : ι → ℝ) (hp : ∑ j, p j = 1) (hpG : ∀ g ∈ pyrCons v G, g.a ⬝ᵥ p ≠ g.b) :
    ∑ i ∈ s, c i * (pyr v (cs i)).indicator 1 p = 0 := by
  have h0 : p v ≠ 0 := by
    have := hpG ⟨-Pi.single v 1, 0⟩ (by simp [pyrCons])
    simpa [neg_dotProduct, single_dotProduct] using this
  have h1 : p v ≠ 1 := by
    have := hpG ⟨Pi.single v 1, 1⟩ (by simp [pyrCons])
    simpa [single_dotProduct] using this
  by_cases hin : 0 < p v ∧ p v < 1
  · obtain ⟨q, hqv, hqs, hpq⟩ := exists_cone_decomp h1
    have hqs := hqs hp
    have hq : ∀ g ∈ G, g.a ⬝ᵥ q ≠ g.b := by
      intro g hg hgq
      have := hpG (g.homog v) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ hg)))
      rw [hpq, Constraint.homog_a_dotProduct_cone v g _ hqv, hgq] at this
      exact this (by simp only [Constraint.homog]; ring)
    rw [← hgen q hqs hqv hq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    have hiff : p ∈ pyr v (cs i) ↔ q ∈ facetPoly v (cs i) := by
      rw [hpq, mem_pyr_iff_of_cone hqv hqs hin.2]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hin.1.le, h⟩⟩
    by_cases hmem : q ∈ facetPoly v (cs i)
    · rw [Set.indicator_of_mem (hiff.mpr hmem), Set.indicator_of_mem hmem, Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem (mt hiff.mp hmem), Set.indicator_of_notMem hmem]
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Set.indicator_of_notMem, mul_zero]
    intro hmem
    obtain ⟨-, ha, hb, -⟩ := mem_pyr_iff.mp hmem
    exact hin ⟨lt_of_le_of_ne ha (Ne.symm h0), lt_of_le_of_ne hb h1⟩

end

end AuthorReal

-- Source module: Solutions/AuthorSubdivision.lean


/-!
# The simplex and the coned dilated facets

* `supportFun_simplex`: the support function of the standard simplex is `max (x₁, …, xₙ)`.
* `subdivision`: for `∅ ≠ R ⊊ ι` with complement `C`, the pyramids `pyr_{e_v}(Q_{v,R})` for
  `v ∈ C` are translates of `|C| T_v`, where the simplices `T_v = {p ∈ Δ | p_v ≤ p_w ∀ w ∈ C}`
  subdivide `Δ`. Hence `∑_{v ∈ C} h_{pyr_{e_v}(Q_{v,R})} ≡ |C| h_Δ`.
-/

open Finset

namespace AuthorReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Membership in the standard simplex. -/
theorem mem_simplex_iff {p : ι → ℝ} :
    p ∈ (simplex : Set (ι → ℝ)) ↔ ∑ i, p i = 1 ∧ ∀ i, 0 ≤ p i := by
  simp [simplex, simplexCons, hpoly, neg_dotProduct, single_dotProduct]

/-- The standard simplex is bounded. -/
theorem isBounded_simplex : Bornology.IsBounded (simplex : Set (ι → ℝ)) := by
  refine (Metric.isBounded_Icc (0 : ι → ℝ) 1).subset fun p hp ↦ ?_
  rw [mem_simplex_iff] at hp
  refine ⟨fun i ↦ hp.2 i, fun i ↦ ?_⟩
  rw [Pi.one_apply, ← hp.1]
  exact single_le_sum (fun j _ ↦ hp.2 j) (mem_univ i)

omit [Fintype ι] in
@[simp]
theorem Constraint.homog_b (v : ι) (c : Constraint ι) : (c.homog v).b = c.b := rfl

/-- Homogenizing the constraint `-p_i ≤ b` with respect to `v ≠ i`. -/
theorem homog_neg_single_dotProduct {v i : ι} (hi : i ≠ v) (b : ℝ) (p : ι → ℝ) :
    (Constraint.homog v ⟨-Pi.single i 1, b⟩).a ⬝ᵥ p = -p i + b * p v := by
  have : Function.update (-Pi.single i 1 : ι → ℝ) v b = -Pi.single i 1 + Pi.single v b := by
    ext j
    rcases eq_or_ne j v with rfl | hj
    · simp [hi]
    · simp [hj]
  simp [Constraint.homog, this, add_dotProduct, neg_dotProduct, single_dotProduct]

/-- Membership in the pyramid `pyr_{e_v}(Q_{v,R})`. -/
theorem mem_pyr_qCons_iff {v : ι} {R : Finset ι} {p : ι → ℝ} :
    p ∈ pyr v (qCons v R) ↔ ∑ i, p i = 1 ∧ 0 ≤ p v ∧ p v ≤ 1 ∧
      ∀ i, i ≠ v → (i ∈ R → 0 ≤ p i) ∧ (i ∉ R → p v - 1 ≤ p i) := by
  simp only [pyr, pyrCons, hpoly, Set.mem_ofPred_eq, forall_mem_insert, qCons, image_image,
    forall_mem_image, mem_erase, mem_univ, and_true, Function.comp_apply]
  simp only [neg_dotProduct, single_dotProduct, one_mul, neg_nonpos]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i ↦ ?_)))
  refine imp_congr_right fun hi ↦ ?_
  split_ifs with h
  · simp [homog_neg_single_dotProduct hi, h]
  · rw [homog_neg_single_dotProduct hi, Constraint.homog_b]
    constructor
    · intro h'
      exact ⟨fun hR ↦ absurd hR h, fun _ ↦ by linarith⟩
    · rintro ⟨-, h'⟩
      linarith [h' h]

/-- Membership in `T_v = {p ∈ Δ | p_v ≤ p_w ∀ w ∈ C}`. -/
theorem mem_hpoly_tCons_iff {C : Finset ι} {v : ι} {p : ι → ℝ} :
    p ∈ hpoly (tCons C v) ↔ p ∈ (simplex : Set (ι → ℝ)) ∧ ∀ w ∈ C.erase v, p v ≤ p w := by
  simp only [mem_erase, mem_simplex_iff]
  simp only [tCons, hpoly, simplexCons, Set.mem_ofPred_eq, mem_union, mem_image, mem_univ,
    true_and, mem_erase]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨⟨hs, fun i ↦ ?_⟩, fun w ⟨hw, hwC⟩ ↦ ?_⟩
    · simpa [neg_dotProduct, single_dotProduct] using h _ (Or.inl ⟨i, rfl⟩)
    · simpa [sub_dotProduct, single_dotProduct] using h _ (Or.inr ⟨w, ⟨hw, hwC⟩, rfl⟩)
  · rintro ⟨⟨hs, h0⟩, h⟩
    refine ⟨hs, ?_⟩
    rintro c (⟨i, rfl⟩ | ⟨w, ⟨hw, hwC⟩, rfl⟩)
    · simpa [neg_dotProduct, single_dotProduct] using h0 i
    · simpa [sub_dotProduct, single_dotProduct] using h w ⟨hw, hwC⟩

omit [Fintype ι] in
/-- Unit vectors are nonnegative. -/
theorem single_one_nonneg (i j : ι) : 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ) j := by
  rw [Pi.single_apply]
  split_ifs <;> norm_num

/-- The unit vectors lie in the simplex. -/
theorem single_mem_simplex (i : ι) : (Pi.single i 1 : ι → ℝ) ∈ (simplex : Set (ι → ℝ)) :=
  mem_simplex_iff.2 ⟨by simp, fun j ↦ single_one_nonneg i j⟩

theorem supportFun_simplex [Nonempty ι] (x : ι → ℝ) :
    supportFun (simplex : Set (ι → ℝ)) x = univ.sup' univ_nonempty x := by
  apply le_antisymm
  · obtain ⟨i⟩ := ‹Nonempty ι›
    refine supportFun_le ⟨_, single_mem_simplex i⟩ fun p hp ↦ ?_
    rw [mem_simplex_iff] at hp
    calc p ⬝ᵥ x = ∑ j, p j * x j := rfl
      _ ≤ ∑ j, p j * univ.sup' univ_nonempty x :=
        sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (le_sup' x (mem_univ j)) (hp.2 j)
      _ = _ := by rw [← sum_mul, hp.1, one_mul]
  · refine sup'_le _ _ fun i _ ↦ ?_
    simpa [single_dotProduct] using le_supportFun isBounded_simplex (single_mem_simplex i) x

theorem facetPoly_qCons_nonempty {v : ι} (hn : 2 ≤ Fintype.card ι) (R : Finset ι) :
    (facetPoly v (qCons v R)).Nonempty := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  refine ⟨Pi.single w 1, by simp, by simp [hw.symm], fun c hc ↦ ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hc
  have := single_one_nonneg i w
  split_ifs <;> simp <;> linarith

theorem isBounded_facetPoly_qCons (v : ι) (R : Finset ι) :
    Bornology.IsBounded (facetPoly v (qCons v R)) := by
  refine (Metric.isBounded_Icc (-1 : ι → ℝ) (fun _ ↦ (Fintype.card ι : ℝ))).subset
    fun p hp ↦ ?_
  obtain ⟨hs, hv, hc⟩ := hp
  have hge : ∀ i, -1 ≤ p i := by
    intro i
    rcases eq_or_ne i v with rfl | hi
    · rw [hv]; norm_num
    have := hc _ (mem_image_of_mem _ (mem_erase.2 ⟨hi, mem_univ i⟩))
    split_ifs at this <;> simp [neg_dotProduct, single_dotProduct] at this <;> linarith
  refine ⟨fun i ↦ by simpa using hge i, fun i ↦ ?_⟩
  have : p i + 1 ≤ ∑ j, (p j + 1) :=
    single_le_sum (f := fun j ↦ p j + 1) (fun j _ ↦ by linarith [hge j]) (mem_univ i)
  rw [sum_add_distrib, hs] at this
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at this
  change p i ≤ (Fintype.card ι : ℝ)
  linarith

/-- The coordinate sum of an indicator vector. -/
theorem sum_indVec (S : Finset ι) : ∑ i, indVec S i = S.card := by
  simp [indVec]

/-- The pyramid `pyr_{e_v}(Q_{v,R})` is a translate of `|C| T_v`, where `C = Rᶜ`. -/
theorem pyr_qCons_eq {R : Finset ι} {v : ι} (hv : v ∈ Rᶜ) :
    pyr v (qCons v R) =
      (fun l ↦ (#Rᶜ : ℝ) • l + -indVec (Rᶜ.erase v)) '' hpoly (tCons Rᶜ v) := by
  set k : ℝ := (#Rᶜ : ℝ)
  have hk0 : 0 < k := by simpa [k] using card_pos.2 ⟨v, hv⟩
  have hk : (#(Rᶜ.erase v) : ℝ) = k - 1 := by
    rw [card_erase_of_mem hv, Nat.cast_sub (card_pos.2 ⟨v, hv⟩), Nat.cast_one]
  have hiv : indVec (Rᶜ.erase v) v = 0 := by simp [indVec]
  have hiR : ∀ i ∈ R, indVec (Rᶜ.erase v) i = 0 := fun i hi ↦ by simp [indVec, hi]
  have hiC : ∀ i, i ≠ v → i ∉ R → indVec (Rᶜ.erase v) i = 1 := fun i h1 h2 ↦ by
    simp [indVec, h1, h2]
  ext p
  constructor
  · intro hp
    obtain ⟨hs, h0, h1, hi⟩ := mem_pyr_qCons_iff.1 hp
    refine ⟨k⁻¹ • (p + indVec (Rᶜ.erase v)), ?_, ?_⟩
    · rw [mem_hpoly_tCons_iff, mem_simplex_iff]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      refine ⟨⟨?_, fun i ↦ ?_⟩, fun w hw ↦ ?_⟩
      · rw [← mul_sum, sum_add_distrib, hs, sum_indVec, hk]
        field_simp
        ring
      · refine mul_nonneg (inv_nonneg.2 hk0.le) ?_
        rcases eq_or_ne i v with rfl | hiv'
        · rw [hiv]; linarith
        by_cases hR : i ∈ R
        · rw [hiR i hR]; linarith [(hi i hiv').1 hR]
        · rw [hiC i hiv' hR]; linarith [(hi i hiv').2 hR]
      · obtain ⟨hwv, hwC⟩ := mem_erase.1 hw
        have hwR := mem_compl.1 hwC
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hk0.le)
        rw [hiv, hiC w hwv hwR]
        linarith [(hi w hwv).2 hwR]
    · ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      field_simp
      ring
  · rintro ⟨l, hl, rfl⟩
    rw [mem_hpoly_tCons_iff, mem_simplex_iff] at hl
    obtain ⟨⟨hs, h0⟩, hle⟩ := hl
    have hCsum : k * l v ≤ 1 :=
      calc k * l v = ∑ _w ∈ Rᶜ, l v := by simp [k]
        _ ≤ ∑ w ∈ Rᶜ, l w := sum_le_sum fun w hw ↦ by
          rcases eq_or_ne w v with rfl | hwv
          · exact le_rfl
          · exact hle w (mem_erase.2 ⟨hwv, hw⟩)
        _ ≤ ∑ w, l w := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ ↦ h0 w
        _ = 1 := hs
    rw [mem_pyr_qCons_iff]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hiv, neg_zero, add_zero]
    refine ⟨?_, mul_nonneg hk0.le (h0 v), hCsum, fun i hiv' ↦ ⟨fun hR ↦ ?_, fun hR ↦ ?_⟩⟩
    · rw [sum_add_distrib, ← mul_sum, hs, sum_neg_distrib, sum_indVec, hk]
      ring
    · rw [hiR i hR, neg_zero, add_zero]
      exact mul_nonneg hk0.le (h0 i)
    · rw [hiC i hiv' hR]
      have := hle i (mem_erase.2 ⟨hiv', mem_compl.2 hR⟩)
      nlinarith

/-- The simplices `T_v` are bounded. -/
theorem isBounded_hpoly_tCons (C : Finset ι) (v : ι) : Bornology.IsBounded (hpoly (tCons C v)) :=
  isBounded_simplex.subset fun _ hp ↦ (mem_hpoly_tCons_iff.1 hp).1

/-- `h_{pyr_{e_v}(Q_{v,R})} = |C| h_{T_v} - ⟪1_{C \ v}, ·⟫`. -/
theorem supportFun_pyr_qCons {R : Finset ι} (hR : R.Nonempty) {v : ι} (hv : v ∈ Rᶜ) :
    supportFun (pyr v (qCons v R)) = (#Rᶜ : ℝ) • supportFun (hpoly (tCons Rᶜ v)) +
      fun x ↦ (-indVec (Rᶜ.erase v)) ⬝ᵥ x := by
  obtain ⟨w, hw⟩ := hR
  have hne : (hpoly (tCons Rᶜ v)).Nonempty := by
    refine ⟨Pi.single w 1, mem_hpoly_tCons_iff.2 ⟨single_mem_simplex w, fun u hu ↦ ?_⟩⟩
    have hvw : v ≠ w := fun h ↦ mem_compl.1 hv (h ▸ hw)
    simp [Pi.single_apply, hvw]
    split_ifs <;> norm_num
  ext x
  rw [pyr_qCons_eq hv, supportFun_image_smul_add (isBounded_hpoly_tCons _ _) hne
    (by simpa using card_pos.2 ⟨v, hv⟩)]
  rfl

/-- The simplices `T_v`, `v ∈ C`, subdivide `Δ`: off the hyperplanes `p_v = p_w`, a point of `Δ`
lies in exactly one `T_v`. -/
theorem sum_indicator_tCons_sub_simplex {C : Finset ι} (hC : C.Nonempty) {p : ι → ℝ}
    (hpG : ∀ v ∈ C, ∀ w ∈ C, v ≠ w → p v ≠ p w) :
    -1 * (simplex : Set (ι → ℝ)).indicator (1 : (ι → ℝ) → ℝ) p +
      ∑ v ∈ C, 1 * (hpoly (tCons C v)).indicator (1 : (ι → ℝ) → ℝ) p = 0 := by
  by_cases hp : p ∈ (simplex : Set (ι → ℝ))
  · obtain ⟨v₀, hv₀, hmin⟩ := exists_min_image C p hC
    have hmem : p ∈ hpoly (tCons C v₀) :=
      mem_hpoly_tCons_iff.2 ⟨hp, fun w hw ↦ hmin w (mem_of_mem_erase hw)⟩
    rw [sum_eq_single v₀]
    · simp [Set.indicator_of_mem hp, Set.indicator_of_mem hmem]
    · intro u hu hne
      rw [Set.indicator_of_notMem, mul_zero]
      intro hpu
      have h1 := (mem_hpoly_tCons_iff.1 hpu).2 v₀ (mem_erase.2 ⟨hne.symm, hv₀⟩)
      exact hpG u hu v₀ hv₀ hne (le_antisymm h1 (hmin u hu))
    · exact fun h ↦ absurd hv₀ h
  · rw [Set.indicator_of_notMem hp, sum_eq_zero]
    · simp
    · intro u _
      rw [Set.indicator_of_notMem, mul_zero]
      exact fun h ↦ hp (mem_hpoly_tCons_iff.1 h).1

theorem subdivision {R : Finset ι} (hR : R.Nonempty) (hRu : R ≠ univ) :
    ∑ v ∈ Rᶜ, supportFun (pyr v (qCons v R)) - (Rᶜ.card : ℝ) • supportFun simplex ∈
      maxSpan ι (Fintype.card ι - 1) := by
  have hC : Rᶜ.Nonempty := (compl_ne_univ_iff_nonempty Rᶜ).1 (by rwa [compl_compl])
  have hn : 1 < Fintype.card ι := by
    obtain ⟨w, hw⟩ := hR
    obtain ⟨v, hv⟩ := hC
    exact Fintype.one_lt_card_iff.2 ⟨v, w, fun h ↦ mem_compl.1 hv (h ▸ hw)⟩
  set G : Finset (Constraint ι) := simplexCons ∪ Rᶜ.biUnion (tCons Rᶜ) with hG_def
  have hS : ∀ g ∈ (simplexCons : Finset (Constraint ι)), g.IsNonconst := by
    intro g hg
    obtain ⟨i, -, rfl⟩ := mem_image.1 hg
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hn i
    exact ⟨i, j, by simp [hj]⟩
  have hG : ∀ g ∈ G, g.IsNonconst := by
    intro g hg
    simp only [G, mem_union, mem_biUnion] at hg
    obtain hg | ⟨v, -, hg⟩ := hg
    · exact hS g hg
    simp only [tCons, mem_union, mem_image] at hg
    obtain hg | ⟨w, hw, rfl⟩ := hg
    · exact hS g hg
    · have hwv := ne_of_mem_erase hw
      exact ⟨v, w, by norm_num [hwv, hwv.symm]⟩
  have ht := transfer (κ := Option ι) (insertNone Rᶜ) (fun o ↦ o.elim (-1) fun _ ↦ 1)
    (fun o ↦ o.elim simplexCons (tCons Rᶜ)) G hG ?_ ?_ ?_
  rotate_left
  · intro o ho
    cases o with
    | none => exact subset_union_left
    | some v =>
      exact (subset_biUnion_of_mem (tCons Rᶜ) (some_mem_insertNone.1 ho)).trans
        subset_union_right
  · intro o _
    cases o with
    | none => exact isBounded_simplex
    | some v => exact isBounded_hpoly_tCons _ _
  · intro p _ hpG
    rw [sum_insertNone]
    simp only [Option.elim]
    refine sum_indicator_tCons_sub_simplex hC fun v hv w hw hvw h ↦ ?_
    refine hpG ⟨Pi.single v 1 - Pi.single w 1, 0⟩ ?_ ?_
    · refine mem_union_right _ (mem_biUnion.2 ⟨v, hv, mem_union_right _ ?_⟩)
      exact mem_image.2 ⟨w, mem_erase.2 ⟨hvw.symm, hw⟩, rfl⟩
    · simp [sub_dotProduct, single_dotProduct, h]
  rw [sum_insertNone] at ht
  simp only [Option.elim] at ht
  have key : ∑ v ∈ Rᶜ, supportFun (pyr v (qCons v R)) - (Rᶜ.card : ℝ) • supportFun simplex =
      (#Rᶜ : ℝ) • ((-1 : ℝ) • supportFun simplex +
        ∑ v ∈ Rᶜ, (1 : ℝ) • supportFun (hpoly (tCons Rᶜ v))) +
      ∑ v ∈ Rᶜ, fun x ↦ (-indVec (Rᶜ.erase v)) ⬝ᵥ x := by
    rw [sum_congr rfl fun v hv ↦ supportFun_pyr_qCons hR hv, sum_add_distrib, ← smul_sum]
    simp only [one_smul, neg_one_smul, smul_add, smul_neg]
    abel
  rw [key]
  exact add_mem (Submodule.smul_mem _ _ ht)
    (sum_mem fun v _ ↦ linear_mem_maxSpan _ (by omega))

end

end AuthorReal

-- Source module: Solutions/AuthorThermostat.lean


/-!
# Counting walks: the thermostat lemma

Fix a vertex `v` and write `V = ι \ {v}`, `m = |V|`. For a generic point `q` of the facet
`{∑ qᵢ = 1, q_v = 0}` with `s` positive coordinates we show

* `thermostat`: `∑_{π, M} (-1)^{|M|} 1_{B_{π,M}}(q) = 1_{E_v}(q) · (-1)^{s-1} s! (m-s)!`,
  where `π` runs over the orderings of `V` and `E_v = Q_{v,∅}`;
* `qcount`: `∑_{∅ ≠ R ⊆ V} c_{|R|} 1_{Q_{v,R}}(q) = 1_{E_v}(q) ∑_{r=1}^{m} c_r (s choose r)`.

We also record that all constraints involved are nonconstant off the apex `v`.
-/

open Finset

namespace AuthorReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem mem_orderings {X : Finset ι} {l : List ι} : l ∈ orderings X ↔ l.Nodup ∧ l.toFinset = X := by
  rw [orderings, List.mem_toFinset, List.mem_permutations]
  refine ⟨fun h ↦ ⟨h.nodup_iff.2 X.nodup_toList, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rw [List.toFinset_eq_of_perm _ _ h, toList_toFinset]
  · exact List.perm_of_nodup_nodup_toFinset_eq h₁ X.nodup_toList (by rw [h₂, toList_toFinset])

omit [Fintype ι] in
/-- The empty set has exactly one ordering. -/
@[simp]
theorem orderings_empty : orderings (∅ : Finset ι) = {[]} := by
  simp [orderings]

omit [Fintype ι] in
/-- Decomposing the orderings of a nonempty set according to their first element. -/
theorem sum_orderings_eq {β : Type*} [AddCommMonoid β] {X : Finset ι} (hX : X.Nonempty)
    (F : List ι → β) :
    ∑ l ∈ orderings X, F l = ∑ x ∈ X, ∑ l ∈ orderings (X.erase x), F (x :: l) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun p _ ↦ p.1 :: p.2) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · rintro ⟨x, l⟩ hp
    simp only [mem_sigma, mem_orderings] at hp ⊢
    obtain ⟨hx, hl, hl'⟩ := hp
    refine ⟨List.nodup_cons.2 ⟨fun h ↦ ?_, hl⟩, ?_⟩
    · simpa [hl'] using (List.mem_toFinset.2 h)
    · rw [List.toFinset_cons, hl', insert_erase hx]
  · rintro ⟨x, l⟩ _ ⟨y, l'⟩ _ h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro l hl
    rw [mem_orderings] at hl
    obtain ⟨hl, rfl⟩ := hl
    cases l with
    | nil => simp at hX
    | cons x t =>
      refine ⟨⟨x, t⟩, ?_, rfl⟩
      rw [List.nodup_cons] at hl
      simp only [mem_sigma, mem_orderings, List.toFinset_cons, mem_insert, true_or, true_and]
      refine ⟨hl.2, ?_⟩
      rw [erase_insert (by simpa using hl.1)]

/-! ### The walk weight -/

/-- The indicator `1_{[0, 1]}(u)`. -/
private def thermostatBoxA (u : ℝ) : ℝ := if 0 ≤ u ∧ u ≤ 1 then 1 else 0

/-- The indicator `1_{[-1, 0]}(q_x)`. -/
private def boxD (q : ι → ℝ) (x : ι) : ℝ := if -1 ≤ q x ∧ q x ≤ 0 then 1 else 0

/-- The signed weight of the walks along the list `l`, starting at the level `u`. -/
private def walkW (q : ι → ℝ) : ℝ → List ι → ℝ
  | _, [] => 1
  | u, x :: l => (boxD q x - thermostatBoxA u) * walkW q (u + q x) l

omit [Fintype ι] in
/-- `boxCons M pre l` only depends on `M ∩ l`. -/
theorem boxCons_congr {M M' : Finset ι} :
    ∀ (pre : Finset ι) (l : List ι), (∀ y ∈ l, y ∈ M ↔ y ∈ M') → boxCons M pre l = boxCons M' pre l
  | _, [], _ => rfl
  | pre, x :: l, h => by
    have hx := h x List.mem_cons_self
    simp only [boxCons, hx, boxCons_congr _ l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]

/-- Pairing with an indicator vector sums over the set. -/
theorem indVec_dotProduct (S : Finset ι) (q : ι → ℝ) : indVec S ⬝ᵥ q = ∑ i ∈ S, q i := by
  simp [indVec, dotProduct, ite_mul, Finset.sum_ite_mem]

/-- Unfolding one step of the feasibility condition of `boxCons`. -/
theorem forall_boxCons_cons (M pre : Finset ι) (x : ι) (l : List ι) (q : ι → ℝ) :
    (∀ c ∈ boxCons M pre (x :: l), c.a ⬝ᵥ q ≤ c.b) ↔
      (if x ∈ M then 0 ≤ ∑ i ∈ pre, q i ∧ ∑ i ∈ pre, q i ≤ 1 else -1 ≤ q x ∧ q x ≤ 0) ∧
      ∀ c ∈ boxCons M (insert x pre) l, c.a ⬝ᵥ q ≤ c.b := by
  rw [boxCons]
  simp only [mem_union, or_imp, forall_and]
  split_ifs <;>
  simp [indVec_dotProduct, neg_dotProduct, neg_le, and_comm]

private theorem ite_and_one_zero (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℝ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- Inclusion-exclusion over the markings of a list reproduces the walk weight. -/
private theorem sum_boxCons_eq_walkW (q : ι → ℝ) :
    ∀ (l : List ι) (pre : Finset ι), l.Nodup → (∀ x ∈ l, x ∉ pre) →
    ∑ M ∈ l.toFinset.powerset, (-1 : ℝ) ^ M.card *
      (if ∀ c ∈ boxCons M pre l, c.a ⬝ᵥ q ≤ c.b then 1 else 0) = walkW q (∑ i ∈ pre, q i) l
  | [], pre, _, _ => by simp [boxCons, walkW]
  | x :: l, pre, hnd, hpre => by
    rw [List.nodup_cons] at hnd
    have hxl : x ∉ l.toFinset := by simpa using hnd.1
    have hpre' : ∀ y ∈ l, y ∉ insert x pre := by
      intro y hy
      rw [mem_insert, not_or]
      exact ⟨fun h ↦ hnd.1 (h ▸ hy), hpre y (List.mem_cons_of_mem _ hy)⟩
    have hxpre : x ∉ pre := hpre x List.mem_cons_self
    rw [List.toFinset_cons, Finset.sum_powerset_insert hxl, walkW, add_comm _ (q x),
      ← sum_insert hxpre, ← sum_boxCons_eq_walkW q l _ hnd.2 hpre',
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M hM ↦ ?_
    have hxM : x ∉ M := fun h ↦ hxl (mem_powerset.1 hM h)
    have hcong : boxCons (insert x M) (insert x pre) l = boxCons M (insert x pre) l := by
      refine boxCons_congr _ _ fun y hy ↦ ?_
      have : y ≠ x := fun h ↦ hnd.1 (h ▸ hy)
      simp [this]
    simp only [forall_boxCons_cons, hcong, card_insert_of_notMem hxM, mem_insert_self,
      ite_true, hxM, ite_false, ite_and_one_zero, thermostatBoxA, boxD]
    ring

/-- The inner sum of the thermostat lemma over the markings of an ordering `h :: t`. -/
private theorem sum_markings_eq_walkW {v : ι} {q : ι → ℝ} (hq : ∑ i, q i = 1) (hqv : q v = 0)
    {h : ι} {t : List ι} (hnd : (h :: t).Nodup) :
    ∑ M ∈ markings (h :: t), (-1 : ℝ) ^ M.card * (facetPoly v (boxConsL M (h :: t))).indicator 1 q =
      walkW q (q h) t := by
  rw [List.nodup_cons] at hnd
  have := sum_boxCons_eq_walkW q t {h} hnd.2 fun x hx ↦ by
    rw [mem_singleton]
    rintro rfl
    exact hnd.1 hx
  rw [sum_singleton] at this
  rw [← this, markings, List.tail_cons]
  refine sum_congr rfl fun M _ ↦ ?_
  simp only [boxConsL, Set.indicator_apply, facetPoly, Set.mem_ofPred_eq, hq, hqv, true_and,
    Pi.one_apply]

/-! ### The closed form of the walk weights -/

/-- The starting level `∑_{V \ X} q` for the walks through `X`. -/
private def lev (v : ι) (q : ι → ℝ) (X : Finset ι) : ℝ := ∑ i ∈ univ.erase v \ X, q i

/-- The total signed weight of the walks through `X`. -/
private def gw (v : ι) (q : ι → ℝ) (X : Finset ι) : ℝ :=
  ∑ l ∈ orderings X, walkW q (lev v q X) l

/-- The indicator that all coordinates in `X` are `> -1`. -/
private def indGt (q : ι → ℝ) (X : Finset ι) : ℝ := if ∀ i ∈ X, -1 < q i then 1 else 0

private theorem lev_erase {v : ι} {q : ι → ℝ} {X : Finset ι} {x : ι} (hx : x ∈ X)
    (hXV : X ⊆ univ.erase v) : lev v q (X.erase x) = lev v q X + q x := by
  rw [lev, lev, sdiff_erase (hXV hx), sum_insert (fun h ↦ (mem_sdiff.1 h).2 hx), add_comm]

private theorem sum_add_lev {v : ι} (q : ι → ℝ) {X : Finset ι} (hXV : X ⊆ univ.erase v) :
    ∑ i ∈ X, q i + lev v q X = ∑ i ∈ univ.erase v, q i := by
  rw [lev, add_comm, sum_sdiff hXV]

private theorem indGt_erase {q : ι → ℝ} {X : Finset ι} {x : ι} (hx : -1 < q x) :
    indGt q (X.erase x) = indGt q X := by
  unfold indGt
  congr 1
  refine propext ⟨fun h i hi ↦ ?_, fun h i hi ↦ h i (mem_of_mem_erase hi)⟩
  by_cases hix : i = x
  · exact hix ▸ hx
  · exact h i (mem_erase.2 ⟨hix, hi⟩)

private theorem gw_eq_sum {v : ι} {q : ι → ℝ} {X : Finset ι} (hX : X.Nonempty)
    (hXV : X ⊆ univ.erase v) :
    gw v q X = ∑ x ∈ X, (boxD q x - thermostatBoxA (lev v q X)) * gw v q (X.erase x) := by
  rw [gw, sum_orderings_eq hX]
  refine sum_congr rfl fun x hx ↦ ?_
  simp only [walkW, gw, mul_sum, lev_erase hx hXV]

/-- The closed form of the walk weights. -/
private theorem gw_eq {v : ι} {q : ι → ℝ} (hsum : ∑ i ∈ univ.erase v, q i = 1)
    (h0 : ∀ i ∈ univ.erase v, q i ≠ 0) (h1 : ∀ i ∈ univ.erase v, q i ≠ -1)
    (hlev : ∀ X ⊆ univ.erase v, X.Nonempty → X ≠ univ.erase v → lev v q X ≠ 0 ∧ lev v q X ≠ 1)
    (X : Finset ι) (hXV : X ⊆ univ.erase v) (hXne : X ≠ univ.erase v) :
    (0 < lev v q X → gw v q X = (-1) ^ (X.filter fun i ↦ 0 < q i).card *
      ((X.filter fun i ↦ 0 < q i).card.factorial : ℝ) *
      ((X.filter fun i ↦ q i < 0).card.factorial : ℝ) * indGt q X) ∧
    (lev v q X < 0 → X.Nonempty → gw v q X = 0) := by
  induction X using Finset.strongInduction with
  | H X ih =>
  have hsumX := sum_add_lev q hXV
  rw [hsum] at hsumX
  rcases X.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ ↦ ?_, fun _ h ↦ absurd h (by simp)⟩
    simp [gw, walkW, indGt]
  have hl := hlev X hXV hne hXne
  -- facts about the subsets `X.erase x`
  have hsub : ∀ x ∈ X, X.erase x ⊆ univ.erase v := fun x _ ↦ (erase_subset x X).trans hXV
  have hne' : ∀ x ∈ X, X.erase x ≠ univ.erase v := fun x _ h ↦
    hXne (subset_antisymm hXV (h ▸ erase_subset x X))
  have IH := fun x (hx : x ∈ X) ↦ ih (X.erase x) (erase_ssubset hx) (hsub x hx) (hne' x hx)
  have hlev1 : ∀ x ∈ X, lev v q X + q x ≠ 1 → (X.erase x).Nonempty := by
    intro x hx h
    rw [nonempty_iff_ne_empty]
    intro he
    apply h
    rw [← lev_erase hx hXV, he, lev, sdiff_empty, hsum]
  have hq0 : ∀ x ∈ X, q x ≠ 0 := fun x hx ↦ h0 x (hXV hx)
  have hq1 : ∀ x ∈ X, q x ≠ -1 := fun x hx ↦ h1 x (hXV hx)
  rw [gw_eq_sum hne hXV]
  refine ⟨fun hpos ↦ ?_, fun hneg _ ↦ ?_⟩
  swap
  · -- negative level: only steps with `q x < 0` contribute, and they stay negative
    refine sum_eq_zero fun x hx ↦ ?_
    have hA : thermostatBoxA (lev v q X) = 0 := by
      rw [thermostatBoxA, ite_eq_right_iff]
      exact fun h ↦ absurd h.1 (not_le.2 hneg)
    unfold boxD
    split_ifs with hD
    · have hx0 : q x < 0 := lt_of_le_of_ne hD.2 (hq0 x hx)
      have hlt : lev v q X + q x < 0 := by linarith
      rw [(IH x hx).2 (by rwa [lev_erase hx hXV]) (hlev1 x hx (by linarith))]
      ring
    · rw [hA]
      ring
  set P := X.filter fun i ↦ 0 < q i with hP
  set N := X.filter fun i ↦ q i < 0 with hN
  rcases lt_or_gt_of_ne hl.2 with hlt1 | hgt1
  · -- level in `(0, 1)`: only the steps with `q x > 0` contribute
    have hA : thermostatBoxA (lev v q X) = 1 := if_pos ⟨hpos.le, hlt1.le⟩
    have hterm : ∀ x ∈ X, (boxD q x - thermostatBoxA (lev v q X)) * gw v q (X.erase x) =
        if 0 < q x then -((-1) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) *
          (N.card.factorial : ℝ) * indGt q X) else 0 := by
      intro x hx
      rw [hA]
      by_cases hx0 : 0 < q x
      · have hD : boxD q x = 0 := if_neg fun h ↦ (h.2.trans_lt hx0).false
        have hxP : x ∈ P := mem_filter.2 ⟨hx, hx0⟩
        have hxN : x ∉ N := fun h ↦ ((mem_filter.1 h).2.trans hx0).false
        rw [if_pos hx0, hD, (IH x hx).1 (by rw [lev_erase hx hXV]; linarith), filter_erase,
          filter_erase, ← hP, ← hN, erase_eq_of_notMem hxN, card_erase_of_mem hxP,
          indGt_erase (by linarith)]
        ring
      · have hx0' : q x < 0 := lt_of_le_of_ne (not_lt.1 hx0) (hq0 x hx)
        rw [if_neg hx0]
        by_cases hx1 : -1 < q x
        · have hD : boxD q x = 1 := if_pos ⟨hx1.le, hx0'.le⟩
          rw [hD]
          ring
        · have hx1' : q x < -1 := lt_of_le_of_ne (not_lt.1 hx1) (hq1 x hx)
          have hD : boxD q x = 0 := if_neg fun h ↦ (h.1.trans_lt hx1').false
          rw [hD, (IH x hx).2 (by rw [lev_erase hx hXV]; linarith)
            (hlev1 x hx (by linarith))]
          ring
    rw [sum_congr rfl hterm, ← sum_filter, ← hP, sum_const, nsmul_eq_mul]
    have hPpos : 0 < P.card := by
      rw [card_pos]
      by_contra h
      rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
      have : ∑ i ∈ X, q i ≤ 0 := sum_nonpos fun i hi ↦ not_lt.1 (h hi)
      linarith
    obtain ⟨k, hk⟩ : ∃ k, P.card = k + 1 := ⟨P.card - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    ring
  · -- level `> 1`: only the steps with `-1 < q x < 0` contribute
    have hA : thermostatBoxA (lev v q X) = 0 := if_neg fun h ↦ (h.2.trans_lt hgt1).false
    have hterm : ∀ x ∈ X, (boxD q x - thermostatBoxA (lev v q X)) * gw v q (X.erase x) =
        if -1 < q x ∧ q x < 0 then (-1) ^ P.card * (P.card.factorial : ℝ) *
          ((N.card - 1).factorial : ℝ) * indGt q X else 0 := by
      intro x hx
      rw [hA]
      by_cases hx' : -1 < q x ∧ q x < 0
      · have hD : boxD q x = 1 := if_pos ⟨hx'.1.le, hx'.2.le⟩
        have hxN : x ∈ N := mem_filter.2 ⟨hx, hx'.2⟩
        have hxP : x ∉ P := fun h ↦ ((mem_filter.1 h).2.trans hx'.2).false
        rw [if_pos hx', hD, (IH x hx).1 (by rw [lev_erase hx hXV]; linarith), filter_erase,
          filter_erase, ← hP, ← hN, erase_eq_of_notMem hxP, card_erase_of_mem hxN,
          indGt_erase hx'.1]
        ring
      · have hD : boxD q x = 0 := by
          refine if_neg fun h ↦ hx' ⟨lt_of_le_of_ne h.1 (hq1 x hx).symm,
            lt_of_le_of_ne h.2 (hq0 x hx)⟩
        rw [if_neg hx', hD]
        ring
    rw [sum_congr rfl hterm, ← sum_filter, sum_const, nsmul_eq_mul]
    by_cases hI : ∀ i ∈ X, -1 < q i
    · have hfN : (X.filter fun x ↦ -1 < q x ∧ q x < 0) = N := by
        refine filter_congr fun x hx ↦ ?_
        simp [hI x hx]
      have hNpos : 0 < N.card := by
        rw [card_pos]
        by_contra h
        rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
        have : 0 ≤ ∑ i ∈ X, q i := sum_nonneg fun i hi ↦ not_lt.1 (h hi)
        linarith
      obtain ⟨k, hk⟩ : ∃ k, N.card = k + 1 := ⟨N.card - 1, by omega⟩
      rw [hfN, hk, Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      ring
    · simp [indGt, hI]

/-! ### Genericity -/

/-- Membership in the dilated facet `Q_{v,R}`. -/
theorem mem_facetPoly_qCons {v : ι} {R : Finset ι} {q : ι → ℝ} :
    q ∈ facetPoly v (qCons v R) ↔ ∑ i, q i = 1 ∧ q v = 0 ∧
      ∀ i ∈ univ.erase v, if i ∈ R then 0 ≤ q i else -1 ≤ q i := by
  simp only [facetPoly, qCons, Set.mem_ofPred_eq, forall_mem_image]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun i _ ↦ ?_
  split_ifs <;> simp [neg_dotProduct, neg_le]

/-- Consequences of the genericity of `q`. -/
private theorem generic_facts {v : ι} {q : ι → ℝ} (hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b) :
    (∀ i ∈ univ.erase v, q i ≠ 0) ∧ (∀ i ∈ univ.erase v, q i ≠ -1) ∧
    ∀ X ⊆ univ.erase v, X.Nonempty → X ≠ univ.erase v → lev v q X ≠ 0 ∧ lev v q X ≠ 1 := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, fun X hXV hX hXne ↦ ?_⟩
  · have := hgen ⟨Pi.single i 1, 0⟩ (by
      unfold facetGen
      exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_image_of_mem _ hi))))
    simpa [single_one_dotProduct] using this
  · have := hgen ⟨Pi.single i 1, -1⟩ (by
      unfold facetGen
      exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hi))))
    simpa [single_one_dotProduct] using this
  · have hS : (univ.erase v \ X) ∈ (univ.erase v).powerset.filter
        fun S ↦ S.Nonempty ∧ S ≠ univ.erase v := by
      refine mem_filter.2 ⟨mem_powerset.2 sdiff_subset, ?_, fun h ↦ ?_⟩
      · rw [sdiff_nonempty]
        exact fun h ↦ hXne (subset_antisymm hXV h)
      · obtain ⟨x, hx⟩ := hX
        have := h.symm ▸ hXV hx
        exact (mem_sdiff.1 this).2 hx
    have h₀ := hgen ⟨indVec (univ.erase v \ X), 0⟩ (by
      unfold facetGen
      exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hS)))
    have h₁ := hgen ⟨indVec (univ.erase v \ X), 1⟩ (by
      unfold facetGen
      exact mem_union_right _ (mem_image_of_mem _ hS))
    simp only [indVec_dotProduct] at h₀ h₁
    exact ⟨h₀, h₁⟩

private theorem indicator_qCons_empty {v : ι} {q : ι → ℝ} (hq : ∑ i, q i = 1) (hqv : q v = 0)
    (h1 : ∀ i ∈ univ.erase v, q i ≠ -1) :
    (facetPoly v (qCons v ∅)).indicator 1 q = indGt q (univ.erase v) := by
  have : q ∈ facetPoly v (qCons v ∅) ↔ ∀ i ∈ univ.erase v, -1 < q i := by
    simp only [mem_facetPoly_qCons, hq, hqv, notMem_empty, ite_false, true_and]
    exact forall₂_congr fun i hi ↦ ⟨fun h ↦ lt_of_le_of_ne h (h1 i hi).symm, le_of_lt⟩
  by_cases h : ∀ i ∈ univ.erase v, -1 < q i
  · rw [Set.indicator_of_mem (this.2 h), indGt, if_pos h, Pi.one_apply]
  · rw [Set.indicator_of_notMem (mt this.1 h), indGt, if_neg h]

theorem thermostat {v : ι} (hn : 3 ≤ Fintype.card ι) {q : ι → ℝ} (hq : ∑ i, q i = 1)
    (hqv : q v = 0) (hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b) :
    ∑ l ∈ orderings (univ.erase v), ∑ M ∈ markings l,
        (-1 : ℝ) ^ M.card * (facetPoly v (boxConsL M l)).indicator 1 q =
      (facetPoly v (qCons v ∅)).indicator 1 q *
        psi (Fintype.card ι - 1) ((univ.erase v).filter fun i ↦ 0 < q i).card := by
  obtain ⟨h0, h1, hlev⟩ := generic_facts hgen
  have hsum : ∑ i ∈ univ.erase v, q i = 1 := by rw [sum_erase _ hqv, hq]
  have hcardV : (univ.erase v).card = Fintype.card ι - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ]
  have hVne : (univ.erase v).Nonempty := by
    rw [← card_pos]
    omega
  set P := (univ.erase v).filter fun i ↦ 0 < q i with hP
  set N := (univ.erase v).filter fun i ↦ q i < 0 with hN
  have hPN : N.card = Fintype.card ι - 1 - P.card := by
    have hNeq : N = (univ.erase v).filter fun i ↦ ¬ 0 < q i :=
      filter_congr fun i hi ↦ ⟨fun h ↦ not_lt.2 h.le,
        fun h ↦ lt_of_le_of_ne (not_lt.1 h) (h0 i hi)⟩
    have := card_filter_add_card_filter_not (s := univ.erase v) (fun i ↦ 0 < q i)
    rw [hNeq, ← hcardV, ← this, ← hP]
    omega
  have hgw : ∀ h ∈ univ.erase v, ∑ t ∈ orderings ((univ.erase v).erase h), ∑ M ∈ markings (h :: t),
      (-1 : ℝ) ^ M.card * (facetPoly v (boxConsL M (h :: t))).indicator 1 q =
      if 0 < q h then (-1) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) *
        (N.card.factorial : ℝ) * indGt q (univ.erase v) else 0 := by
    intro h hh
    have hlevh : lev v q ((univ.erase v).erase h) = q h := by
      rw [lev, sdiff_erase_self hh, sum_singleton]
    have hne : (univ.erase v).erase h ≠ univ.erase v := fun H ↦
      notMem_erase h (univ.erase v) (by rw [H]; exact hh)
    have key := gw_eq hsum h0 h1 hlev _ (erase_subset _ _) hne
    have hsw : ∑ t ∈ orderings ((univ.erase v).erase h), ∑ M ∈ markings (h :: t),
        (-1 : ℝ) ^ M.card * (facetPoly v (boxConsL M (h :: t))).indicator 1 q =
        gw v q ((univ.erase v).erase h) := by
      rw [gw, hlevh]
      refine sum_congr rfl fun t ht ↦ ?_
      obtain ⟨hnd, hto⟩ := mem_orderings.1 ht
      refine sum_markings_eq_walkW hq hqv (List.nodup_cons.2 ⟨fun H ↦ ?_, hnd⟩)
      have := List.mem_toFinset.2 H
      rw [hto] at this
      exact notMem_erase h _ this
    rw [hsw]
    by_cases hpos : 0 < q h
    · have hhP : h ∈ P := mem_filter.2 ⟨hh, hpos⟩
      have hhN : h ∉ N := fun H ↦ ((mem_filter.1 H).2.trans hpos).false
      rw [if_pos hpos, key.1 (hlevh ▸ hpos), filter_erase _ h (univ.erase v),
        filter_erase _ h (univ.erase v), ← hP, ← hN,
        erase_eq_of_notMem hhN, card_erase_of_mem hhP, indGt_erase (by linarith)]
    · have hneg : q h < 0 := lt_of_le_of_ne (not_lt.1 hpos) (h0 h hh)
      have hne' : ((univ.erase v).erase h).Nonempty := by
        rw [← card_pos, card_erase_of_mem hh]
        omega
      rw [if_neg hpos, key.2 (hlevh ▸ hneg) hne']
  rw [sum_orderings_eq hVne, sum_congr rfl hgw, ← sum_filter, ← hP, sum_const, nsmul_eq_mul,
    indicator_qCons_empty hq hqv h1, psi, ← hPN]
  have hPpos : 0 < P.card := by
    rw [card_pos]
    by_contra h
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    have : ∑ i ∈ univ.erase v, q i ≤ 0 := sum_nonpos fun i hi ↦ not_lt.1 (h hi)
    linarith
  obtain ⟨k, hk⟩ : ∃ k, P.card = k + 1 := ⟨P.card - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Counting the nonempty subsets of a finite set according to their cardinality. -/
theorem sum_powerset_nonempty_apply_card (c : ℕ → ℝ) (S : Finset ι) {m : ℕ} (hm : S.card ≤ m) :
    ∑ R ∈ S.powerset.filter (·.Nonempty), c R.card =
      ∑ r ∈ Icc 1 m, c r * (S.card.choose r : ℝ) := by
  set g : ℕ → ℝ := fun k ↦ if k = 0 then 0 else c k with hg
  have h₁ : ∀ R ∈ S.powerset, (if R.Nonempty then c R.card else 0) = g R.card := by
    intro R _
    simp only [hg, card_eq_zero, ← not_nonempty_iff_eq_empty]
    split_ifs <;> simp_all
  rw [sum_filter, sum_congr rfl h₁, sum_powerset_apply_card]
  calc ∑ k ∈ range (S.card + 1), S.card.choose k • g k
      = ∑ k ∈ range (m + 1), S.card.choose k • g k := by
        refine sum_subset (range_subset_range.2 (by omega)) fun k _ hk ↦ ?_
        rw [mem_range, not_lt] at hk
        rw [Nat.choose_eq_zero_of_lt (by omega), zero_smul]
    _ = ∑ k ∈ Icc 1 m, S.card.choose k • g k := by
        refine (sum_subset (fun k hk ↦ ?_) fun k hk hk' ↦ ?_).symm
        · rw [mem_Icc] at hk
          rw [mem_range]
          omega
        · have : k = 0 := by
            rw [mem_range] at hk
            rw [mem_Icc] at hk'
            omega
          simp [this, hg]
    _ = ∑ r ∈ Icc 1 m, c r * (S.card.choose r : ℝ) := by
        refine sum_congr rfl fun k hk ↦ ?_
        have : k ≠ 0 := by
          rw [mem_Icc] at hk
          omega
        simp [hg, this, nsmul_eq_mul, mul_comm]

theorem qcount {v : ι} (c : ℕ → ℝ) {q : ι → ℝ} (hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b) :
    ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
        c R.card * (facetPoly v (qCons v R)).indicator 1 q =
      (facetPoly v (qCons v ∅)).indicator 1 q *
        ∑ r ∈ Icc 1 (Fintype.card ι - 1),
          c r * (((univ.erase v).filter fun i ↦ 0 < q i).card.choose r : ℝ) := by
  obtain ⟨h0, -, -⟩ := generic_facts hgen
  set Pos := (univ.erase v).filter fun i ↦ 0 < q i with hPos
  have hmem : ∀ R ⊆ univ.erase v, (facetPoly v (qCons v R)).indicator (1 : (ι → ℝ) → ℝ) q =
      (facetPoly v (qCons v ∅)).indicator 1 q * if R ⊆ Pos then 1 else 0 := by
    intro R hR
    have key : q ∈ facetPoly v (qCons v R) ↔ q ∈ facetPoly v (qCons v ∅) ∧ R ⊆ Pos := by
      simp only [mem_facetPoly_qCons, notMem_empty, ite_false]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨h1, h2, fun i hi ↦ ?_⟩, fun i hiR ↦ ?_⟩
        · have := h3 i hi
          split_ifs at this
          · linarith
          · exact this
        · have := h3 i (hR hiR)
          rw [if_pos hiR] at this
          exact mem_filter.2 ⟨hR hiR, lt_of_le_of_ne this (h0 i (hR hiR)).symm⟩
      · rintro ⟨⟨h1, h2, h3⟩, hRP⟩
        refine ⟨h1, h2, fun i hi ↦ ?_⟩
        split_ifs with hiR
        · exact (mem_filter.1 (hRP hiR)).2.le
        · exact h3 i hi
    by_cases ha : q ∈ facetPoly v (qCons v ∅) <;> by_cases hb : R ⊆ Pos <;>
      simp [key, ha, hb]
  have hsub : Pos ⊆ univ.erase v := filter_subset _ _
  have hcard : Pos.card ≤ Fintype.card ι - 1 := by
    have := card_le_card hsub
    rwa [card_erase_of_mem (mem_univ _), card_univ] at this
  rw [← sum_powerset_nonempty_apply_card c Pos hcard, mul_sum]
  calc _ = ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
          if R ⊆ Pos then (facetPoly v (qCons v ∅)).indicator 1 q * c R.card else 0 := by
        refine sum_congr rfl fun R hR ↦ ?_
        simp only [hmem R (mem_powerset.1 (mem_filter.1 hR).1)]
        split_ifs <;> ring
    _ = _ := by
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ ↦ rfl
        ext R
        simp only [mem_filter, mem_powerset]
        exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.trans hsub, h.2⟩, h.1⟩⟩

/-! ### Nonconstancy of the constraints -/

omit [DecidableEq ι] in
private theorem exists_ne_ne (hn : 3 ≤ Fintype.card ι) (i v : ι) : ∃ j, j ≠ i ∧ j ≠ v := by
  classical
  obtain ⟨j, -, hj⟩ := exists_mem_notMem_of_card_lt_card (s := {i, v}) (t := univ) (by
    rw [card_univ]
    exact card_le_two.trans_lt (by omega))
  simp only [mem_insert, mem_singleton, not_or] at hj
  exact ⟨j, hj.1, hj.2⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem nonconst_neg {v : ι} {a : ι → ℝ} (h : ∃ i j, i ≠ v ∧ j ≠ v ∧ a i ≠ a j) :
    ∃ i j, i ≠ v ∧ j ≠ v ∧ (-a) i ≠ (-a) j := by
  obtain ⟨i, j, hi, hj, h⟩ := h
  exact ⟨i, j, hi, hj, by simpa using h⟩

private theorem nonconst_single {v x : ι} (hx : x ≠ v) (hn : 3 ≤ Fintype.card ι) :
    ∃ i j, i ≠ v ∧ j ≠ v ∧ (Pi.single x 1 : ι → ℝ) i ≠ (Pi.single x 1 : ι → ℝ) j := by
  obtain ⟨j, hjx, hjv⟩ := exists_ne_ne hn x v
  exact ⟨x, j, hx, hjv, by simp [Pi.single_eq_of_ne hjx]⟩

omit [Fintype ι] in
private theorem nonconst_indVec {v i j : ι} {S : Finset ι} (hi : i ∈ S) (hj : j ∉ S) (hiv : i ≠ v)
    (hjv : j ≠ v) : ∃ i j, i ≠ v ∧ j ≠ v ∧ indVec S i ≠ indVec S j :=
  ⟨i, j, hiv, hjv, by simp [indVec, hi, hj]⟩

theorem nonconst_facetGen {v : ι} {g : Constraint ι} (hg : g ∈ facetGen v)
    (hn : 3 ≤ Fintype.card ι) : ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j := by
  unfold facetGen at hg
  simp only [mem_union, mem_image, mem_filter, mem_powerset] at hg
  rcases hg with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨S, ⟨hSV, hSne, hSV'⟩, rfl⟩) |
      ⟨S, ⟨hSV, hSne, hSV'⟩, rfl⟩
  · exact nonconst_single (mem_erase.1 hi).1 hn
  · exact nonconst_single (mem_erase.1 hi).1 hn
  all_goals
    obtain ⟨i, hi⟩ := hSne
    obtain ⟨j, hj, hjS⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hSV hSV')
    exact nonconst_indVec hi hjS (mem_erase.1 (hSV hi)).1 (mem_erase.1 hj).1

theorem nonconst_qCons {v : ι} {R : Finset ι} {g : Constraint ι} (hg : g ∈ qCons v R)
    (hn : 3 ≤ Fintype.card ι) : ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j := by
  unfold qCons at hg
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hg
  have := nonconst_neg (nonconst_single (mem_erase.1 hi).1 hn)
  by_cases hiR : i ∈ R <;> simp only [hiR, ite_true, ite_false] <;> exact this

private theorem nonconst_boxCons {v : ι} (hn : 3 ≤ Fintype.card ι) (M : Finset ι)
    {g : Constraint ι} : ∀ (pre : Finset ι) (t : List ι), pre.Nonempty → pre ⊆ univ.erase v →
    t.Nodup → (∀ x ∈ t, x ∈ univ.erase v ∧ x ∉ pre) → g ∈ boxCons M pre t →
    ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j
  | _, [], _, _, _, _, hg => by simp [boxCons] at hg
  | pre, x :: t, hne, hpre, hnd, ht, hg => by
    rw [boxCons, mem_union] at hg
    obtain ⟨hxV, hxpre⟩ := ht x List.mem_cons_self
    have hxv := (mem_erase.1 hxV).1
    rcases hg with hg | hg
    · split_ifs at hg
      · obtain ⟨i, hi⟩ := hne
        have h := nonconst_indVec hi hxpre (mem_erase.1 (hpre hi)).1 hxv
        rw [mem_insert, mem_singleton] at hg
        rcases hg with rfl | rfl
        · exact nonconst_neg h
        · exact h
      · rw [mem_insert, mem_singleton] at hg
        rcases hg with rfl | rfl
        · exact nonconst_neg (nonconst_single hxv hn)
        · exact nonconst_single hxv hn
    · rw [List.nodup_cons] at hnd
      refine nonconst_boxCons hn M (insert x pre) t (insert_nonempty _ _)
        (insert_subset hxV hpre) hnd.2 (fun y hy ↦ ?_) hg
      obtain ⟨hyV, hypre⟩ := ht y (List.mem_cons_of_mem _ hy)
      refine ⟨hyV, ?_⟩
      rw [mem_insert, not_or]
      exact ⟨fun h ↦ hnd.1 (h ▸ hy), hypre⟩

theorem nonconst_boxConsL {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (M : Finset ι) {g : Constraint ι} (hg : g ∈ boxConsL M l) (hn : 3 ≤ Fintype.card ι) :
    ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j := by
  obtain ⟨hnd, hl⟩ := mem_orderings.1 hl
  cases l with
  | nil => simp [boxConsL] at hg
  | cons h t =>
    rw [List.nodup_cons] at hnd
    have hmem : ∀ y ∈ h :: t, y ∈ univ.erase v := fun y hy ↦ hl ▸ List.mem_toFinset.2 hy
    refine nonconst_boxCons hn M {h} t (singleton_nonempty _)
      (singleton_subset_iff.2 (hmem h List.mem_cons_self)) hnd.2 (fun y hy ↦ ?_) hg
    refine ⟨hmem y (List.mem_cons_of_mem _ hy), ?_⟩
    rw [mem_singleton]
    rintro rfl
    exact hnd.1 hy

end

end AuthorReal

-- Source module: Solutions/AuthorBox.lean


/-!
# The parallelepipeds `B_{π,M}`

For an ordering `l` of `ι \ {v}` and a marking `M`, the polytope `facetPoly v (boxConsL M l)` is
the preimage of a box under an affine isomorphism (the defining system is triangular). Hence it is
a nonempty bounded parallelepiped, and its support function is affine plus a sum of ReLUs of linear
forms, i.e. it lies in `reluNet ι 1`.
-/

open Finset

namespace AuthorReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Parallelepipeds given by an invertible linear system -/

/-- The parallelepiped `{p | lo y ≤ ⟪a y, p⟫ ≤ hi y for all y}`. -/
def slabPoly (a : ι → ι → ℝ) (lo hi : ι → ℝ) : Set (ι → ℝ) :=
  {p | ∀ y, a y ⬝ᵥ p ∈ Set.Icc (lo y) (hi y)}

omit [DecidableEq ι] in
theorem mulVecLin_of_apply (a : ι → ι → ℝ) (p : ι → ℝ) (y : ι) :
    (Matrix.of a).mulVecLin p y = a y ⬝ᵥ p := rfl

omit [DecidableEq ι] in
theorem slabPoly_eq_preimage (a : ι → ι → ℝ) (lo hi : ι → ℝ) :
    slabPoly a lo hi = (Matrix.of a).mulVecLin ⁻¹' Set.Icc lo hi := by
  ext p
  simp only [slabPoly, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_preimage, Pi.le_def,
    mulVecLin_of_apply, ← forall_and]

/-- `max (lo * w) (hi * w)` written as a linear term plus a ReLU, bounding `z * w` for
`z ∈ [lo, hi]`. -/
theorem mul_le_of_mem_Icc {lo hi z : ℝ} (hz : z ∈ Set.Icc lo hi) (w : ℝ) :
    z * w ≤ lo * w + (hi - lo) * relu w := by
  rcases le_total 0 w with hw | hw
  · have : relu w = w := max_eq_left hw
    rw [this]
    nlinarith [hz.2]
  · have : relu w = 0 := max_eq_right hw
    rw [this]
    nlinarith [hz.1]

theorem mul_ite_eq {lo hi : ℝ} (w : ℝ) :
    (if 0 ≤ w then hi else lo) * w = lo * w + (hi - lo) * relu w := by
  split_ifs with hw
  · rw [show relu w = w from max_eq_left hw]; ring
  · rw [show relu w = 0 from max_eq_right (le_of_not_ge hw)]; ring

section slab

variable {a : ι → ι → ℝ} (ha : Function.Injective (Matrix.of a).mulVecLin) {lo hi : ι → ℝ}

/-- The linear automorphism `p ↦ (⟪a y, p⟫)_y`. -/
def slabEquiv : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofInjectiveEndo _ ha

omit [DecidableEq ι] in
include ha in
theorem slabPoly_eq_image :
    slabPoly a lo hi = (slabEquiv ha).symm '' Set.Icc lo hi := by
  rw [LinearEquiv.image_symm_eq_preimage, slabPoly_eq_preimage]
  rfl

omit [DecidableEq ι] in
include ha in
/-- A parallelepiped with `lo ≤ hi` is nonempty. -/
theorem slabPoly_nonempty (hlh : lo ≤ hi) : (slabPoly a lo hi).Nonempty := by
  rw [slabPoly_eq_image ha]
  exact ⟨_, lo, Set.left_mem_Icc.mpr hlh, rfl⟩

omit [DecidableEq ι] in
include ha in
/-- A parallelepiped is bounded. -/
theorem isBounded_slabPoly : Bornology.IsBounded (slabPoly a lo hi) := by
  rw [slabPoly_eq_image ha]
  exact (isCompact_Icc.image
    (LinearMap.continuous_of_finiteDimensional (slabEquiv ha).symm.toLinearMap)).isBounded

theorem dotProduct_symm_eq (z x : ι → ℝ) :
    (slabEquiv ha).symm z ⬝ᵥ x = ∑ y, z y * ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  simp only [map_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have : Pi.single y (z y) = z y • Pi.single y (1 : ℝ) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [this, map_smul, smul_dotProduct, smul_eq_mul]

/-- The support function of a parallelepiped. -/
theorem supportFun_slabPoly (hlh : lo ≤ hi) (x : ι → ℝ) :
    supportFun (slabPoly a lo hi) x = ∑ y, (lo y * ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x) +
      (hi y - lo y) * relu ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x)) := by
  set w : ι → ℝ := fun y ↦ (slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x
  refine le_antisymm (supportFun_le (slabPoly_nonempty ha hlh) fun p hp ↦ ?_) ?_
  · rw [slabPoly_eq_image ha] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    rw [dotProduct_symm_eq]
    exact Finset.sum_le_sum fun y _ ↦ mul_le_of_mem_Icc ⟨hz.1 y, hz.2 y⟩ (w y)
  · let z : ι → ℝ := fun y ↦ if 0 ≤ w y then hi y else lo y
    have hz : z ∈ Set.Icc lo hi := by
      refine ⟨fun y ↦ ?_, fun y ↦ ?_⟩ <;> simp only [z] <;> split_ifs <;> simp [hlh y]
    have hp : (slabEquiv ha).symm z ∈ slabPoly a lo hi := by
      rw [slabPoly_eq_image ha]; exact ⟨z, hz, rfl⟩
    have := le_supportFun (isBounded_slabPoly ha) hp x
    rw [dotProduct_symm_eq] at this
    exact le_of_eq_of_le (Finset.sum_congr rfl fun y _ ↦ (mul_ite_eq (w y)).symm) this

omit [DecidableEq ι] in
include ha in
/-- The support function of a parallelepiped lies in `reluNet ι 1`. -/
theorem supportFun_slabPoly_mem (hlh : lo ≤ hi) : supportFun (slabPoly a lo hi) ∈ reluNet ι 1 := by
  classical
  have : supportFun (slabPoly a lo hi) = ∑ y, ((lo y) • (fun x ↦
      (slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x) + (hi y - lo y) • (fun x ↦
      relu ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x + 0))) := by
    funext x
    simp [supportFun_slabPoly ha hlh, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun y _ ↦ add_mem (Submodule.smul_mem _ _ (reluNet.linear_mem 1 _))
    (Submodule.smul_mem _ _ (reluNet.relu_affine_mem _ _))

end slab

/-! ### The triangular system of `boxCons` -/

/-- The normal vector of the functional constrained at position `x` of the list `l` by
`boxCons M pre l`: `indVec` of the coordinates visited before `x` if `x ∈ M`, else `e_x`. -/
def boxCoef (M : Finset ι) : Finset ι → List ι → ι → ι → ℝ
  | _, [], _ => 0
  | pre, y :: l, x =>
    if x = y then (if y ∈ M then indVec pre else Pi.single y 1) else boxCoef M (insert y pre) l x

/-- The lower bound of the functional at position `x`. -/
def boxLo (M : Finset ι) (x : ι) : ℝ := if x ∈ M then 0 else -1

/-- The upper bound of the functional at position `x`. -/
def boxHi (M : Finset ι) (x : ι) : ℝ := if x ∈ M then 1 else 0

/-- The constraints `boxCons M pre l` as a triangular system of interval constraints. -/
theorem forall_boxCons_iff {M pre : Finset ι} {l : List ι} (hl : l.Nodup) (p : ι → ℝ) :
    (∀ c ∈ boxCons M pre l, c.a ⬝ᵥ p ≤ c.b) ↔
      ∀ x ∈ l, boxCoef M pre l x ⬝ᵥ p ∈ Set.Icc (boxLo M x) (boxHi M x) := by
  induction l generalizing pre with
  | nil => simp [boxCons]
  | cons y l ih =>
    obtain ⟨hy, hl⟩ := List.nodup_cons.mp hl
    have hrest : ∀ x ∈ l, boxCoef M pre (y :: l) x = boxCoef M (insert y pre) l x := by
      intro x hx
      have : x ≠ y := fun h ↦ hy (h ▸ hx)
      simp [boxCoef, this]
    rw [List.forall_mem_cons, boxCons, Finset.forall_mem_union, ih hl]
    refine and_congr ?_ ⟨fun h x hx ↦ hrest x hx ▸ h x hx, fun h x hx ↦ hrest x hx ▸ h x hx⟩
    by_cases hyM : y ∈ M <;>
      simp [hyM, boxCoef, boxLo, boxHi, neg_dotProduct, neg_le, and_comm]

/-- Triangularity of `boxCoef`: the homogeneous system has only the trivial solution. -/
theorem boxCoef_eq_zero {M pre : Finset ι} {l : List ι} (hl : l.Nodup)
    (hpre : Disjoint pre l.toFinset) {p : ι → ℝ} (hp : ∀ x ∈ l, boxCoef M pre l x ⬝ᵥ p = 0)
    (hsum : ∑ i ∈ pre ∪ l.toFinset, p i = 0) : (∀ x ∈ l, p x = 0) ∧ ∑ i ∈ pre, p i = 0 := by
  induction l generalizing pre with
  | nil => simpa using hsum
  | cons y l ih =>
    obtain ⟨hy, hl⟩ := List.nodup_cons.mp hl
    have hypre : y ∉ pre := fun h ↦ Finset.disjoint_left.mp hpre h (by simp)
    have hrest : ∀ x ∈ l, boxCoef M pre (y :: l) x = boxCoef M (insert y pre) l x := by
      intro x hx
      have : x ≠ y := fun h ↦ hy (h ▸ hx)
      simp [boxCoef, this]
    have hpre' : Disjoint (insert y pre) l.toFinset := by
      rw [Finset.disjoint_insert_left]
      exact ⟨by simpa using hy, (Finset.disjoint_of_subset_right (by simp) hpre)⟩
    obtain ⟨hl0, hs⟩ := ih hl hpre' (fun x hx ↦ hrest x hx ▸ hp x (by simp [hx]))
      (by rw [← hsum, List.toFinset_cons, Finset.insert_union, Finset.union_insert])
    rw [Finset.sum_insert hypre] at hs
    have hy0 := hp y (by simp)
    by_cases hyM : y ∈ M
    · simp only [boxCoef, ite_true, hyM, indVec_dotProduct] at hy0
      refine ⟨List.forall_mem_cons.mpr ⟨by linarith, hl0⟩, hy0⟩
    · simp only [boxCoef, ite_true, hyM, ite_false, single_one_dotProduct] at hy0
      refine ⟨List.forall_mem_cons.mpr ⟨hy0, hl0⟩, by linarith⟩

/-- The normal vectors of the full triangular system of `facetPoly v (boxConsL M (h :: t))`:
`e_v`, the all-ones vector at `h`, and `boxCoef` along `t`. -/
def boxA (v h : ι) (M : Finset ι) (t : List ι) (y : ι) : ι → ℝ :=
  if y = v then Pi.single v 1 else if y = h then 1 else boxCoef M {h} t y

/-- The lower bounds of the full triangular system. -/
def boxLoA (v h : ι) (M : Finset ι) (y : ι) : ℝ :=
  if y = v then 0 else if y = h then 1 else boxLo M y

/-- The upper bounds of the full triangular system. -/
def boxHiA (v h : ι) (M : Finset ι) (y : ι) : ℝ :=
  if y = v then 0 else if y = h then 1 else boxHi M y

omit [Fintype ι] in
theorem boxLoA_le_boxHiA (v h : ι) (M : Finset ι) : boxLoA v h M ≤ boxHiA v h M := by
  intro y
  simp only [boxLoA, boxHiA, boxLo, boxHi]
  split_ifs <;> norm_num

section full

variable {v h : ι} {t : List ι} (hnd : (h :: t).Nodup) (hX : insert h t.toFinset = univ.erase v)
  (M : Finset ι)

include hX

theorem ne_of_insert_eq_erase : h ≠ v := by
  have : h ∈ insert h t.toFinset := Finset.mem_insert_self _ _
  rw [hX] at this
  exact (Finset.mem_erase.mp this).1

theorem mem_tail_of_ne {i : ι} (hiv : i ≠ v) (hih : i ≠ h) : i ∈ t := by
  have : i ∈ insert h t.toFinset := hX ▸ Finset.mem_erase.mpr ⟨hiv, Finset.mem_univ i⟩
  simpa [hih] using this

include hnd

theorem ne_of_mem_tail {x : ι} (hx : x ∈ t) : x ≠ v ∧ x ≠ h := by
  refine ⟨fun hxv ↦ ?_, fun hxh ↦ (List.nodup_cons.mp hnd).1 (hxh ▸ hx)⟩
  have : x ∈ insert h t.toFinset := by simp [hx]
  rw [hX, hxv] at this
  simp at this

/-- The box written as a parallelepiped. -/
theorem facetPoly_boxCons_eq :
    facetPoly v (boxCons M {h} t) = slabPoly (boxA v h M t) (boxLoA v h M) (boxHiA v h M) := by
  have hhv : h ≠ v := ne_of_insert_eq_erase hX
  ext p
  simp only [facetPoly, slabPoly, Set.mem_ofPred_eq,
    forall_boxCons_iff (List.nodup_cons.mp hnd).2]
  constructor
  · rintro ⟨hs, hv0, ht⟩ y
    by_cases hyv : y = v
    · subst hyv; simp [boxA, boxLoA, boxHiA, hv0]
    by_cases hyh : y = h
    · subst hyh; simp [boxA, boxLoA, boxHiA, hyv, one_dotProduct, hs]
    simpa [boxA, boxLoA, boxHiA, hyv, hyh] using ht y (mem_tail_of_ne hX hyv hyh)
  · intro H
    refine ⟨by simpa [boxA, boxLoA, boxHiA, hhv, one_dotProduct] using H h,
      by simpa [boxA, boxLoA, boxHiA] using H v, fun x hx ↦ ?_⟩
    obtain ⟨hxv, hxh⟩ := ne_of_mem_tail hnd hX hx
    simpa [boxA, boxLoA, boxHiA, hxv, hxh] using H x

/-- The full triangular system is invertible. -/
theorem injective_boxA : Function.Injective (Matrix.of (boxA v h M t)).mulVecLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  have hy : ∀ y, boxA v h M t y ⬝ᵥ p = 0 := fun y ↦ by
    simpa [mulVecLin_of_apply] using congrFun hp y
  have hhv : h ≠ v := ne_of_insert_eq_erase hX
  have hv0 : p v = 0 := by simpa [boxA] using hy v
  have hs : ∑ i, p i = 0 := by simpa [boxA, hhv, one_dotProduct] using hy h
  have hdis : Disjoint {h} t.toFinset := by
    simpa using (List.nodup_cons.mp hnd).1
  obtain ⟨ht0, hh0⟩ := boxCoef_eq_zero (M := M) (List.nodup_cons.mp hnd).2 hdis
    (p := p) (fun x hx ↦ by
      obtain ⟨hxv, hxh⟩ := ne_of_mem_tail hnd hX hx
      simpa [boxA, hxv, hxh] using hy x)
    (by
      rw [← Finset.insert_eq, hX]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at hs
      linarith)
  funext i
  by_cases hiv : i = v
  · subst hiv; exact hv0
  by_cases hih : i = h
  · subst hih; simpa using hh0
  exact ht0 i (mem_tail_of_ne hX hiv hih)

end full

/-- An ordering of `ι \ {v}` is nonempty if `ι` has at least two elements. -/
theorem exists_cons_of_mem_orderings {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (hn : 2 ≤ Fintype.card ι) :
    ∃ h t, l = h :: t ∧ (h :: t).Nodup ∧ insert h t.toFinset = univ.erase v := by
  obtain ⟨hnd, hX⟩ := mem_orderings.mp hl
  match l, hnd, hX with
  | [], _, hX =>
    have := congrArg Finset.card hX
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at this
    simp at this
    omega
  | h :: t, hnd, hX => exact ⟨h, t, rfl, hnd, by simpa using hX⟩

/-- The box as a parallelepiped `slabPoly` with an injective system. -/
theorem exists_box_eq_slabPoly {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (M : Finset ι) (hn : 2 ≤ Fintype.card ι) :
    ∃ (a : ι → ι → ℝ) (lo hi : ι → ℝ), Function.Injective (Matrix.of a).mulVecLin ∧ lo ≤ hi ∧
      facetPoly v (boxConsL M l) = slabPoly a lo hi := by
  obtain ⟨h, t, rfl, hnd, hX⟩ := exists_cons_of_mem_orderings hl hn
  exact ⟨_, _, _, injective_boxA hnd hX M, boxLoA_le_boxHiA v h M,
    facetPoly_boxCons_eq hnd hX M⟩

/-- The parallelepiped `B_{π,M}` is nonempty. -/
theorem box_nonempty {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v)) (M : Finset ι)
    (hn : 2 ≤ Fintype.card ι) : (facetPoly v (boxConsL M l)).Nonempty := by
  obtain ⟨a, lo, hi, ha, hlh, heq⟩ := exists_box_eq_slabPoly hl M hn
  exact heq ▸ slabPoly_nonempty ha hlh

/-- The parallelepiped `B_{π,M}` is bounded. -/
theorem isBounded_box {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v)) (M : Finset ι)
    (hn : 2 ≤ Fintype.card ι) : Bornology.IsBounded (facetPoly v (boxConsL M l)) := by
  obtain ⟨a, lo, hi, ha, -, heq⟩ := exists_box_eq_slabPoly hl M hn
  exact heq ▸ isBounded_slabPoly ha

/-- The support function of `B_{π,M}` is computed by a one-hidden-layer ReLU network. -/
theorem supportFun_box_mem {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (M : Finset ι) (hn : 2 ≤ Fintype.card ι) :
    supportFun (facetPoly v (boxConsL M l)) ∈ reluNet ι 1 := by
  obtain ⟨a, lo, hi, ha, hlh, heq⟩ := exists_box_eq_slabPoly hl M hn
  exact heq ▸ supportFun_slabPoly_mem ha hlh

end

end AuthorReal

-- Source module: Solutions/AuthorMain.lean


/-!
# Two hidden ReLU layers compute the maximum

We assemble the proof that `max (x₁, …, xₙ)` lies in `reluNet (Fin n) 2`, i.e. can be computed by a
ReLU network with two hidden layers.

The proof is by induction on `n`. For `n ≥ 3`, the thermostat lemma, the count of the dilated
facets and coning show that for every vertex `v` the signed sum of the paramids
`pyr_{e_v}(B_{v,π,M})` agrees with a combination of the cones `pyr_{e_v}(Q_{v,R})` modulo maxima of
`n - 1` linear forms. Summing over `v` and using the subdivision lemma, the paramids sum to
`(-1)^n n! · max` modulo maxima of `n - 1` linear forms, which are handled by induction.

## Main results

* `max_mem_reluNet`: `max (x₁, …, xₙ)` lies in `reluNet (Fin n) 2`.
* `exists_twoLayerNet_eq_max`: there is an explicit ReLU network with two hidden layers computing
  `max (x₁, …, xₙ)`.
-/

open Finset

namespace AuthorReal

noncomputable section

/-- Coefficients expressing `psi m` in the basis `s ↦ (s choose r)`, defined by the triangular
recursion `a_r = psi m r - ∑_{k < r} a_k (r choose k)` (with `a_0 = 0`). -/
def coeffs (m : ℕ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else psi m r - ∑ k : Fin r, coeffs m k * (r.choose k : ℝ)
decreasing_by exact k.isLt

theorem sum_range_coeffs_mul_choose (m : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    ∑ r ∈ range (s + 1), coeffs m r * (s.choose r : ℝ) = psi m s := by
  rw [sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one]
  conv_rhs => rw [show psi m s = coeffs m s + ∑ k : Fin s, coeffs m k * (s.choose k : ℝ) by
    rw [coeffs, if_neg (by omega)]; ring]
  rw [add_comm, Fin.sum_univ_eq_sum_range (fun k ↦ coeffs m k * (s.choose k : ℝ))]

theorem sum_coeffs_mul_choose (m : ℕ) {s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∑ r ∈ Icc 1 m, coeffs m r * (s.choose r : ℝ) = psi m s := by
  rw [← sum_range_coeffs_mul_choose m hs]
  have hsub : Icc 1 s ⊆ Icc 1 m := Icc_subset_Icc le_rfl hsm
  rw [← sum_subset hsub, ← sum_subset (s₁ := Icc 1 s) (s₂ := range (s + 1))]
  · intro r hr
    simp only [mem_Icc, mem_range] at hr ⊢
    omega
  · intro r hr hr'
    simp only [mem_Icc, mem_range, not_and_or, not_le] at hr hr'
    have : r = 0 := by omega
    subst this
    simp [coeffs]
  · intro r hr hr'
    simp only [mem_Icc, not_and_or, not_le] at hr hr'
    have : s < r := by omega
    simp [Nat.choose_eq_zero_of_lt this]

theorem psi_self_ne_zero (m : ℕ) : psi m m ≠ 0 := by
  simp [psi, Nat.factorial_ne_zero]

theorem sum_filter_nonempty_coeffs {ι : Type*} {X : Finset ι} {m : ℕ} (hX : X.card = m)
    (hm : 1 ≤ m) :
    ∑ R ∈ X.powerset.filter (·.Nonempty), coeffs m R.card = psi m m := by
  rw [sum_filter_of_ne fun R _ h ↦ ?_]
  · rw [sum_powerset_apply_card, hX, ← sum_range_coeffs_mul_choose m hm]
    simp [nsmul_eq_mul, mul_comm]
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    simp [coeffs] at h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reindexing pairs `(v, R)` with `∅ ≠ R ⊆ ι \ {v}`. -/
theorem sum_sum_powerset_erase_comm {β : Type*} [AddCommMonoid β] (f : ι → Finset ι → β) :
    ∑ v, ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty), f v R =
      ∑ R ∈ univ.powerset.filter (fun R : Finset ι ↦ R.Nonempty ∧ R ≠ univ), ∑ v ∈ Rᶜ, f v R := by
  refine sum_comm' fun v R ↦ ?_
  simp only [mem_filter, mem_powerset, mem_univ, true_and, mem_compl]
  constructor
  · rintro ⟨hRv, hR⟩
    have hv : v ∉ R := fun h ↦ by simpa using hRv h
    exact ⟨hv, subset_univ _, hR, fun h ↦ hv (h ▸ mem_univ v)⟩
  · rintro ⟨hv, -, hR, -⟩
    exact ⟨fun x hx ↦ mem_erase.2 ⟨fun h ↦ hv (h ▸ hx), mem_univ _⟩, hR⟩

/-- The per-vertex identity: the signed paramids with apex `e_v` agree with a combination of the
coned dilated facets modulo maxima of `card ι - 1` linear forms. -/
theorem vertex_identity (hn : 3 ≤ Fintype.card ι) (v : ι) :
    (∑ lM ∈ (orderings (univ.erase v)).sigma markings,
        (-1 : ℝ) ^ lM.2.card • supportFun (pyr v (boxConsL lM.2 lM.1))) -
      ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
        coeffs (Fintype.card ι - 1) R.card • supportFun (pyr v (qCons v R)) ∈
      maxSpan ι (Fintype.card ι - 1) := by
  set m := Fintype.card ι - 1
  set S₁ := (orderings (univ.erase v)).sigma markings
  set S₂ := (univ.erase v).powerset.filter (·.Nonempty)
  set Gf := facetGen v ∪ S₁.biUnion (fun lM ↦ boxConsL lM.2 lM.1) ∪ S₂.biUnion (qCons v)
  set coef : (Σ _ : List ι, Finset ι) ⊕ Finset ι → ℝ :=
    Sum.elim (fun lM ↦ (-1 : ℝ) ^ lM.2.card) (fun R ↦ -coeffs m R.card)
  set csf : (Σ _ : List ι, Finset ι) ⊕ Finset ι → Finset (Constraint ι) :=
    Sum.elim (fun lM ↦ boxConsL lM.2 lM.1) (fun R ↦ qCons v R)
  have hS₁ : ∀ lM ∈ S₁, lM.1 ∈ orderings (univ.erase v) := fun lM h ↦ (mem_sigma.1 h).1
  have hcsf : ∀ i ∈ S₁.disjSum S₂, csf i ⊆ Gf := by
    rintro (lM | R) h
    · simp only [inl_mem_disjSum] at h
      exact (subset_biUnion_of_mem (fun lM : Σ _ : List ι, Finset ι ↦ boxConsL lM.2 lM.1) h).trans
        (subset_union_right.trans subset_union_left)
    · simp only [inr_mem_disjSum] at h
      exact (subset_biUnion_of_mem (qCons v) h).trans subset_union_right
  have hfacet : ∀ q : ι → ℝ, ∑ j, q j = 1 → q v = 0 → (∀ g ∈ Gf, g.a ⬝ᵥ q ≠ g.b) →
      ∑ i ∈ S₁.disjSum S₂, coef i * (facetPoly v (csf i)).indicator 1 q = 0 := by
    intro q hq hqv hqG
    have hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b := fun g hg ↦
      hqG g (mem_union_left _ (mem_union_left _ hg))
    rw [sum_disjSum]
    simp only [coef, csf, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib]
    rw [sum_sigma, thermostat hn hq hqv hgen, qcount _ hgen, ← sub_eq_add_neg, ← mul_sub,
      sub_eq_zero.2, mul_zero]
    set s := ((univ.erase v).filter fun i ↦ 0 < q i).card
    refine (sum_coeffs_mul_choose m ?_ ?_).symm
    · rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, filter_eq_empty_iff]
      intro h
      have : ∑ j, q j ≤ 0 := by
        rw [← add_sum_erase _ _ (mem_univ v), hqv, zero_add]
        exact sum_nonpos fun i hi ↦ not_lt.1 (h hi)
      linarith
    · exact (card_filter_le _ _).trans (by rw [card_erase_of_mem (mem_univ v), card_univ])
  have hT := transfer (S₁.disjSum S₂) coef (fun i ↦ pyrCons v (csf i)) (pyrCons v Gf)
    (isNonconst_of_mem_pyrCons (fun g hg ↦ by
      simp only [Gf, mem_union, mem_biUnion] at hg
      rcases hg with (hg | ⟨lM, hlM, hg⟩) | ⟨R, -, hg⟩
      · exact nonconst_facetGen hg hn
      · exact nonconst_boxConsL (hS₁ lM hlM) _ hg hn
      · exact nonconst_qCons hg hn) (by omega))
    (fun i hi ↦ pyrCons_mono (hcsf i hi))
    (by
      rintro (lM | R) h
      · simp only [inl_mem_disjSum] at h
        exact isBounded_pyr (box_nonempty (hS₁ lM h) _ (by omega)) (isBounded_box (hS₁ lM h) _
          (by omega))
      · exact isBounded_pyr (facetPoly_qCons_nonempty (by omega) R)
          (isBounded_facetPoly_qCons v R))
    (fun p hp hpG ↦ pyr_generic v _ coef csf Gf hfacet p hp hpG)
  rw [sum_disjSum] at hT
  simpa [coef, csf, sub_eq_add_neg, neg_smul, pyr] using hT

/-- The main step: for `card ι ≥ 3`, if maxima of `card ι - 1` linear forms are computable with
two hidden layers, then so is `max (x_i)_i`. -/
theorem supportFun_simplex_mem_reluNet (hn : 3 ≤ Fintype.card ι)
    (hL : maxSpan ι (Fintype.card ι - 1) ≤ reluNet ι 2) :
    supportFun (simplex : Set (ι → ℝ)) ∈ reluNet ι 2 := by
  set m := Fintype.card ι - 1
  set T := univ.powerset.filter fun R : Finset ι ↦ R.Nonempty ∧ R ≠ univ
  -- the paramid sum
  set P : (ι → ℝ) → ℝ := ∑ v, ∑ lM ∈ (orderings (univ.erase v)).sigma markings,
    (-1 : ℝ) ^ lM.2.card • supportFun (pyr v (boxConsL lM.2 lM.1))
  have hP : P ∈ reluNet ι 2 := by
    refine Submodule.sum_mem _ fun v _ ↦ Submodule.sum_mem _ fun lM hlM ↦ ?_
    have hl := (mem_sigma.1 hlM).1
    refine Submodule.smul_mem _ _ ?_
    have : supportFun (pyr v (boxConsL lM.2 lM.1)) =
        fun x ↦ max ((Pi.single v 1 : ι → ℝ) ⬝ᵥ x)
          (supportFun (facetPoly v (boxConsL lM.2 lM.1)) x) := by
      ext x
      rw [supportFun_pyr (box_nonempty hl _ (by omega)) (isBounded_box hl _ (by omega)),
        single_dotProduct, one_mul]
    rw [this]
    exact reluNet.max_mem (reluNet.linear_mem 1 _) (supportFun_box_mem hl _ (by omega))
  -- swap the order of summation over pairs `(v, R)` with `v ∉ R`
  set K : ℝ := ∑ R ∈ T, coeffs m R.card * (Rᶜ.card : ℝ)
  have hK : K = Fintype.card ι * psi m m := by
    have := sum_sum_powerset_erase_comm fun (_ : ι) R ↦ coeffs m R.card
    simp only [sum_const, nsmul_eq_mul] at this
    rw [show K = ∑ R ∈ T, (Rᶜ.card : ℝ) * coeffs m R.card by simp [K, mul_comm], ← this]
    rw [sum_congr rfl fun v _ ↦ sum_filter_nonempty_coeffs (X := univ.erase v)
      (by rw [card_erase_of_mem (mem_univ v), card_univ]) (by omega)]
    simp
  have hKne : K ≠ 0 := by
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    rw [hK]
    exact mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (psi_self_ne_zero m)
  -- the combined identity modulo `maxSpan`
  have hQ : ∑ v, ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
      coeffs m R.card • supportFun (pyr v (qCons v R)) - K • supportFun simplex ∈ maxSpan ι m := by
    rw [sum_sum_powerset_erase_comm fun v R ↦ coeffs m R.card • supportFun (pyr v (qCons v R))]
    simp_rw [← smul_sum]
    have : K • supportFun (simplex : Set (ι → ℝ)) =
        ∑ R ∈ T, coeffs m R.card • ((Rᶜ.card : ℝ) • supportFun simplex) := by
      simp only [smul_smul, ← sum_smul, K]
    rw [this, ← sum_sub_distrib]
    refine Submodule.sum_mem _ fun R hR ↦ ?_
    simp only [mem_filter] at hR
    rw [← smul_sub]
    exact Submodule.smul_mem _ _ (subdivision hR.2.1 hR.2.2)
  have hV : P - ∑ v, ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
      coeffs m R.card • supportFun (pyr v (qCons v R)) ∈ maxSpan ι m := by
    rw [← sum_sub_distrib]
    exact Submodule.sum_mem _ fun v _ ↦ vertex_identity hn v
  have hsum : P - K • supportFun simplex ∈ maxSpan ι m := by
    have := Submodule.add_mem _ hV hQ
    rwa [sub_add_sub_cancel] at this
  have : supportFun (simplex : Set (ι → ℝ)) = K⁻¹ • (P - (P - K • supportFun simplex)) := by
    rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hKne, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hP (hL hsum))

omit [DecidableEq ι] in
/-- Maxima of at most `n` linear forms are computable with two hidden layers once
`max (x₁, …, xₙ)` is. -/
theorem maxSpan_le_reluNet {n : ℕ} [NeZero n]
    (h : (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∈ reluNet (Fin n) 2) :
    maxSpan ι n ≤ reluNet ι 2 := by
  classical
  refine Submodule.span_le.2 ?_
  rintro f ⟨W, hW, hcard, rfl⟩
  obtain ⟨w₀, hw₀⟩ := hW
  -- enumerate `W` by `Fin n`, repeating `w₀`
  let e : Fin n → ι → ℝ := fun k ↦
    if hk : (k : ℕ) < W.card then (W.equivFin.symm ⟨k, hk⟩ : ι → ℝ) else w₀
  have he : ∀ k, e k ∈ W := by
    intro k
    simp only [e]
    split_ifs
    · exact Finset.coe_mem _
    · exact hw₀
  have hsurj : ∀ w ∈ W, ∃ k, e k = w := by
    intro w hw
    refine ⟨⟨W.equivFin ⟨w, hw⟩, (W.equivFin ⟨w, hw⟩).isLt.trans_le hcard⟩, ?_⟩
    simp [e]
  let A : (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin (Matrix.of e)
  have hA : maxLin W = (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∘ A := by
    ext x
    have hWne : W.Nonempty := ⟨w₀, hw₀⟩
    simp only [maxLin, dif_pos hWne, Function.comp_apply, A, Matrix.mulVecLin_apply]
    have hmv : ∀ k, (Matrix.of e).mulVec x k = e k ⬝ᵥ x := fun k ↦ rfl
    simp only [hmv]
    apply le_antisymm
    · refine sup'_le _ _ fun w hw ↦ ?_
      obtain ⟨k, rfl⟩ := hsurj w hw
      exact le_sup'_of_le _ (mem_univ k) le_rfl
    · exact sup'_le _ _ fun k _ ↦ le_sup' (· ⬝ᵥ x) (he k)
  rw [hA]
  exact reluNet.comp_linearMap A h

theorem max_mem_reluNet_succ (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ ↦ univ.sup' univ_nonempty x) ∈ reluNet (Fin (n + 1)) 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | _ | n
  · have : (fun x : Fin 1 → ℝ ↦ univ.sup' univ_nonempty x) =
        fun x ↦ (Pi.single 0 1 : Fin 1 → ℝ) ⬝ᵥ x := by
      ext x
      simp [single_dotProduct, univ_unique]
    rw [this]
    exact reluNet.linear_mem 2 _
  · have : (fun x : Fin 2 → ℝ ↦ univ.sup' univ_nonempty x) =
        fun x ↦ max ((Pi.single 0 1 : Fin 2 → ℝ) ⬝ᵥ x) ((Pi.single 1 1 : Fin 2 → ℝ) ⬝ᵥ x) := by
      ext x
      simp only [single_dotProduct, one_mul]
      apply le_antisymm
      · refine sup'_le _ _ fun k _ ↦ ?_
        fin_cases k
        exacts [le_max_left _ _, le_max_right _ _]
      · exact max_le (le_sup' x (mem_univ 0)) (le_sup' x (mem_univ 1))
    rw [this]
    exact reluNet.max_mem (reluNet.linear_mem 1 _) (reluNet.linear_mem 1 _)
  · have hL : maxSpan (Fin (n + 3)) (Fintype.card (Fin (n + 3)) - 1) ≤ reluNet (Fin (n + 3)) 2 := by
      rw [Fintype.card_fin]
      exact maxSpan_le_reluNet (n := n + 2) (ih (n + 1) (by omega))
    have := supportFun_simplex_mem_reluNet (by simp) hL
    rwa [show supportFun (simplex : Set (Fin (n + 3) → ℝ)) = fun x ↦ univ.sup' univ_nonempty x
      from funext supportFun_simplex] at this

/-- **Two hidden ReLU layers compute the maximum**: `MAXₙ ∈ ReLU_{n,2}`. -/
theorem max_mem_reluNet (n : ℕ) [NeZero n] :
    (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∈ reluNet (Fin n) 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact max_mem_reluNet_succ k

/-- **Two hidden ReLU layers compute the maximum**, with an explicit network:
there are widths `k₁, k₂` and weights such that for all `x : Fin n → ℝ`,
`max (x₁, …, xₙ) = w₃ ⬝ᵥ relu (W₂ *ᵥ relu (W₁ *ᵥ x + b₁) + b₂) + b₃`. -/
theorem exists_twoLayerNet_eq_max (n : ℕ) [NeZero n] :
    ∃ (k₁ k₂ : ℕ) (W₁ : Matrix (Fin k₁) (Fin n) ℝ) (b₁ : Fin k₁ → ℝ)
      (W₂ : Matrix (Fin k₂) (Fin k₁) ℝ) (b₂ : Fin k₂ → ℝ) (w₃ : Fin k₂ → ℝ) (b₃ : ℝ),
      ∀ x : Fin n → ℝ, univ.sup' univ_nonempty x = twoLayerNet W₁ b₁ W₂ b₂ w₃ b₃ x := by
  obtain ⟨k₁, k₂, W₁, b₁, W₂, b₂, w₃, b₃, h⟩ := reluNet.exists_twoLayerNet (max_mem_reluNet n)
  exact ⟨k₁, k₂, W₁, b₁, W₂, b₂, w₃, b₃, fun x ↦ congr_fun h x⟩

end

end AuthorReal

-- Source module: Solutions/FieldLinear.lean

namespace FieldLinear
noncomputable section
open Matrix Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

 theorem det_mem (R : Subfield ℝ) (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j ∈ R) :
    A.det ∈ R := by
  rw [Matrix.det_apply]
  apply R.sum_mem
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  exact R.mul_mem (R.intCast_mem _) (R.prod_mem fun i _ => hA _ _)

 theorem unique_square_solution_mem (R : Subfield ℝ) (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j ∈ R) {b p : ι → ℝ} (hb : ∀ i, b i ∈ R)
    (hdet : A.det ≠ 0) (hp : A.mulVec p = b) : ∀ i, p i ∈ R := by
  intro i
  have hvec : A.cramer (A.mulVec p) = A.det • p := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have h := congrFun hvec i
  rw [hp, Matrix.cramer_apply] at h
  have heq : p i = (A.updateCol i b).det / A.det := by
    change (A.updateCol i b).det = A.det * p i at h
    exact (eq_div_iff hdet).2 (by linarith)
  rw [heq]
  apply R.div_mem _ (det_mem R A hA)
  apply det_mem R
  intro j k
  simp only [Matrix.updateCol_apply]
  split_ifs <;> first | apply hb | apply hA

 theorem unique_solution_mem (R : Subfield ℝ) (A : Matrix κ ι ℝ)
    (hA : ∀ i j, A i j ∈ R) {b : κ → ℝ} (hb : ∀ i, b i ∈ R)
    (hinj : Function.Injective A.mulVec) {p : ι → ℝ} (hp : A.mulVec p = b) :
    ∀ i, p i ∈ R := by
  let G := A.transpose * A
  have hg : G.det ≠ 0 := by
    have hpos := Matrix.PosDef.conjTranspose_mul_self A hinj
    have hG : A.conjTranspose = A.transpose := by ext i j; simp
    rw [hG] at hpos
    exact hpos.det_pos.ne'
  apply unique_square_solution_mem R G _ (b := A.transpose.mulVec b) _ hg
  · dsimp only [G]
    rw [← Matrix.mulVec_mulVec, hp]
  · intro i j
    exact R.sum_mem fun k _ => R.mul_mem (hA k i) (hA k j)
  · intro i
    exact R.sum_mem fun k _ => R.mul_mem (hA k i) (hb k)

end
end FieldLinear

-- Source module: Solutions/FieldExtreme.lean

namespace AuthorReal
noncomputable section
open Finset Filter Topology Matrix

variable {ι : Type*} [Fintype ι]

theorem extremePoint_over (R : Subfield ℝ) {cs : Finset (Constraint ι)}
    (hcs : ∀ c ∈ cs, (∀ i, c.a i ∈ R) ∧ c.b ∈ R)
    {p : ι → ℝ} (hp : p ∈ (hpoly cs).extremePoints ℝ) : ∀ i, p i ∈ R := by
  classical
  let T := cs.filter (fun c => c.a ⬝ᵥ p = c.b)
  let A : Matrix (Option T) ι ℝ := fun c => c.elim (fun _ => 1) (fun c => c.val.a)
  let b : Option T → ℝ := fun c => c.elim 1 (fun c => c.val.b)
  have hzero : ∀ d : ι → ℝ, A.mulVec d = 0 → d = 0 := by
    intro d hd
    have hsum : ∑ i, d i = 0 := by simpa [A, Matrix.mulVec, dotProduct] using congrFun hd none
    have htight : ∀ c ∈ cs, c.a ⬝ᵥ p = c.b → c.a ⬝ᵥ d = 0 := by
      intro c hc hcp
      exact congrFun hd (some ⟨c, mem_filter.mpr ⟨hc, hcp⟩⟩)
    let φ : ℝ → ι → ℝ := fun ε => p + ε • d
    have hcont : Continuous φ := by fun_prop
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), φ ε ∈ hpoly cs := by
      have hslack : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ c ∈ cs, c.a ⬝ᵥ p ≠ c.b → c.a ⬝ᵥ φ ε < c.b := by
        rw [eventually_all_finset]
        intro c hc
        by_cases hcp : c.a ⬝ᵥ p = c.b
        · exact Eventually.of_forall fun _ h => (h hcp).elim
        · have hlt : c.a ⬝ᵥ φ 0 < c.b := by
            simpa [φ] using lt_of_le_of_ne (hp.1.2 c hc) hcp
          exact ((continuous_const.dotProduct hcont).continuousAt.eventually_lt
            continuousAt_const hlt).mono fun ε hε _ => hε
      filter_upwards [hslack] with ε hε
      refine ⟨?_, fun c hc => ?_⟩
      · simp [φ, sum_add_distrib, ← mul_sum, hp.1.1, hsum]
      · by_cases hcp : c.a ⬝ᵥ p = c.b
        · simp [φ, dotProduct_add, dotProduct_smul, hcp, htight c hc hcp]
        · exact (hε c hc hcp).le
    have hevneg : ∀ᶠ ε in 𝓝 (0 : ℝ), φ (-ε) ∈ hpoly cs :=
      (show Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 0) by
        simpa using continuous_neg.tendsto (0 : ℝ)).eventually hev
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    obtain ⟨ε, hε, hplus, hminus⟩ :=
      (hpos.and ((hev.and hevneg).filter_mono nhdsWithin_le_nhds)).exists
    have hseg : p ∈ openSegment ℝ (φ ε) (φ (-ε)) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      dsimp [φ]
      module
    have heq := ((mem_extremePoints.mp hp).2 _ hplus _ hminus hseg).1
    have hsd : ε • d = 0 := by
      have hsd : p + ε • d = p := heq
      exact add_left_cancel (hsd.trans (add_zero p).symm)
    exact (smul_eq_zero.mp hsd).resolve_left hε.ne'
  have hinj : Function.Injective A.mulVec := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hzero
    simp [Matrix.mulVec_sub, huv]
  apply FieldLinear.unique_solution_mem R A _ (b := b) _ hinj
  · funext c
    cases c with
    | none => simpa [A, b, Matrix.mulVec, dotProduct] using hp.1.1
    | some c => exact (mem_filter.mp c.property).2
  · intro c i
    cases c with
    | none => exact R.one_mem
    | some c => exact (hcs c.val (mem_filter.mp c.property).1).1 i
  · intro c
    cases c with
    | none => exact R.one_mem
    | some c => exact (hcs c.val (mem_filter.mp c.property).1).2

end
end AuthorReal

-- Source module: Solutions/RationalSpan.lean

namespace AuthorReal
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι]

def rationalPoint (p : ι → ℝ) : Prop := ∀ i, p i ∈ (⊥ : Subfield ℝ)

def rationalMaxSpan (ι : Type*) [Fintype ι] (k : ℕ) : Submodule ℚ ((ι → ℝ) → ℝ) :=
  Submodule.span ℚ {f | ∃ W : Finset (ι → ℝ), W.Nonempty ∧ W.card ≤ k ∧
    (∀ w ∈ W, rationalPoint w) ∧ f = maxLin W}

theorem maxLin_mem_rationalMaxSpan_of_card_le {W : Finset (ι → ℝ)} (hW : W.Nonempty) {k : ℕ}
    (hk : W.card ≤ k) (hR : ∀ w ∈ W, rationalPoint w) : maxLin W ∈ rationalMaxSpan ι k :=
  Submodule.subset_span ⟨W, hW, hk, hR, rfl⟩

theorem linear_mem_rationalMaxSpan (t : ι → ℝ) (ht : rationalPoint t) {k : ℕ} (hk : 1 ≤ k) :
    (fun x => t ⬝ᵥ x) ∈ rationalMaxSpan ι k := by
  rw [← maxLin_singleton]
  exact maxLin_mem_rationalMaxSpan_of_card_le (singleton_nonempty t)
    (by simpa using hk) (by simpa using ht)

theorem maxLin_mem_rationalMaxSpan (W : Finset (ι → ℝ))
    (hR : ∀ w ∈ W, rationalPoint w) (A : AffineSubspace ℝ (ι → ℝ))
    (hW : (W : Set (ι → ℝ)) ⊆ A) {d : ℕ} (hA : Module.finrank ℝ A.direction ≤ d) :
    maxLin W ∈ rationalMaxSpan ι (d + 1) := by
  classical
  induction W using Finset.strongInduction with
  | H W ih =>
  rcases W.eq_empty_or_nonempty with rfl | hne
  · rw [maxLin_empty]; exact zero_mem _
  by_cases hai : AffineIndependent ℝ ((↑) : W → ι → ℝ)
  · refine maxLin_mem_rationalMaxSpan_of_card_le hne ?_ hR
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hne.card_pos.ne'
    have h₁ := hai.finrank_vectorSpan (n := n) (by simpa using hn)
    have h₂ : vectorSpan ℝ (Set.range ((↑) : W → ι → ℝ)) ≤ A.direction := by
      rw [Subtype.range_coe_subtype]
      exact vectorSpan_mono ℝ hW
    have h₃ := Submodule.finrank_mono h₂
    omega
  obtain ⟨I, z, hz₁, hz₂⟩ := Convex.radon_partition hai
  set I' : Finset (ι → ℝ) := W.filter fun w => ∃ h : w ∈ W, (⟨w, h⟩ : W) ∈ I
  have hI' : ((↑) : W → ι → ℝ) '' I = I' := by
    ext w; simp [I']
  have hI'c : ((↑) : W → ι → ℝ) '' Iᶜ = ↑(W \ I') := by
    ext w
    simp only [Set.mem_image, Set.mem_compl_iff, Subtype.exists, exists_and_right,
      exists_eq_right, coe_sdiff, coe_filter, and_exists_self, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_ofPred_eq, not_exists, I']
    exact ⟨fun ⟨h, h'⟩ => ⟨h, fun _ => h'⟩, fun ⟨h, h'⟩ => ⟨h, h' h⟩⟩
  rw [hI'] at hz₁
  rw [hI'c] at hz₂
  have heq : maxLin W = -∑ S ∈ I'.powerset.erase ∅, (-1 : ℚ)^S.card • maxLin (W \ S) := by
    rw [maxLin_eq_neg_sum_of_radon hz₁ hz₂]
    congr 1
    apply sum_congr rfl
    intro S _
    ext x
    simp [Algebra.smul_def]
  rw [heq]
  refine neg_mem (sum_mem fun S hS => Submodule.smul_mem _ _ (ih _ ?_
    (fun w hw => hR w (mem_sdiff.mp hw).1) ((coe_subset.2 sdiff_subset).trans hW)))
  obtain ⟨hS0, hS⟩ := mem_erase.1 hS
  exact sdiff_ssubset ((mem_powerset.1 hS).trans (filter_subset _ _)) (nonempty_iff_ne_empty.2 hS0)

end
end AuthorReal

-- Source module: Solutions/RationalHPolytope.lean

namespace AuthorReal
noncomputable section
open Finset Filter Topology
variable {ι : Type*} [Fintype ι]

def rationalConstraint (c : Constraint ι) : Prop := rationalPoint c.a ∧ c.b ∈ (⊥ : Subfield ℝ)

theorem rationalConstraint_rev {c : Constraint ι} (hc : rationalConstraint c) :
    rationalConstraint c.rev := by
  exact ⟨fun i => (⊥ : Subfield ℝ).neg_mem (hc.1 i), (⊥ : Subfield ℝ).neg_mem hc.2⟩

theorem rational_cellCons {F S : Finset (Constraint ι)} (hF : ∀ c ∈ F, rationalConstraint c)
    (hS : S ⊆ F) : ∀ c ∈ cellCons F S, rationalConstraint c := by
  intro c hc
  rcases mem_union.mp hc with hc | hc
  · exact hF c (hS hc)
  · obtain ⟨d, hd, rfl⟩ := mem_image.mp hc
    exact rationalConstraint_rev (hF d (mem_sdiff.mp hd).1)

theorem q_supportFun_mem_maxSpan_of_subset {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) {g : Constraint ι} (hg : g.IsNonconst)
    (hsub : hpoly cs ⊆ {p | g.a ⬝ᵥ p = g.b})
    (hR : ∀ c ∈ cs, rationalConstraint c) :
    supportFun (hpoly cs) ∈ rationalMaxSpan ι (Fintype.card ι - 1) := by
  classical
  rcases (hpoly cs).eq_empty_or_nonempty with hemp | ⟨p₀, hp₀⟩
  · rw [hemp, supportFun_empty]
    exact zero_mem _
  obtain ⟨i, j, hij⟩ := hg
  have hij' : i ≠ j := fun h ↦ hij (h ▸ rfl)
  have hcard : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.2 ⟨i, j, hij'⟩
  let L : (ι → ℝ) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun d ↦ (∑ k, d k, g.a ⬝ᵥ d)
      map_add' := fun d e ↦ by simp [sum_add_distrib, dotProduct_add]
      map_smul' := fun r d ↦ by simp [mul_sum, dotProduct_smul] }
  have hL : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨s, t⟩
    have hne : g.a i - g.a j ≠ 0 := sub_ne_zero.2 hij
    refine ⟨s • Pi.single i 1 + ((t - s * g.a i) / (g.a i - g.a j)) •
      (Pi.single i 1 - Pi.single j 1), ?_⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq]
    constructor
    · simp [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    · simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, dotProduct_single, smul_eq_mul]
      field_simp
      ring
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [hL, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hrank
  let A : AffineSubspace ℝ (ι → ℝ) := AffineSubspace.mk' p₀ (LinearMap.ker L)
  have hK := isCompact_hpoly hb
  have hfin := finite_extremePoints_hpoly cs
  rw [supportFun_eq_maxLin_of_finite hK (convex_hpoly cs) ⟨p₀, hp₀⟩ hfin]
  have hEA : (hfin.toFinset : Set (ι → ℝ)) ⊆ A := by
    intro e he
    have heK : e ∈ hpoly cs := extremePoints_subset (by simpa using he)
    have h1 : g.a ⬝ᵥ e = g.b := hsub heK
    have h2 : g.a ⬝ᵥ p₀ = g.b := hsub hp₀
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', LinearMap.mem_ker]
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, vsub_eq_sub, Pi.sub_apply, sum_sub_distrib,
      heK.1, hp₀.1, sub_self, dotProduct_sub, h1, h2, Prod.mk_zero_zero]
  have hdim : Module.finrank ℝ A.direction ≤ Fintype.card ι - 2 := by
    rw [AffineSubspace.direction_mk']
    omega
  have := maxLin_mem_rationalMaxSpan _
    (fun p hp => extremePoint_over (⊥ : Subfield ℝ) hR (by simpa using hp)) A hEA hdim
  rwa [show Fintype.card ι - 2 + 1 = Fintype.card ι - 1 by omega] at this


/-! ### Cells of a hyperplane arrangement -/

/-- The reversed constraint `⟪a, p⟫ ≥ b`. -/
theorem q_supportFun_inter_cell_mem_maxSpan {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) {F S : Finset (Constraint ι)} {g : Constraint ι}
    (hg : g.IsNonconst) (hsub : hpoly cs ∩ cell F S ⊆ {p | g.a ⬝ᵥ p = g.b})
    (hR : ∀ c ∈ cs, rationalConstraint c) (hF : ∀ c ∈ F, rationalConstraint c)
    (hS : S ⊆ F) :
    supportFun (hpoly cs ∩ cell F S) ∈ rationalMaxSpan ι (Fintype.card ι - 1) := by
  rw [← hpoly_union_cellCons] at hsub ⊢
  exact q_supportFun_mem_maxSpan_of_subset
    (by rw [hpoly_union_cellCons]; exact hb.subset Set.inter_subset_left) hg hsub (fun c hc => (mem_union.mp hc).elim (hR c) (rational_cellCons hF hS c))

theorem q_supportFun_sub_sum_cell_mem_maxSpan {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) (F : Finset (Constraint ι))
    (hF : ∀ g ∈ F, g.IsNonconst) (hR : ∀ c ∈ cs, rationalConstraint c)
    (hFR : ∀ c ∈ F, rationalConstraint c) :
    supportFun (hpoly cs) - ∑ S ∈ F.powerset, supportFun (hpoly cs ∩ cell F S) ∈
      rationalMaxSpan ι (Fintype.card ι - 1) := by
  induction F using Finset.induction_on with
  | empty => simp [cell_empty_empty]
  | insert g F hgF ih =>
    have ih := ih (fun g' hg' ↦ hF g' (mem_insert_of_mem hg')) (fun c hc => hFR c (mem_insert_of_mem hc))
    have hg := hF g (mem_insert_self g F)
    rw [sum_powerset_insert hgF]
    have key : ∀ S ∈ F.powerset, supportFun (hpoly cs ∩ cell (insert g F) S) +
        supportFun (hpoly cs ∩ cell (insert g F) (insert g S)) =
        supportFun (hpoly cs ∩ cell F S) +
          supportFun (hpoly cs ∩ cell F S ∩ {p | g.a ⬝ᵥ p = g.b}) := by
      intro S hS
      have hgS : g ∉ S := fun h ↦ hgF (mem_powerset.1 hS h)
      have hcut := supportFun_cut (isCompact_hpoly_inter_cell hb F S)
        (convex_hpoly_inter_cell cs F S) g.a g.b
      rw [cell_insert_of_notMem hgS, cell_insert_insert hgF, ← Set.inter_assoc,
        ← Set.inter_assoc, hcut]
      abel
    have hmem : ∑ S ∈ F.powerset, supportFun (hpoly cs ∩ cell F S ∩ {p | g.a ⬝ᵥ p = g.b}) ∈
        rationalMaxSpan ι (Fintype.card ι - 1) := by
      refine sum_mem fun S hS ↦ ?_
      rw [← hpoly_union_cellCons, ← hpoly_union_pair_rev]
      refine q_supportFun_mem_maxSpan_of_subset ?_ hg ?_ ?_
      · rw [hpoly_union_pair_rev, hpoly_union_cellCons]
        exact hb.subset (Set.inter_subset_left.trans Set.inter_subset_left)
      · rw [hpoly_union_pair_rev]
        exact Set.inter_subset_right
      · intro c hc
        rcases mem_union.mp hc with hc | hc
        · rcases mem_union.mp hc with hc | hc
          · exact hR c hc
          · exact rational_cellCons (fun c hc => hFR c (mem_insert_of_mem hc)) (mem_powerset.mp hS) c hc
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
          rcases hc with hc | hc
          · rw [hc]; exact hFR g (mem_insert_self _ _)
          · rw [hc]; exact rationalConstraint_rev (hFR g (mem_insert_self _ _))
    rw [← sum_add_distrib, sum_congr rfl key, sum_add_distrib]
    convert sub_mem ih hmem using 1
    abel

/-- A convex set on which each of finitely many affine functions is not identically zero
contains a point at which none of them vanishes. -/
theorem q_sum_smul_q_supportFun_inter_cell_mem_maxSpan {κ : Type*} (s : Finset κ) (c : κ → ℚ)
    (cs : κ → Finset (Constraint ι)) (G : Finset (Constraint ι)) (hG : ∀ g ∈ G, g.IsNonconst)
    (hcs : ∀ i ∈ s, cs i ⊆ G) (hbdd : ∀ i ∈ s, Bornology.IsBounded (hpoly (cs i)))
    (hgen : ∀ p : ι → ℝ, ∑ j, p j = 1 → (∀ g ∈ G, g.a ⬝ᵥ p ≠ g.b) →
      ∑ i ∈ s, (c i : ℝ) * (hpoly (cs i)).indicator 1 p = 0) (S : Finset (Constraint ι))
    (hGR : ∀ c ∈ G, rationalConstraint c) (hS : S ⊆ G) :
    ∑ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) ∈ rationalMaxSpan ι (Fintype.card ι - 1) := by
  classical
  by_cases hz : ∃ z ∈ hpoly ∅ ∩ cell G S, ∀ g ∈ G, g.a ⬝ᵥ z ≠ g.b
  · obtain ⟨z, ⟨hzH, hzc⟩, hzg⟩ := hz
    have hsumreal := hgen z hzH.1 hzg
    have hsum : ∑ i ∈ s, c i * (if z ∈ hpoly (cs i) then 1 else 0 : ℚ) = 0 := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      simpa [Set.indicator_apply, apply_ite] using hsumreal
    have key : ∀ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) -
        (c i * (if z ∈ hpoly (cs i) then 1 else 0 : ℚ)) • supportFun (hpoly ∅ ∩ cell G S) ∈
          rationalMaxSpan ι (Fintype.card ι - 1) := by
      intro i hi
      by_cases hzi : z ∈ hpoly (cs i)
      · have heq : hpoly (cs i) ∩ cell G S = hpoly ∅ ∩ cell G S := by
          ext p
          constructor
          · rintro ⟨hp, hpc⟩
            exact ⟨⟨hp.1, by simp⟩, hpc⟩
          · rintro ⟨hp, hpc⟩
            refine ⟨⟨hp.1, fun d hd ↦ ?_⟩, hpc⟩
            have hdG := hcs i hi hd
            have hdS : d ∈ S := by
              by_contra hdS
              exact hzg d hdG (le_antisymm (hzi.2 d hd) (hzc.2 d hdG hdS))
            exact hpc.1 d hdS
        simp only [heq, if_pos hzi, mul_one, sub_self]
        
        exact zero_mem _
      · simp only [if_neg hzi, mul_zero, zero_smul, sub_zero]
        refine Submodule.smul_mem _ _ ?_
        have : ∃ d ∈ cs i, d.b < d.a ⬝ᵥ z := by
          by_contra! h
          exact hzi ⟨hzH.1, h⟩
        obtain ⟨d, hd, hdz⟩ := this
        have hdG := hcs i hi hd
        have hdS : d ∉ S := fun h ↦ (hzc.1 d h).not_gt hdz
        refine q_supportFun_inter_cell_mem_maxSpan (hbdd i hi) (hG d hdG) ?_ (fun c hc => hGR c (hcs i hi hc)) hGR hS
        rintro p ⟨hp, hpc⟩
        exact le_antisymm (hp.2 d hd) (hpc.2 d hdG hdS)
    have := sum_mem key
    rwa [sum_sub_distrib, ← sum_smul, hsum, zero_smul, sub_zero] at this
  · push Not at hz
    refine sum_mem fun i hi ↦ Submodule.smul_mem _ _ ?_
    rcases (hpoly (cs i) ∩ cell G S).eq_empty_or_nonempty with hemp | hne
    · rw [hemp, supportFun_empty]
      exact zero_mem _
    · have : ∃ g ∈ G, ∀ q ∈ hpoly (cs i) ∩ cell G S, g.a ⬝ᵥ q = g.b := by
        by_contra! h
        obtain ⟨p, ⟨hp, hpc⟩, hpg⟩ :=
          exists_forall_ne_of_convex (convex_hpoly_inter_cell _ _ _) hne G h
        obtain ⟨g, hg, hgp⟩ := hz p ⟨⟨hp.1, by simp⟩, hpc⟩
        exact hpg g hg hgp
      obtain ⟨g, hg, hgq⟩ := this
      exact q_supportFun_inter_cell_mem_maxSpan (hbdd i hi) (hG g hg) hgq (fun c hc => hGR c (hcs i hi hc)) hGR hS

/-- **Transfer principle.** Let `G` be a finite set of hyperplanes, none parallel to
`∑ pᵢ = 1`, containing all constraints of the bounded polytopes `hpoly (cs i)`. If
`∑ i, c i * 1_{hpoly (cs i)}` vanishes at every point of `∑ pᵢ = 1` off the hyperplanes in `G`,
then `∑ i, c i • h_{hpoly (cs i)}` is a linear combination of maxima of `card ι - 1` linear forms.
-/
theorem q_transfer {κ : Type*} (s : Finset κ) (c : κ → ℚ) (cs : κ → Finset (Constraint ι))
    (G : Finset (Constraint ι)) (hG : ∀ g ∈ G, g.IsNonconst) (hcs : ∀ i ∈ s, cs i ⊆ G)
    (hbdd : ∀ i ∈ s, Bornology.IsBounded (hpoly (cs i)))
    (hGR : ∀ c ∈ G, rationalConstraint c)
    (hgen : ∀ p : ι → ℝ, ∑ j, p j = 1 → (∀ g ∈ G, g.a ⬝ᵥ p ≠ g.b) →
      ∑ i ∈ s, (c i : ℝ) * (hpoly (cs i)).indicator 1 p = 0) :
    ∑ i ∈ s, c i • supportFun (hpoly (cs i)) ∈ rationalMaxSpan ι (Fintype.card ι - 1) := by
  have h1 := sum_mem fun i hi ↦
    Submodule.smul_mem _ (c i) (q_supportFun_sub_sum_cell_mem_maxSpan (hbdd i hi) G hG (fun c hc => hGR c (hcs i hi hc)) hGR)
  have h2 : ∑ S ∈ G.powerset, ∑ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) ∈
      rationalMaxSpan ι (Fintype.card ι - 1) :=
    sum_mem fun S hS ↦ q_sum_smul_q_supportFun_inter_cell_mem_maxSpan s c cs G hG hcs hbdd hgen S hGR (mem_powerset.mp hS)
  convert add_mem h1 h2 using 1
  simp only [smul_sub, sum_sub_distrib, smul_sum]
  rw [sum_comm (s := s)]
  abel

end
end AuthorReal

-- Source module: Solutions/RationalNetwork.lean

namespace AuthorReal
noncomputable section
open Finset Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def qreluNet (ι : Type*) [Fintype ι] : ℕ → Submodule ℚ ((ι → ℝ) → ℝ)
  | 0 => Submodule.span ℚ (insert (fun _ => 1)
      (Set.range fun (a : ι → ℚ) (x : ι → ℝ) => (fun i => (a i : ℝ)) ⬝ᵥ x))
  | k + 1 => Submodule.span ℚ (insert (fun _ => 1)
      {f | ∃ g ∈ qreluNet ι k, f = fun x => relu (g x)})

namespace qreluNet

theorem one_mem (k : ℕ) : (fun _ => (1 : ℝ)) ∈ qreluNet ι k := by
  cases k <;> exact Submodule.subset_span (Set.mem_insert _ _)

theorem const_mem (k : ℕ) (c : ℚ) : (fun _ => (c : ℝ)) ∈ qreluNet ι k := by
  convert Submodule.smul_mem _ c (one_mem (ι := ι) k) using 1
  ext x
  simp [Algebra.smul_def]

theorem relu_mem {k : ℕ} {g : (ι → ℝ) → ℝ} (hg : g ∈ qreluNet ι k) :
    (fun x => relu (g x)) ∈ qreluNet ι (k + 1) :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨g, hg, rfl⟩)

theorem linear_mem_zero (a : ι → ℚ) : (fun x => (fun i => (a i : ℝ)) ⬝ᵥ x) ∈ qreluNet ι 0 :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨a, rfl⟩)

theorem affine_mem_zero (a : ι → ℚ) (b : ℚ) :
    (fun x => (fun i => (a i : ℝ)) ⬝ᵥ x + (b : ℝ)) ∈ qreluNet ι 0 :=
  add_mem (linear_mem_zero a) (const_mem 0 b)

theorem le_succ (k : ℕ) : qreluNet ι k ≤ qreluNet ι (k + 1) := by
  induction k with
  | zero =>
    refine Submodule.span_le.2 ?_
    rintro f (rfl | ⟨a, rfl⟩)
    · exact one_mem 1
    · have h := sub_mem (relu_mem (linear_mem_zero a)) (relu_mem (linear_mem_zero (-a)))
      have he : ((fun x => relu ((fun i => (a i : ℝ)) ⬝ᵥ x)) -
          fun x => relu ((fun i => ((-a) i : ℝ)) ⬝ᵥ x)) =
          fun x => (fun i => (a i : ℝ)) ⬝ᵥ x := by
        ext x
        simp only [Pi.sub_apply, Pi.neg_apply, Rat.cast_neg]
        rw [show (fun i => -(a i : ℝ)) = -(fun i => (a i : ℝ)) from rfl,
          neg_dotProduct, reluNet.relu_sub_relu_neg]
      rw [he] at h
      exact h
  | succ k ih =>
    refine Submodule.span_le.2 ?_
    rintro f (rfl | ⟨g, hg, rfl⟩)
    · exact one_mem _
    · exact relu_mem (ih hg)

theorem mono : Monotone (qreluNet ι) := monotone_nat_of_le_succ le_succ

theorem linear_mem (k : ℕ) (a : ι → ℚ) :
    (fun x => (fun i => (a i : ℝ)) ⬝ᵥ x) ∈ qreluNet ι k :=
  mono (Nat.zero_le k) (linear_mem_zero a)

theorem affine_mem (k : ℕ) (a : ι → ℚ) (b : ℚ) :
    (fun x => (fun i => (a i : ℝ)) ⬝ᵥ x + (b : ℝ)) ∈ qreluNet ι k :=
  mono (Nat.zero_le k) (affine_mem_zero a b)

theorem max_mem {k : ℕ} {g h : (ι → ℝ) → ℝ} (hg : g ∈ qreluNet ι k) (hh : h ∈ qreluNet ι k) :
    (fun x => max (g x) (h x)) ∈ qreluNet ι (k + 1) := by
  convert add_mem (le_succ k hh) (relu_mem (sub_mem hg hh)) using 1
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, relu]
  rw [← max_add_add_left, add_zero, add_sub_cancel]

theorem comp_matrix (A : Matrix κ ι ℚ) {k : ℕ} {f : (κ → ℝ) → ℝ}
    (hf : f ∈ qreluNet κ k) :
    (fun x => f ((A.map (Rat.castHom ℝ)).mulVec x)) ∈ qreluNet ι k := by
  classical
  induction k generalizing f with
  | zero =>
    induction hf using Submodule.span_induction with
    | mem f hf =>
      rcases hf with rfl | ⟨a, rfl⟩
      · exact one_mem 0
      · convert linear_mem_zero (a ᵥ* A) using 1
        ext x
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Rat.cast_sum,
          Rat.cast_mul, Matrix.map_apply, Rat.castHom, sum_mul, mul_sum, mul_assoc]
        rw [sum_comm]
        rfl
    | zero => exact zero_mem _
    | add f g _ _ hf hg => exact add_mem hf hg
    | smul r f _ hf => exact Submodule.smul_mem _ r hf
  | succ k ih =>
    induction hf using Submodule.span_induction with
    | mem f hf =>
      rcases hf with rfl | ⟨g, hg, rfl⟩
      · exact one_mem _
      · exact relu_mem (ih hg)
    | zero => exact zero_mem _
    | add f g _ _ hf hg => exact add_mem hf hg
    | smul r f _ hf => exact Submodule.smul_mem _ r hf

 theorem exists_affine {g : (ι → ℝ) → ℝ} (hg : g ∈ qreluNet ι 0) :
    ∃ (a : ι → ℚ) (c : ℚ), g = fun x => (fun i => (a i : ℝ)) ⬝ᵥ x + (c : ℝ) := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨a, rfl⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨a, 0, by simp⟩
  | zero => exact ⟨0, 0, by ext x; simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨a, c, rfl⟩ := hf
    obtain ⟨a', c', rfl⟩ := hg
    refine ⟨a + a', c + c', ?_⟩
    ext x
    simp only [Pi.add_apply, Rat.cast_add]
    rw [show (fun i => (a i : ℝ) + (a' i : ℝ)) =
      (fun i => (a i : ℝ)) + (fun i => (a' i : ℝ)) from rfl, add_dotProduct]
    ring
  | smul r f _ hf =>
    obtain ⟨a, c, rfl⟩ := hf
    refine ⟨r • a, r * c, ?_⟩
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Algebra.smul_def]
    rw [show (fun i => (r : ℝ) * (a i : ℝ)) = (r : ℝ) • (fun i => (a i : ℝ)) from rfl,
      smul_dotProduct]
    simp [mul_add]

 theorem exists_sum {g : (ι → ℝ) → ℝ} (hg : g ∈ qreluNet ι 1) :
    ∃ (k : ℕ) (a : Fin k → ι → ℚ) (b d : Fin k → ℚ) (c : ℚ),
      g = fun x => ∑ j, (d j : ℝ) * relu ((fun i => (a j i : ℝ)) ⬝ᵥ x + (b j : ℝ)) + (c : ℝ) := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨g, hg, rfl⟩
    · exact ⟨0, ![], ![], ![], 1, by simp⟩
    · obtain ⟨a, b, rfl⟩ := exists_affine hg
      exact ⟨1, ![a], ![b], ![1], 0, by simp⟩
  | zero => exact ⟨0, ![], ![], ![], 0, by ext x; simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨k, a, b, d, c, rfl⟩ := hf
    obtain ⟨k', a', b', d', c', rfl⟩ := hg
    refine ⟨k + k', Fin.append a a', Fin.append b b', Fin.append d d', c + c', ?_⟩
    ext x
    simp only [Pi.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Rat.cast_add]
    ring
  | smul r f _ hf =>
    obtain ⟨k, a, b, d, c, rfl⟩ := hf
    refine ⟨k, a, b, r • d, r * c, ?_⟩
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Algebra.smul_def, mul_add,
      mul_sum, mul_assoc]
    rfl

 theorem linear_mem_of_rational (k : ℕ) (a : ι → ℝ) (ha : rationalPoint a) :
    (fun x => a ⬝ᵥ x) ∈ qreluNet ι k := by
  have he : ∀ i, ∃ q : ℚ, (q : ℝ) = a i := fun i =>
    (show (⊥ : Subfield ℝ) ≤ (Rat.castHom ℝ).fieldRange from bot_le) (ha i)
  choose q hq using he
  simpa only [hq] using linear_mem k q

end qreluNet
end
end AuthorReal

-- Source module: Solutions/RationalConstruction.lean

namespace AuthorReal
noncomputable section
open Finset Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rationalPoint_single (i : ι) (b : ℝ) (hb : b ∈ (⊥ : Subfield ℝ)) :
    rationalPoint (Pi.single i b) := by
  intro j
  by_cases h : i = j <;> simp [Pi.single_apply, h, hb]

theorem rationalPoint_indVec (S : Finset ι) : rationalPoint (indVec S) := by
  intro i
  simp only [indVec]
  split_ifs <;> simp

theorem rationalConstraint_homog {c : Constraint ι} (hc : rationalConstraint c) (v : ι) :
    rationalConstraint (c.homog v) := by
  refine ⟨fun i => ?_, hc.2⟩
  by_cases h : i = v
  · subst h
    simpa [Constraint.homog] using hc.2
  · simpa [Constraint.homog, h] using hc.1 i

theorem rational_pyrCons (v : ι) {cs : Finset (Constraint ι)}
    (hc : ∀ c ∈ cs, rationalConstraint c) : ∀ c ∈ pyrCons v cs, rationalConstraint c := by
  intro c hc'
  simp only [pyrCons, mem_insert, mem_image] at hc'
  rcases hc' with rfl | rfl | ⟨d, hd, rfl⟩
  · exact ⟨fun i => (⊥ : Subfield ℝ).neg_mem (rationalPoint_single v 1 (by simp) i), by simp⟩
  · exact ⟨rationalPoint_single v 1 (by simp), by simp⟩
  · exact rationalConstraint_homog (hc d hd) v

theorem rational_simplexCons : ∀ c ∈ (simplexCons : Finset (Constraint ι)), rationalConstraint c := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := mem_image.mp hc
  exact ⟨fun j => (⊥ : Subfield ℝ).neg_mem (rationalPoint_single i 1 (by simp) j), by simp⟩

theorem rational_tCons (C : Finset ι) (v : ι) : ∀ c ∈ tCons C v, rationalConstraint c := by
  intro c hc
  rcases mem_union.mp hc with hc | hc
  · exact rational_simplexCons c hc
  · obtain ⟨w, -, rfl⟩ := mem_image.mp hc
    exact ⟨fun j => (⊥ : Subfield ℝ).sub_mem
      (rationalPoint_single v 1 (by simp) j) (rationalPoint_single w 1 (by simp) j), by simp⟩

theorem rational_qCons (v : ι) (R : Finset ι) : ∀ c ∈ qCons v R, rationalConstraint c := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := mem_image.mp hc
  split_ifs <;> exact ⟨fun j => (⊥ : Subfield ℝ).neg_mem
    (rationalPoint_single i 1 (by simp) j), by simp⟩

theorem rational_boxCons (M pre : Finset ι) (l : List ι) :
    ∀ c ∈ boxCons M pre l, rationalConstraint c := by
  induction l generalizing pre with
  | nil => simp [boxCons]
  | cons y l ih =>
    intro c hc
    rw [boxCons] at hc
    rcases mem_union.mp hc with hc | hc
    · split_ifs at hc with hy
      · simp only [mem_insert, mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact ⟨fun i => (⊥ : Subfield ℝ).neg_mem (rationalPoint_indVec pre i), by simp⟩
        · exact ⟨rationalPoint_indVec pre, by simp⟩
      · simp only [mem_insert, mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact ⟨fun i => (⊥ : Subfield ℝ).neg_mem (rationalPoint_single y 1 (by simp) i), by simp⟩
        · exact ⟨rationalPoint_single y 1 (by simp), by simp⟩
    · exact ih _ c hc

theorem rational_boxConsL (M : Finset ι) (l : List ι) :
    ∀ c ∈ boxConsL M l, rationalConstraint c := by
  cases l with
  | nil => simp [boxConsL]
  | cons h t => exact rational_boxCons M {h} t

theorem rational_facetGen (v : ι) : ∀ c ∈ facetGen v, rationalConstraint c := by
  intro c hc
  simp only [facetGen, mem_union, mem_image] at hc
  rcases hc with ((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨S, -, rfl⟩) | ⟨S, -, rfl⟩
  · exact ⟨rationalPoint_single i 1 (by simp), by simp⟩
  · exact ⟨rationalPoint_single i 1 (by simp), by simp⟩
  · exact ⟨rationalPoint_indVec S, by simp⟩
  · exact ⟨rationalPoint_indVec S, by simp⟩

theorem rational_boxCoef (M pre : Finset ι) (l : List ι) (y : ι) :
    rationalPoint (boxCoef M pre l y) := by
  induction l generalizing pre with
  | nil => intro i; simp [boxCoef]
  | cons h t ih =>
    simp only [boxCoef]
    split_ifs
    · exact rationalPoint_indVec pre
    · exact rationalPoint_single h 1 (by simp)
    · exact ih _

theorem rational_boxA (v h : ι) (M : Finset ι) (t : List ι) (y : ι) :
    rationalPoint (boxA v h M t y) := by
  simp only [boxA]
  split_ifs
  · exact rationalPoint_single v 1 (by simp)
  · intro i; simp
  · exact rational_boxCoef M {h} t y

theorem q_supportFun_slabPoly_mem {a : ι → ι → ℝ} (ha : Function.Injective (Matrix.of a).mulVecLin)
    {lo hi : ι → ℝ} (hlh : lo ≤ hi) (hA : ∀ i, rationalPoint (a i))
    (hlo : rationalPoint lo) (hhi : rationalPoint hi) :
    supportFun (slabPoly a lo hi) ∈ qreluNet ι 1 := by
  have hw : ∀ y, rationalPoint ((slabEquiv ha).symm (Pi.single y 1)) := by
    intro y
    apply FieldLinear.unique_solution_mem (⊥ : Subfield ℝ) (Matrix.of a) hA
      (rationalPoint_single y 1 (by simp)) ha
    exact (slabEquiv ha).apply_symm_apply _
  have he : ∀ y, ∃ l h : ℚ, (l : ℝ) = lo y ∧ (h : ℝ) = hi y := by
    intro y
    exact ⟨Classical.choose ((show (⊥ : Subfield ℝ) ≤ (Rat.castHom ℝ).fieldRange from bot_le) (hlo y)),
      Classical.choose ((show (⊥ : Subfield ℝ) ≤ (Rat.castHom ℝ).fieldRange from bot_le) (hhi y)),
      Classical.choose_spec ((show (⊥ : Subfield ℝ) ≤ (Rat.castHom ℝ).fieldRange from bot_le) (hlo y)),
      Classical.choose_spec ((show (⊥ : Subfield ℝ) ≤ (Rat.castHom ℝ).fieldRange from bot_le) (hhi y))⟩
  choose l h hl hh using he
  have heq : supportFun (slabPoly a lo hi) = ∑ y,
      ((l y) • (fun x => (slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x) +
      (h y - l y) • (fun x => relu ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x))) := by
    ext x
    simp [supportFun_slabPoly ha hlh, Finset.sum_apply, Algebra.smul_def, hl, hh]
  rw [heq]
  exact sum_mem fun y _ => add_mem
    (Submodule.smul_mem _ _ (qreluNet.linear_mem_of_rational 1 _ (hw y)))
    (Submodule.smul_mem _ _ (qreluNet.relu_mem (qreluNet.linear_mem_of_rational 0 _ (hw y))))

theorem q_supportFun_box_mem {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (M : Finset ι) (hn : 2 ≤ Fintype.card ι) :
    supportFun (facetPoly v (boxConsL M l)) ∈ qreluNet ι 1 := by
  obtain ⟨h, t, rfl, hnd, hX⟩ := exists_cons_of_mem_orderings hl hn
  rw [boxConsL, facetPoly_boxCons_eq hnd hX M]
  apply q_supportFun_slabPoly_mem (injective_boxA hnd hX M) (boxLoA_le_boxHiA v h M)
    (rational_boxA v h M t)
  · intro i
    simp only [boxLoA, boxLo]
    split_ifs <;> simp
  · intro i
    simp only [boxHiA, boxHi]
    split_ifs <;> simp

end
end AuthorReal

-- Source module: Solutions/RationalSubdivision.lean

namespace AuthorReal
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem q_supportFun_pyr_qCons {R : Finset ι} (hR : R.Nonempty) {v : ι} (hv : v ∈ Rᶜ) :
    supportFun (pyr v (qCons v R)) = (#Rᶜ : ℚ) • supportFun (hpoly (tCons Rᶜ v)) +
      fun x => (-indVec (Rᶜ.erase v)) ⬝ᵥ x := by
  convert supportFun_pyr_qCons hR hv using 1
  ext x
  simp [Algebra.smul_def]

theorem q_subdivision {R : Finset ι} (hR : R.Nonempty) (hRu : R ≠ univ) :
    ∑ v ∈ Rᶜ, supportFun (pyr v (qCons v R)) - (Rᶜ.card : ℚ) • supportFun simplex ∈
      rationalMaxSpan ι (Fintype.card ι - 1) := by
  have hC : Rᶜ.Nonempty := (compl_ne_univ_iff_nonempty Rᶜ).1 (by rwa [compl_compl])
  have hn : 1 < Fintype.card ι := by
    obtain ⟨w, hw⟩ := hR
    obtain ⟨v, hv⟩ := hC
    exact Fintype.one_lt_card_iff.2 ⟨v, w, fun h ↦ mem_compl.1 hv (h ▸ hw)⟩
  set G : Finset (Constraint ι) := simplexCons ∪ Rᶜ.biUnion (tCons Rᶜ) with hG_def
  have hS : ∀ g ∈ (simplexCons : Finset (Constraint ι)), g.IsNonconst := by
    intro g hg
    obtain ⟨i, -, rfl⟩ := mem_image.1 hg
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hn i
    exact ⟨i, j, by simp [hj]⟩
  have hG : ∀ g ∈ G, g.IsNonconst := by
    intro g hg
    simp only [G, mem_union, mem_biUnion] at hg
    obtain hg | ⟨v, -, hg⟩ := hg
    · exact hS g hg
    simp only [tCons, mem_union, mem_image] at hg
    obtain hg | ⟨w, hw, rfl⟩ := hg
    · exact hS g hg
    · have hwv := ne_of_mem_erase hw
      exact ⟨v, w, by norm_num [hwv, hwv.symm]⟩
  have ht := q_transfer (κ := Option ι) (insertNone Rᶜ) (fun o ↦ o.elim (-1) fun _ ↦ 1)
    (fun o ↦ o.elim simplexCons (tCons Rᶜ)) G hG ?_ ?_ ?_ ?_
  rotate_left
  · intro o ho
    cases o with
    | none => exact subset_union_left
    | some v =>
      exact (subset_biUnion_of_mem (tCons Rᶜ) (some_mem_insertNone.1 ho)).trans
        subset_union_right
  · intro o _
    cases o with
    | none => exact isBounded_simplex
    | some v => exact isBounded_hpoly_tCons _ _
  · intro g hg
    rcases mem_union.mp hg with hg | hg
    · exact rational_simplexCons g hg
    · obtain ⟨v, -, hg⟩ := mem_biUnion.mp hg
      exact rational_tCons _ _ g hg
  · intro p _ hpG
    rw [sum_insertNone]
    simp only [Option.elim, Rat.cast_neg, Rat.cast_one]
    refine sum_indicator_tCons_sub_simplex hC fun v hv w hw hvw h ↦ ?_
    refine hpG ⟨Pi.single v 1 - Pi.single w 1, 0⟩ ?_ ?_
    · refine mem_union_right _ (mem_biUnion.2 ⟨v, hv, mem_union_right _ ?_⟩)
      exact mem_image.2 ⟨w, mem_erase.2 ⟨hvw.symm, hw⟩, rfl⟩
    · simp [sub_dotProduct, single_dotProduct, h]
  rw [sum_insertNone] at ht
  simp only [Option.elim] at ht
  have key : ∑ v ∈ Rᶜ, supportFun (pyr v (qCons v R)) - (Rᶜ.card : ℚ) • supportFun simplex =
      (#Rᶜ : ℚ) • ((-1 : ℚ) • supportFun simplex +
        ∑ v ∈ Rᶜ, (1 : ℚ) • supportFun (hpoly (tCons Rᶜ v))) +
      ∑ v ∈ Rᶜ, fun x ↦ (-indVec (Rᶜ.erase v)) ⬝ᵥ x := by
    rw [sum_congr rfl fun v hv ↦ q_supportFun_pyr_qCons hR hv, sum_add_distrib, ← smul_sum]
    simp only [one_smul, neg_one_smul, smul_add, smul_neg]
    abel
  rw [key]
  exact add_mem (Submodule.smul_mem _ _ ht)
    (sum_mem fun v _ ↦ linear_mem_rationalMaxSpan _
      (fun i => (⊥ : Subfield ℝ).neg_mem (rationalPoint_indVec _ i)) (by omega))

end
end AuthorReal

-- Source module: Solutions/RationalMain.lean

namespace AuthorReal
noncomputable section
open Finset

def qpsi (m s : ℕ) : ℚ := (-1) ^ (s - 1) * (s.factorial : ℚ) * ((m - s).factorial : ℚ)
@[simp] theorem qpsi_cast (m s : ℕ) : (qpsi m s : ℝ) = psi m s := by
  simp [qpsi, psi]

def qcoeffs (m : ℕ) (r : ℕ) : ℚ :=
  if r = 0 then 0 else qpsi m r - ∑ k : Fin r, qcoeffs m k * (r.choose k : ℚ)
decreasing_by exact k.isLt

@[simp] theorem qcoeffs_cast (m r : ℕ) : (qcoeffs m r : ℝ) = coeffs m r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [qcoeffs, coeffs]
    by_cases hr : r = 0
    · simp [hr]
    · simp [hr, ih]

 theorem qpsi_self_ne_zero (m : ℕ) : qpsi m m ≠ 0 := by
  simp [qpsi, Nat.factorial_ne_zero]

 theorem q_sum_filter_nonempty_coeffs {ι : Type*} {X : Finset ι} {m : ℕ} (hX : X.card = m)
    (hm : 1 ≤ m) : ∑ R ∈ X.powerset.filter (·.Nonempty), qcoeffs m R.card = qpsi m m := by
  apply Rat.cast_injective (α := ℝ)
  push_cast
  simpa only [qcoeffs_cast, qpsi_cast] using sum_filter_nonempty_coeffs hX hm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem q_vertex_identity (hn : 3 ≤ Fintype.card ι) (v : ι) :
    (∑ lM ∈ (orderings (univ.erase v)).sigma markings,
        (-1 : ℚ) ^ lM.2.card • supportFun (pyr v (boxConsL lM.2 lM.1))) -
      ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
        qcoeffs (Fintype.card ι - 1) R.card • supportFun (pyr v (qCons v R)) ∈
      rationalMaxSpan ι (Fintype.card ι - 1) := by
  set m := Fintype.card ι - 1
  set S₁ := (orderings (univ.erase v)).sigma markings
  set S₂ := (univ.erase v).powerset.filter (·.Nonempty)
  set Gf := facetGen v ∪ S₁.biUnion (fun lM ↦ boxConsL lM.2 lM.1) ∪ S₂.biUnion (qCons v)
  set coef : (Σ _ : List ι, Finset ι) ⊕ Finset ι → ℚ :=
    Sum.elim (fun lM ↦ (-1 : ℚ) ^ lM.2.card) (fun R ↦ -qcoeffs m R.card)
  set csf : (Σ _ : List ι, Finset ι) ⊕ Finset ι → Finset (Constraint ι) :=
    Sum.elim (fun lM ↦ boxConsL lM.2 lM.1) (fun R ↦ qCons v R)
  have hS₁ : ∀ lM ∈ S₁, lM.1 ∈ orderings (univ.erase v) := fun lM h ↦ (mem_sigma.1 h).1
  have hcsf : ∀ i ∈ S₁.disjSum S₂, csf i ⊆ Gf := by
    rintro (lM | R) h
    · simp only [inl_mem_disjSum] at h
      exact (subset_biUnion_of_mem (fun lM : Σ _ : List ι, Finset ι ↦ boxConsL lM.2 lM.1) h).trans
        (subset_union_right.trans subset_union_left)
    · simp only [inr_mem_disjSum] at h
      exact (subset_biUnion_of_mem (qCons v) h).trans subset_union_right
  have hfacet : ∀ q : ι → ℝ, ∑ j, q j = 1 → q v = 0 → (∀ g ∈ Gf, g.a ⬝ᵥ q ≠ g.b) →
      ∑ i ∈ S₁.disjSum S₂, (coef i : ℝ) * (facetPoly v (csf i)).indicator 1 q = 0 := by
    intro q hq hqv hqG
    have hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b := fun g hg ↦
      hqG g (mem_union_left _ (mem_union_left _ hg))
    rw [sum_disjSum]
    simp only [coef, csf, Sum.elim_inl, Sum.elim_inr, Rat.cast_neg, Rat.cast_pow, Rat.cast_one, qcoeffs_cast, neg_mul, sum_neg_distrib]
    rw [sum_sigma, thermostat hn hq hqv hgen, qcount _ hgen, ← sub_eq_add_neg, ← mul_sub,
      sub_eq_zero.2, mul_zero]
    set s := ((univ.erase v).filter fun i ↦ 0 < q i).card
    refine (sum_coeffs_mul_choose m ?_ ?_).symm
    · rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, filter_eq_empty_iff]
      intro h
      have : ∑ j, q j ≤ 0 := by
        rw [← add_sum_erase _ _ (mem_univ v), hqv, zero_add]
        exact sum_nonpos fun i hi ↦ not_lt.1 (h hi)
      linarith
    · exact (card_filter_le _ _).trans (by rw [card_erase_of_mem (mem_univ v), card_univ])
  have hT := q_transfer (S₁.disjSum S₂) coef (fun i ↦ pyrCons v (csf i)) (pyrCons v Gf)
    (isNonconst_of_mem_pyrCons (fun g hg ↦ by
      simp only [Gf, mem_union, mem_biUnion] at hg
      rcases hg with (hg | ⟨lM, hlM, hg⟩) | ⟨R, -, hg⟩
      · exact nonconst_facetGen hg hn
      · exact nonconst_boxConsL (hS₁ lM hlM) _ hg hn
      · exact nonconst_qCons hg hn) (by omega))
    (fun i hi ↦ pyrCons_mono (hcsf i hi))
    (by
      rintro (lM | R) h
      · simp only [inl_mem_disjSum] at h
        exact isBounded_pyr (box_nonempty (hS₁ lM h) _ (by omega)) (isBounded_box (hS₁ lM h) _
          (by omega))
      · exact isBounded_pyr (facetPoly_qCons_nonempty (by omega) R)
          (isBounded_facetPoly_qCons v R))
    (by
      intro g hg
      apply rational_pyrCons v _ g hg
      intro d hd
      simp only [Gf, mem_union, mem_biUnion] at hd
      rcases hd with (hd | ⟨lM, hlM, hd⟩) | ⟨R, -, hd⟩
      · exact rational_facetGen v d hd
      · exact rational_boxConsL lM.2 lM.1 d hd
      · exact rational_qCons v R d hd)
    (fun p hp hpG ↦ pyr_generic v _ (fun i => (coef i : ℝ)) csf Gf hfacet p hp hpG)
  rw [sum_disjSum] at hT
  simpa [coef, csf, sub_eq_add_neg, neg_smul, pyr] using hT

/-- The main step: for `card ι ≥ 3`, if maxima of `card ι - 1` linear forms are computable with
two hidden layers, then so is `max (x_i)_i`. -/
theorem q_supportFun_simplex_mem_reluNet (hn : 3 ≤ Fintype.card ι)
    (hL : rationalMaxSpan ι (Fintype.card ι - 1) ≤ qreluNet ι 2) :
    supportFun (simplex : Set (ι → ℝ)) ∈ qreluNet ι 2 := by
  set m := Fintype.card ι - 1
  set T := univ.powerset.filter fun R : Finset ι ↦ R.Nonempty ∧ R ≠ univ
  -- the paramid sum
  set P : (ι → ℝ) → ℝ := ∑ v, ∑ lM ∈ (orderings (univ.erase v)).sigma markings,
    (-1 : ℚ) ^ lM.2.card • supportFun (pyr v (boxConsL lM.2 lM.1))
  have hP : P ∈ qreluNet ι 2 := by
    refine Submodule.sum_mem _ fun v _ ↦ Submodule.sum_mem _ fun lM hlM ↦ ?_
    have hl := (mem_sigma.1 hlM).1
    refine Submodule.smul_mem _ _ ?_
    have : supportFun (pyr v (boxConsL lM.2 lM.1)) =
        fun x ↦ max ((Pi.single v 1 : ι → ℝ) ⬝ᵥ x)
          (supportFun (facetPoly v (boxConsL lM.2 lM.1)) x) := by
      ext x
      rw [supportFun_pyr (box_nonempty hl _ (by omega)) (isBounded_box hl _ (by omega)),
        single_dotProduct, one_mul]
    rw [this]
    exact qreluNet.max_mem (qreluNet.linear_mem_of_rational 1 _ (rationalPoint_single v 1 (by simp))) (q_supportFun_box_mem hl _ (by omega))
  -- swap the order of summation over pairs `(v, R)` with `v ∉ R`
  set K : ℚ := ∑ R ∈ T, qcoeffs m R.card * (Rᶜ.card : ℚ)
  have hK : K = Fintype.card ι * qpsi m m := by
    have := sum_sum_powerset_erase_comm fun (_ : ι) R ↦ qcoeffs m R.card
    simp only [sum_const, nsmul_eq_mul] at this
    rw [show K = ∑ R ∈ T, (Rᶜ.card : ℚ) * qcoeffs m R.card by simp [K, mul_comm], ← this]
    rw [sum_congr rfl fun v _ ↦ q_sum_filter_nonempty_coeffs (X := univ.erase v)
      (by rw [card_erase_of_mem (mem_univ v), card_univ]) (by omega)]
    simp
  have hKne : K ≠ 0 := by
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    rw [hK]
    exact mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (qpsi_self_ne_zero m)
  -- the combined identity modulo `maxSpan`
  have hQ : ∑ v, ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
      qcoeffs m R.card • supportFun (pyr v (qCons v R)) - K • supportFun simplex ∈ rationalMaxSpan ι m := by
    rw [sum_sum_powerset_erase_comm fun v R ↦ qcoeffs m R.card • supportFun (pyr v (qCons v R))]
    simp_rw [← smul_sum]
    have : K • supportFun (simplex : Set (ι → ℝ)) =
        ∑ R ∈ T, qcoeffs m R.card • ((Rᶜ.card : ℚ) • supportFun simplex) := by
      simp only [smul_smul, ← sum_smul, K]
    rw [this, ← sum_sub_distrib]
    refine Submodule.sum_mem _ fun R hR ↦ ?_
    simp only [mem_filter] at hR
    rw [← smul_sub]
    exact Submodule.smul_mem _ _ (q_subdivision hR.2.1 hR.2.2)
  have hV : P - ∑ v, ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
      qcoeffs m R.card • supportFun (pyr v (qCons v R)) ∈ rationalMaxSpan ι m := by
    rw [← sum_sub_distrib]
    exact Submodule.sum_mem _ fun v _ ↦ q_vertex_identity hn v
  have hsum : P - K • supportFun simplex ∈ rationalMaxSpan ι m := by
    have := Submodule.add_mem _ hV hQ
    rwa [sub_add_sub_cancel] at this
  have : supportFun (simplex : Set (ι → ℝ)) = K⁻¹ • (P - (P - K • supportFun simplex)) := by
    rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hKne, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hP (hL hsum))

omit [DecidableEq ι] in
/-- Maxima of at most `n` linear forms are computable with two hidden layers once
`max (x₁, …, xₙ)` is. -/
theorem q_maxSpan_le_reluNet {n : ℕ} [NeZero n]
    (h : (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∈ qreluNet (Fin n) 2) :
    rationalMaxSpan ι n ≤ qreluNet ι 2 := by
  classical
  refine Submodule.span_le.2 ?_
  rintro f ⟨W, hW, hcard, hR, rfl⟩
  obtain ⟨w₀, hw₀⟩ := hW
  -- enumerate `W` by `Fin n`, repeating `w₀`
  let e : Fin n → ι → ℝ := fun k ↦
    if hk : (k : ℕ) < W.card then (W.equivFin.symm ⟨k, hk⟩ : ι → ℝ) else w₀
  have he : ∀ k, e k ∈ W := by
    intro k
    simp only [e]
    split_ifs
    · exact Finset.coe_mem _
    · exact hw₀
  have hsurj : ∀ w ∈ W, ∃ k, e k = w := by
    intro w hw
    refine ⟨⟨W.equivFin ⟨w, hw⟩, (W.equivFin ⟨w, hw⟩).isLt.trans_le hcard⟩, ?_⟩
    simp [e]
  have heR : ∀ k j, e k j ∈ (⊥ : Subfield ℝ) := fun k j => hR (e k) (he k) j
  have heQ : ∀ k j, ∃ q : ℚ, (q : ℝ) = e k j := fun k j =>
    (show (⊥ : Subfield ℝ) ≤ (Rat.castHom ℝ).fieldRange from bot_le) (heR k j)
  choose Q hQ using heQ
  let A : (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin (Matrix.of e)
  have hA : maxLin W = (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∘ A := by
    ext x
    have hWne : W.Nonempty := ⟨w₀, hw₀⟩
    simp only [maxLin, dif_pos hWne, Function.comp_apply, A, Matrix.mulVecLin_apply]
    have hmv : ∀ k, (Matrix.of e).mulVec x k = e k ⬝ᵥ x := fun k ↦ rfl
    simp only [hmv]
    apply le_antisymm
    · refine sup'_le _ _ fun w hw ↦ ?_
      obtain ⟨k, rfl⟩ := hsurj w hw
      exact le_sup'_of_le _ (mem_univ k) le_rfl
    · exact sup'_le _ _ fun k _ ↦ le_sup' (· ⬝ᵥ x) (he k)
  rw [hA]
  have hmatrix : (Matrix.of Q).map (Rat.castHom ℝ) = Matrix.of e := by
    ext k i
    exact hQ k i
  have hcomp := qreluNet.comp_matrix (Matrix.of Q) h
  rw [hmatrix] at hcomp
  exact hcomp

theorem q_max_mem_reluNet_succ (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ ↦ univ.sup' univ_nonempty x) ∈ qreluNet (Fin (n + 1)) 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | _ | n
  · have : (fun x : Fin 1 → ℝ ↦ univ.sup' univ_nonempty x) =
        fun x ↦ (Pi.single 0 1 : Fin 1 → ℝ) ⬝ᵥ x := by
      ext x
      simp [single_dotProduct, univ_unique]
    rw [this]
    exact qreluNet.linear_mem_of_rational 2 _ (rationalPoint_single 0 1 (by simp))
  · have : (fun x : Fin 2 → ℝ ↦ univ.sup' univ_nonempty x) =
        fun x ↦ max ((Pi.single 0 1 : Fin 2 → ℝ) ⬝ᵥ x) ((Pi.single 1 1 : Fin 2 → ℝ) ⬝ᵥ x) := by
      ext x
      simp only [single_dotProduct, one_mul]
      apply le_antisymm
      · refine sup'_le _ _ fun k _ ↦ ?_
        fin_cases k
        exacts [le_max_left _ _, le_max_right _ _]
      · exact max_le (le_sup' x (mem_univ 0)) (le_sup' x (mem_univ 1))
    rw [this]
    exact qreluNet.max_mem (qreluNet.linear_mem_of_rational 1 _ (rationalPoint_single 0 1 (by simp)))
      (qreluNet.linear_mem_of_rational 1 _ (rationalPoint_single 1 1 (by simp)))
  · have hL : rationalMaxSpan (Fin (n + 3)) (Fintype.card (Fin (n + 3)) - 1) ≤ qreluNet (Fin (n + 3)) 2 := by
      rw [Fintype.card_fin]
      exact q_maxSpan_le_reluNet (n := n + 2) (ih (n + 1) (by omega))
    have := q_supportFun_simplex_mem_reluNet (by simp) hL
    rwa [show supportFun (simplex : Set (Fin (n + 3) → ℝ)) = fun x ↦ univ.sup' univ_nonempty x
      from funext supportFun_simplex] at this

/-- **Two hidden ReLU layers compute the maximum**: `MAXₙ ∈ ReLU_{n,2}`. -/
theorem q_max_mem_reluNet (n : ℕ) [NeZero n] :
    (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∈ qreluNet (Fin n) 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact q_max_mem_reluNet_succ k


end
end AuthorReal

-- Source module: Solutions/RationalEval.lean

namespace AuthorReal
noncomputable section
open Finset
open TwoReLULayers.DepthCollapse

 theorem qreluNet_eval {n : ℕ} (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ qreluNet (Fin n) 2) :
    (fun x : E n => f x.ofLp) ∈ ReLU2 (⊥ : Subfield ℝ) n := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨g, hg, rfl⟩
    · refine ⟨⟨0, 0, Fin.elim0, Fin.elim0, ⟨Fin.elim0, 1⟩⟩, fun x => ?_⟩
      change (1 : ℝ) = (1 : ℝ) + ∑ i : Fin 0, _
      simp
    · obtain ⟨k, a, b, d, c, rfl⟩ := qreluNet.exists_sum hg
      refine ⟨⟨k, 1, (fun j => ⟨fun i => (a j i : (⊥ : Subfield ℝ)), (b j : (⊥ : Subfield ℝ))⟩),
        (fun _ => ⟨fun j => (d j : (⊥ : Subfield ℝ)), (c : (⊥ : Subfield ℝ))⟩),
        ⟨fun _ => 1, 0⟩⟩, fun x => ?_⟩
      dsimp only [Network2.eval, AffineScalar.eval, affineEval, TwoReLULayers.DepthCollapse.relu]
      simp [AuthorReal.relu, dotProduct, max_comm, add_comm]
  | zero =>
    refine ⟨⟨0, 0, Fin.elim0, Fin.elim0, ⟨Fin.elim0, 0⟩⟩, fun x => ?_⟩
    change (0 : ℝ) = (0 : ℝ) + ∑ i : Fin 0, _
    simp
  | add f g _ _ hf hg =>
    have h := network_linear_combination hn (⊥ : Subfield ℝ)
      (![1, 1] : Fin 2 → (⊥ : Subfield ℝ))
      (![fun x : E n => f x.ofLp, fun x : E n => g x.ofLp])
      (by intro i; fin_cases i <;> assumption)
    simpa [Fin.sum_univ_two] using h
  | smul r f _ hf =>
    have h := network_linear_combination hn (⊥ : Subfield ℝ)
      (fun _ : Fin 1 => (r : (⊥ : Subfield ℝ)))
      (fun _ (x : E n) => f x.ofLp) (fun _ => hf)
    convert h using 1
    ext x
    simp [Fin.sum_univ_one, Algebra.smul_def]

end
end AuthorReal

-- Source module: Solutions/MaxRational.lean

open TwoReLULayers.DepthCollapse
open Finset

theorem solution {n : ℕ} (hn : 1 ≤ n) :
    (maxCoord : E n → ℝ) ∈ ReLU2 (⊥ : Subfield ℝ) n := by
  letI : NeZero n := ⟨by omega⟩
  have h := AuthorReal.qreluNet_eval hn (AuthorReal.q_max_mem_reluNet n)
  have heq : (maxCoord : E n → ℝ) =
      (fun x : E n => Finset.univ.sup' Finset.univ_nonempty (fun i => x i)) := by
    ext x
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      exact le_sup' (fun i => x i) (mem_univ i)
    · apply sup'_le
      intro i _
      exact le_csSup (Set.finite_range (fun i : Fin n => x i)).bddAbove ⟨i, rfl⟩
  rw [heq]
  exact h
