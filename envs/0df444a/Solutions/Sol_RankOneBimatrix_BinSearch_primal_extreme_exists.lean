-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.primal_extreme_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:15:26.823938+00:00
-- url     : https://prove2.me/submissions/3be350f3-5457-4d58-b33b-384ca7cb7416

import Mathlib
import Theorems.Thm_LinearOptimization_polyhedron_extreme_point_existence
import Theorems.Thm_LinearOptimization_lp_attains_or_unbounded
import Theorems.Thm_LinearOptimization_lp_optimal_extreme_point
import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

open Matrix LinearOptimization

namespace R1BSLP

/-- Linear programming over a line-free polyhedron `{x | ∀ i, c i ≤ φ i x}` in a
finite-dimensional real space: a linear objective bounded below attains its
minimum at an extreme point. -/
theorem exists_extreme_min {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (φ : ι → E →ₗ[ℝ] ℝ) (c : ι → ℝ) (f : E →ₗ[ℝ] ℝ)
    (hne : {x | ∀ i, c i ≤ φ i x}.Nonempty)
    (hline : ∀ x ∈ {x | ∀ i, c i ≤ φ i x}, ∀ d : E,
      (∀ t : ℝ, x + t • d ∈ {x | ∀ i, c i ≤ φ i x}) → d = 0)
    (B : ℝ) (hbdd : ∀ x ∈ {x | ∀ i, c i ≤ φ i x}, B ≤ f x) :
    ∃ x ∈ Set.extremePoints ℝ {x | ∀ i, c i ≤ φ i x},
      ∀ y ∈ {x | ∀ i, c i ≤ φ i x}, f x ≤ f y := by
  classical
  set S := {x | ∀ i, c i ≤ φ i x} with hS
  set bE := Module.finBasis ℝ E
  set e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := bE.equivFun
  set σ := Fintype.equivFin ι
  let G : Matrix (Fin (Fintype.card ι)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun k j => φ (σ.symm k) (bE j)
  let h : Fin (Fintype.card ι) → ℝ := fun k => c (σ.symm k)
  let cv : Fin (Module.finrank ℝ E) → ℝ := fun j => f (bE j)
  have hlin : ∀ (g : E →ₗ[ℝ] ℝ) (z : Fin (Module.finrank ℝ E) → ℝ),
      g (e.symm z) = ∑ j, g (bE j) * z j := by
    intro g z
    simp only [e, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hG : ∀ z k, (G *ᵥ z) k = φ (σ.symm k) (e.symm z) := by
    intro z k
    rw [hlin]; rfl
  have hc : ∀ z, cv ⬝ᵥ z = f (e.symm z) := by
    intro z; rw [hlin]; rfl
  have hmem : ∀ z, z ∈ polyhedron G h ↔ e.symm z ∈ S := by
    intro z
    simp only [polyhedron, Set.mem_setOf_eq, hS]
    constructor
    · intro hz i
      have := hz (σ i)
      simp only [Pi.le_def] at hz
      have h1 := hz (σ i)
      rw [hG] at h1
      simpa [h] using h1
    · intro hz k
      rw [hG]
      exact hz _
  have himg : e '' S = polyhedron G h := by
    ext z
    rw [hmem]
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hz; exact ⟨e.symm z, hz, by simp⟩
  have hpne : (polyhedron G h).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, (hmem _).2 (by simpa using hx)⟩
  have hnl : ¬ ContainsLine (polyhedron G h) := by
    rintro ⟨z, hz, d, hd, hall⟩
    have := hline (e.symm z) ((hmem z).1 hz) (e.symm d) (fun t => by
      have := (hmem _).1 (hall t)
      simpa [map_add, map_smul] using this)
    exact hd (by simpa using congrArg e this)
  have hext : (Set.extremePoints ℝ (polyhedron G h)).Nonempty :=
    ((polyhedron_extreme_point_existence G h hpne).out 0 1).2 hnl
  have hopt : ∃ x, IsLpOptimal cv (polyhedron G h) x := by
    rcases lp_attains_or_unbounded G h cv hpne with hb | ho
    · exfalso
      have hle : ((B : ℝ) : EReal) ≤ lpValue cv (polyhedron G h) := by
        unfold lpValue
        refine le_iInf₂ fun z hz => ?_
        rw [hc]
        exact_mod_cast hbdd _ ((hmem z).1 hz)
      rw [hb] at hle
      exact EReal.coe_ne_bot B (le_bot_iff.1 hle)
    · exact ho
  obtain ⟨z, hzext, hzopt⟩ := lp_optimal_extreme_point G h cv hext hopt
  rw [← himg, ← image_extremePoints] at hzext
  obtain ⟨x, hx, rfl⟩ := hzext
  refine ⟨x, hx, fun y hy => ?_⟩
  have h1 := hzopt.2 (e y) (himg ▸ ⟨y, hy, rfl⟩)
  rw [hc, hc] at h1
  simpa using h1


/-- Variant with equality constraints and an arbitrary presentation of the set. -/
theorem exists_extreme_min_eq {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (φ : ι → E →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (ψ : κ → E →ₗ[ℝ] ℝ) (d : κ → ℝ) (f : E →ₗ[ℝ] ℝ) (S : Set E)
    (hS : S = {x | (∀ i, c i ≤ φ i x) ∧ ∀ k, ψ k x = d k})
    (hne : S.Nonempty)
    (hline : ∀ x ∈ S, ∀ v : E, (∀ t : ℝ, x + t • v ∈ S) → v = 0)
    (B : ℝ) (hbdd : ∀ x ∈ S, B ≤ f x) :
    ∃ x ∈ Set.extremePoints ℝ S, ∀ y ∈ S, f x ≤ f y := by
  let φ' : ι ⊕ κ ⊕ κ → E →ₗ[ℝ] ℝ := Sum.elim φ (Sum.elim ψ (fun k => -ψ k))
  let c' : ι ⊕ κ ⊕ κ → ℝ := Sum.elim c (Sum.elim d (fun k => -d k))
  have hS' : S = {x | ∀ j, c' j ≤ φ' j x} := by
    rw [hS]
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ j
      rcases j with i | k | k
      · exact h1 i
      · exact (h2 k).ge
      · simp only [φ', c', Sum.elim_inr, LinearMap.neg_apply, neg_le_neg_iff]
        exact (h2 k).le
    · intro h
      refine ⟨fun i => h (Sum.inl i), fun k => le_antisymm ?_ (h (Sum.inr (Sum.inl k)))⟩
      have := h (Sum.inr (Sum.inr k))
      simp only [φ', c', Sum.elim_inr, LinearMap.neg_apply, neg_le_neg_iff] at this
      exact this
  rw [hS'] at hne hline hbdd ⊢
  exact exists_extreme_min φ' c' f hne hline B hbdd

/-- Helper: a real affine function `c + t δ` that is nonnegative for all `t` is constant. -/
lemma slope_zero_of_nonneg (c δ : ℝ) (h : ∀ t : ℝ, 0 ≤ c + t * δ) : δ = 0 := by
  by_contra hδ
  have := h (-(|c| + 1) / δ)
  rw [div_mul_cancel₀ _ hδ] at this
  have := le_abs_self c
  linarith

lemma slope_zero_of_le (c δ U : ℝ) (h : ∀ t : ℝ, c + t * δ ≤ U) : δ = 0 := by
  have := slope_zero_of_nonneg (U - c) (-δ) (fun t => by have := h t; linarith)
  linarith

end R1BSLP


open Matrix RankOneBimatrix.BinSearch

namespace R1BSLP

variable {m n : ℕ}

/-- Coordinate linear maps on `PPoint m n`. -/
def px (i : Fin m) : PPoint m n →ₗ[ℝ] ℝ where
  toFun p := p.1 i
  map_add' p q := rfl
  map_smul' r p := rfl

def pv : PPoint m n →ₗ[ℝ] ℝ where
  toFun p := p.2.1
  map_add' p q := rfl
  map_smul' r p := rfl

def ps (j : Fin n) : PPoint m n →ₗ[ℝ] ℝ where
  toFun p := p.2.2 j
  map_add' p q := rfl
  map_smul' r p := rfl

def psum : PPoint m n →ₗ[ℝ] ℝ where
  toFun p := ∑ i, p.1 i
  map_add' p q := by simp [Finset.sum_add_distrib]
  map_smul' r p := by simp [Finset.mul_sum]

def peq (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : PPoint m n →ₗ[ℝ] ℝ where
  toFun p := (A.transpose *ᵥ p.1) j + p.2.1 - p.2.2 j
  map_add' p q := by simp [mulVec_add]; ring
  map_smul' r p := by simp [mulVec_smul]; ring

lemma PFeas_eq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    PFeas A b lam = {p | (∀ k : Fin m ⊕ Fin n,
        (0 : ℝ) ≤ (Sum.elim (fun i => px i) (fun j => ps j) k : PPoint m n →ₗ[ℝ] ℝ) p) ∧
      ∀ k : Option (Fin n),
        (Option.elim k psum (fun j => peq A j) : PPoint m n →ₗ[ℝ] ℝ) p =
          Option.elim k 1 (fun j => b j * lam)} := by
  ext p
  simp only [PFeas, Set.mem_setOf_eq, Mixed, stdSimplex]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, hs0, heq⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rcases k with i | j
      · exact hx0 i
      · exact hs0 j
    · rcases k with _ | j
      · exact hx1
      · exact heq j
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun i => h1 (Sum.inl i), h2 none⟩, fun j => h1 (Sum.inr j), fun j => h2 (some j)⟩

theorem primal_extreme (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    (PExtreme A b lam).Nonempty := by
  classical
  have j0 : Fin n := ⟨0, hn⟩
  have i0 : Fin m := ⟨0, hm⟩
  -- nonempty
  have hne : (PFeas A b lam).Nonempty := by
    let x : Fin m → ℝ := Pi.single i0 1
    let v : ℝ := ∑ j, |b j * lam - (A.transpose *ᵥ x) j|
    refine ⟨(x, v, fun j => (A.transpose *ᵥ x) j + v - b j * lam), ⟨?_, ?_, ?_⟩⟩
    · exact single_mem_stdSimplex ℝ i0
    · intro j
      have h1 : |b j * lam - (A.transpose *ᵥ x) j| ≤ v :=
        Finset.single_le_sum (f := fun j => |b j * lam - (A.transpose *ᵥ x) j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have h2 := le_abs_self (b j * lam - (A.transpose *ᵥ x) j)
      simp only
      linarith
    · intro j; simp only; ring
  -- line free
  have hline : ∀ p ∈ PFeas A b lam, ∀ d : PPoint m n,
      (∀ t : ℝ, p + t • d ∈ PFeas A b lam) → d = 0 := by
    intro p hp d hd
    have hdx : ∀ i, d.1 i = 0 := fun i => slope_zero_of_nonneg (p.1 i) (d.1 i) (fun t => by
      have := (hd t).1.1 i
      simpa [mul_comm] using this)
    have hds : ∀ j, d.2.2 j = 0 := fun j => slope_zero_of_nonneg (p.2.2 j) (d.2.2 j) (fun t => by
      have := (hd t).2.1 j
      simpa [mul_comm] using this)
    have hdx' : d.1 = 0 := funext hdx
    have hds' : d.2.2 = 0 := funext hds
    have h1 := (hd 1).2.2 j0
    have h0 := hp.2.2 j0
    simp only [one_smul, Prod.fst_add, Prod.snd_add, hdx', add_zero, hds', Pi.add_apply,
      Pi.zero_apply] at h1
    have hdv : d.2.1 = 0 := by linarith
    ext i
    · simp [hdx]
    · simp [hdv]
    · simp [hds]
  -- bounded below
  have hbdd : ∀ p ∈ PFeas A b lam, b j0 * lam - ∑ i, |A i j0| ≤ (pv : PPoint m n →ₗ[ℝ] ℝ) p := by
    intro p hp
    obtain ⟨⟨hx0, hx1⟩, hs0, heq⟩ := hp
    have hA : (A.transpose *ᵥ p.1) j0 ≤ ∑ i, |A i j0| := by
      simp only [mulVec, dotProduct, transpose_apply]
      refine Finset.sum_le_sum fun i _ => ?_
      have hxi : p.1 i ≤ 1 := by
        have := Finset.single_le_sum (f := p.1) (fun i _ => hx0 i) (Finset.mem_univ i)
        linarith
      calc A i j0 * p.1 i ≤ |A i j0| * p.1 i := mul_le_mul_of_nonneg_right (le_abs_self _) (hx0 i)
        _ ≤ |A i j0| * 1 := mul_le_mul_of_nonneg_left hxi (abs_nonneg _)
        _ = |A i j0| := mul_one _
    have := heq j0
    have := hs0 j0
    show _ ≤ p.2.1
    linarith
  obtain ⟨p, hpext, hpmin⟩ := exists_extreme_min_eq _ _ _ _ pv (PFeas A b lam)
    (PFeas_eq A b lam) hne hline _ hbdd
  refine ⟨p, ⟨extremePoints_subset hpext, ⟨p, extremePoints_subset hpext, rfl⟩,
    ?_⟩, hpext⟩
  rintro _ ⟨q, hq, rfl⟩
  exact hpmin q hq

end R1BSLP


open RankOneBimatrix.BinSearch in
theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    (PExtreme A b lam).Nonempty := R1BSLP.primal_extreme hm hn A b lam
