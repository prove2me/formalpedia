-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.dual_extreme_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:15:27.518057+00:00
-- url     : https://prove2.me/submissions/db94ba1a-fd98-433a-86d2-e3de87f44764

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

def dy (j : Fin n) : DPoint n →ₗ[ℝ] ℝ where
  toFun p := p.1 j
  map_add' p q := rfl
  map_smul' r p := rfl

def dsum : DPoint n →ₗ[ℝ] ℝ where
  toFun p := ∑ j, p.1 j
  map_add' p q := by simp [Finset.sum_add_distrib]
  map_smul' r p := by simp [Finset.mul_sum]

def drow (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : DPoint n →ₗ[ℝ] ℝ where
  toFun p := -((A *ᵥ p.1) i + p.2)
  map_add' p q := by simp [mulVec_add]; ring
  map_smul' r p := by simp [mulVec_smul]; ring

def dneg (b : Fin n → ℝ) (lam : ℝ) : DPoint n →ₗ[ℝ] ℝ where
  toFun p := -(lam * (b ⬝ᵥ p.1) + p.2)
  map_add' p q := by simp [dotProduct_add]; ring
  map_smul' r p := by simp [dotProduct_smul]; ring

lemma DSet_eq (A : Matrix (Fin m) (Fin n) ℝ) :
    DSet A = {p | (∀ k : Fin n ⊕ Fin m,
        (0 : ℝ) ≤ (Sum.elim (fun j => dy j) (fun i => drow A i) k : DPoint n →ₗ[ℝ] ℝ) p) ∧
      ∀ _k : Unit, (dsum : DPoint n →ₗ[ℝ] ℝ) p = 1} := by
  ext p
  simp only [DSet, Set.mem_setOf_eq, Mixed, stdSimplex]
  constructor
  · rintro ⟨⟨hy0, hy1⟩, hD⟩
    refine ⟨fun k => ?_, fun _ => hy1⟩
    rcases k with j | i
    · exact hy0 j
    · show 0 ≤ -((A *ᵥ p.1) i + p.2)
      linarith [hD i]
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun j => h1 (Sum.inl j), h2 ()⟩, fun i => ?_⟩
    have := h1 (Sum.inr i)
    change 0 ≤ -((A *ᵥ p.1) i + p.2) at this
    linarith

theorem dual_extreme (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    (DExtreme A b lam).Nonempty := by
  classical
  have j0 : Fin n := ⟨0, hn⟩
  have i0 : Fin m := ⟨0, hm⟩
  have hne : (DSet A).Nonempty := by
    let y : Fin n → ℝ := Pi.single j0 1
    refine ⟨(y, -∑ i, |(A *ᵥ y) i|), single_mem_stdSimplex ℝ j0, fun i => ?_⟩
    have h1 : |(A *ᵥ y) i| ≤ ∑ i, |(A *ᵥ y) i| :=
      Finset.single_le_sum (f := fun i => |(A *ᵥ y) i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    have h2 := le_abs_self ((A *ᵥ y) i)
    simp only
    linarith
  have hline : ∀ p ∈ DSet A, ∀ d : DPoint n, (∀ t : ℝ, p + t • d ∈ DSet A) → d = 0 := by
    intro p hp d hd
    have hdy : ∀ j, d.1 j = 0 := fun j => slope_zero_of_nonneg (p.1 j) (d.1 j) (fun t => by
      have := (hd t).1.1 j
      simpa [mul_comm] using this)
    have hdy' : d.1 = 0 := funext hdy
    have hdt : d.2 = 0 := by
      refine slope_zero_of_le (p.2) (d.2) (-(A *ᵥ p.1) i0) (fun t => ?_)
      have := (hd t).2 i0
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hdy', smul_zero,
        add_zero, smul_eq_mul] at this
      linarith
    ext j
    · simp [hdy]
    · simp [hdt]
  have hbdd : ∀ p ∈ DSet A, -(|lam| * ∑ j, |b j| + ∑ j, |A i0 j|) ≤
      (dneg b lam : DPoint n →ₗ[ℝ] ℝ) p := by
    intro p hp
    obtain ⟨⟨hy0, hy1⟩, hD⟩ := hp
    have hyj : ∀ j, p.1 j ≤ 1 := fun j => by
      have := Finset.single_le_sum (f := p.1) (fun j _ => hy0 j) (Finset.mem_univ j)
      linarith
    have hb : lam * (b ⬝ᵥ p.1) ≤ |lam| * ∑ j, |b j| := by
      have h1 : |b ⬝ᵥ p.1| ≤ ∑ j, |b j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (hy0 j)]
        calc |b j| * p.1 j ≤ |b j| * 1 := mul_le_mul_of_nonneg_left (hyj j) (abs_nonneg _)
          _ = |b j| := mul_one _
      calc lam * (b ⬝ᵥ p.1) ≤ |lam * (b ⬝ᵥ p.1)| := le_abs_self _
        _ = |lam| * |b ⬝ᵥ p.1| := abs_mul _ _
        _ ≤ |lam| * ∑ j, |b j| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have hAy : -(∑ j, |A i0 j|) ≤ (A *ᵥ p.1) i0 := by
      have : |(A *ᵥ p.1) i0| ≤ ∑ j, |A i0 j| := by
        simp only [mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (hy0 j)]
        calc |A i0 j| * p.1 j ≤ |A i0 j| * 1 := mul_le_mul_of_nonneg_left (hyj j) (abs_nonneg _)
          _ = |A i0 j| := mul_one _
      linarith [neg_abs_le ((A *ᵥ p.1) i0)]
    have := hD i0
    show _ ≤ -(lam * (b ⬝ᵥ p.1) + p.2)
    linarith
  obtain ⟨p, hpext, hpmin⟩ := exists_extreme_min_eq _ _ _ _ (dneg b lam) (DSet A)
    (DSet_eq A) hne hline _ hbdd
  refine ⟨p, ⟨extremePoints_subset hpext, ⟨p, extremePoints_subset hpext, rfl⟩, ?_⟩, hpext⟩
  rintro _ ⟨q, hq, rfl⟩
  have := hpmin q hq
  change -(lam * (b ⬝ᵥ p.1) + p.2) ≤ -(lam * (b ⬝ᵥ q.1) + q.2) at this
  show lam * (b ⬝ᵥ q.1) + q.2 ≤ lam * (b ⬝ᵥ p.1) + p.2
  linarith

end R1BSLP


open RankOneBimatrix.BinSearch in
theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    (DExtreme A b lam).Nonempty := R1BSLP.dual_extreme hm hn A b lam
