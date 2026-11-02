-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.br_extreme_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:15:29.042619+00:00
-- url     : https://prove2.me/submissions/e9fd4d5d-1e2c-4ba9-9041-64d49953d6a8

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

def ql : PolyPoint m n →ₗ[ℝ] ℝ where
  toFun p := p.1
  map_add' p q := rfl
  map_smul' r p := rfl

def qx (i : Fin m) : PolyPoint m n →ₗ[ℝ] ℝ where
  toFun p := p.2.1 i
  map_add' p q := rfl
  map_smul' r p := rfl

def qs (j : Fin n) : PolyPoint m n →ₗ[ℝ] ℝ where
  toFun p := p.2.2.2 j
  map_add' p q := rfl
  map_smul' r p := rfl

def qsum : PolyPoint m n →ₗ[ℝ] ℝ where
  toFun p := ∑ i, p.2.1 i
  map_add' p q := by simp [Finset.sum_add_distrib]
  map_smul' r p := by simp [Finset.mul_sum]

def qdot (a : Fin m → ℝ) : PolyPoint m n →ₗ[ℝ] ℝ where
  toFun p := p.2.1 ⬝ᵥ a
  map_add' p q := by simp [add_dotProduct]
  map_smul' r p := by simp [smul_dotProduct]

def qeq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (j : Fin n) :
    PolyPoint m n →ₗ[ℝ] ℝ where
  toFun p := (A.transpose *ᵥ p.2.1) j + p.2.2.1 - p.2.2.2 j - b j * p.1
  map_add' p q := by simp [mulVec_add]; ring
  map_smul' r p := by simp [mulVec_smul]; ring

/-- Inequality functionals of `P`: `x ≥ 0`, `s ≥ 0`. -/
def faceIneq : Fin m ⊕ Fin n → PolyPoint m n →ₗ[ℝ] ℝ :=
  Sum.elim (fun i => qx i) (fun j => qs j)

/-- Equality functionals of `P(M,N)`. -/
def faceEq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (M : Finset (Fin m))
    (N : Finset (Fin n)) : Option (Fin n) ⊕ (M ⊕ N) → PolyPoint m n →ₗ[ℝ] ℝ :=
  Sum.elim (fun k => Option.elim k qsum (fun j => qeq A b j))
    (Sum.elim (fun i => qx i.1) (fun j => qs j.1))

def faceEqRhs (M : Finset (Fin m)) (N : Finset (Fin n)) : Option (Fin n) ⊕ (M ⊕ N) → ℝ :=
  Sum.elim (fun k => Option.elim k 1 (fun _ => 0)) (fun _ => 0)

lemma mem_PFace_iff (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (M : Finset (Fin m))
    (N : Finset (Fin n)) (p : PolyPoint m n) :
    p ∈ PFace A b M N ↔ (∀ k, (0 : ℝ) ≤ faceIneq k p) ∧
      ∀ k, faceEq A b M N k p = faceEqRhs M N k := by
  simp only [PFace, PPoly, PFeas, Set.mem_setOf_eq, Mixed, stdSimplex]
  constructor
  · rintro ⟨⟨⟨hx0, hx1⟩, hs0, heq⟩, hM, hN⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rcases k with i | j
      · exact hx0 i
      · exact hs0 j
    · rcases k with (_ | j) | (i | j)
      · exact hx1
      · show (A.transpose *ᵥ p.2.1) j + p.2.2.1 - p.2.2.2 j - b j * p.1 = 0
        linarith [heq j]
      · exact hM i.1 i.2
      · exact hN j.1 j.2
  · rintro ⟨h1, h2⟩
    refine ⟨⟨⟨fun i => h1 (Sum.inl i), h2 (Sum.inl none)⟩, fun j => h1 (Sum.inr j),
      fun j => ?_⟩, fun i hi => h2 (Sum.inr (Sum.inl ⟨i, hi⟩)),
      fun j hj => h2 (Sum.inr (Sum.inr ⟨j, hj⟩))⟩
    have := h2 (Sum.inl (some j))
    change (A.transpose *ᵥ p.2.1) j + p.2.2.1 - p.2.2.2 j - b j * p.1 = 0 at this
    linarith

/-- A line in `P(M,N)` with no `λ`-component is trivial. -/
lemma face_line (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (p d : PolyPoint m n)
    (hd : ∀ t : ℝ, p + t • d ∈ PFace A b M N) (hl : d.1 = 0) : d = 0 := by
  have j0 : Fin n := ⟨0, hn⟩
  have hdx : ∀ i, d.2.1 i = 0 := fun i => slope_zero_of_nonneg (p.2.1 i) (d.2.1 i) (fun t => by
    have := (hd t).1.1.1 i
    simpa [mul_comm] using this)
  have hds : ∀ j, d.2.2.2 j = 0 := fun j => slope_zero_of_nonneg (p.2.2.2 j) (d.2.2.2 j)
    (fun t => by
      have := (hd t).1.2.1 j
      simpa [mul_comm] using this)
  have hdx' : d.2.1 = 0 := funext hdx
  have hds' : d.2.2.2 = 0 := funext hds
  have h1 := (hd 1).1.2.2 j0
  have h0 := (hd 0).1.2.2 j0
  simp only [one_smul, zero_smul, add_zero, Prod.fst_add, Prod.snd_add, hdx', hds', hl,
    Pi.add_apply, Pi.zero_apply] at h1 h0
  have hdv : d.2.2.1 = 0 := by linarith
  ext
  · simp [hl]
  · simp [hdx]
  · simp [hdv]
  · simp [hds]

theorem pmax_pmin (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℝ) :
    ((PmaxFeas A a b M N lam').Nonempty →
      (PmaxExtreme A a b M N lam').Nonempty) ∧
    ((PminFeas A a b M N lam').Nonempty →
      (PminExtreme A a b M N lam').Nonempty) := by
  classical
  constructor
  · intro hne
    let φ : (Fin m ⊕ Fin n) ⊕ Bool → PolyPoint m n →ₗ[ℝ] ℝ :=
      Sum.elim faceIneq (fun t => cond t (qdot a - ql) ql)
    let c : (Fin m ⊕ Fin n) ⊕ Bool → ℝ := Sum.elim (fun _ => 0) (fun t => cond t 0 lam')
    have hS : PmaxFeas A a b M N lam' =
        {p | (∀ k, c k ≤ φ k p) ∧ ∀ k, faceEq A b M N k p = faceEqRhs M N k} := by
      ext p
      simp only [PmaxFeas, Set.mem_setOf_eq, mem_PFace_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        refine ⟨fun k => ?_, h2⟩
        rcases k with k | t
        · exact h1 k
        · cases t
          · exact h4
          · show (0 : ℝ) ≤ p.2.1 ⬝ᵥ a - p.1
            linarith
      · rintro ⟨h1, h2⟩
        refine ⟨⟨fun k => h1 (Sum.inl k), h2⟩, ?_, h1 (Sum.inr false)⟩
        have := h1 (Sum.inr true)
        change (0 : ℝ) ≤ p.2.1 ⬝ᵥ a - p.1 at this
        linarith
    have hline : ∀ p ∈ PmaxFeas A a b M N lam', ∀ d : PolyPoint m n,
        (∀ t : ℝ, p + t • d ∈ PmaxFeas A a b M N lam') → d = 0 := by
      intro p _ d hd
      refine face_line hn A b M N p d (fun t => (hd t).1) ?_
      refine slope_zero_of_nonneg (p.1 - lam') d.1 (fun t => ?_)
      have := (hd t).2.2
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
      linarith
    have hbdd : ∀ p ∈ PmaxFeas A a b M N lam', (0 : ℝ) ≤ (qdot a - ql : PolyPoint m n →ₗ[ℝ] ℝ) p := by
      intro p hp
      show 0 ≤ p.2.1 ⬝ᵥ a - p.1
      linarith [hp.2.1]
    obtain ⟨p, hpext, hpmin⟩ := exists_extreme_min_eq _ _ _ _ (qdot a - ql)
      (PmaxFeas A a b M N lam') hS hne hline _ hbdd
    refine ⟨p, ⟨extremePoints_subset hpext, ⟨p, extremePoints_subset hpext, rfl⟩, ?_⟩, hpext⟩
    rintro _ ⟨q, hq, rfl⟩
    have := hpmin q hq
    change p.2.1 ⬝ᵥ a - p.1 ≤ q.2.1 ⬝ᵥ a - q.1 at this
    show q.1 - q.2.1 ⬝ᵥ a ≤ p.1 - p.2.1 ⬝ᵥ a
    linarith
  · intro hne
    let φ : (Fin m ⊕ Fin n) ⊕ Bool → PolyPoint m n →ₗ[ℝ] ℝ :=
      Sum.elim faceIneq (fun t => cond t (ql - qdot a) (-ql))
    let c : (Fin m ⊕ Fin n) ⊕ Bool → ℝ := Sum.elim (fun _ => 0) (fun t => cond t 0 (-lam'))
    have hS : PminFeas A a b M N lam' =
        {p | (∀ k, c k ≤ φ k p) ∧ ∀ k, faceEq A b M N k p = faceEqRhs M N k} := by
      ext p
      simp only [PminFeas, Set.mem_setOf_eq, mem_PFace_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        refine ⟨fun k => ?_, h2⟩
        rcases k with k | t
        · exact h1 k
        · cases t
          · show -lam' ≤ -p.1
            linarith
          · show (0 : ℝ) ≤ p.1 - p.2.1 ⬝ᵥ a
            linarith
      · rintro ⟨h1, h2⟩
        refine ⟨⟨fun k => h1 (Sum.inl k), h2⟩, ?_, ?_⟩
        · have := h1 (Sum.inr true)
          change (0 : ℝ) ≤ p.1 - p.2.1 ⬝ᵥ a at this
          linarith
        · have := h1 (Sum.inr false)
          change -lam' ≤ -p.1 at this
          linarith
    have hline : ∀ p ∈ PminFeas A a b M N lam', ∀ d : PolyPoint m n,
        (∀ t : ℝ, p + t • d ∈ PminFeas A a b M N lam') → d = 0 := by
      intro p _ d hd
      refine face_line hn A b M N p d (fun t => (hd t).1) ?_
      refine slope_zero_of_le p.1 d.1 lam' (fun t => ?_)
      have := (hd t).2.2
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
      linarith
    have hbdd : ∀ p ∈ PminFeas A a b M N lam', (0 : ℝ) ≤ (ql - qdot a : PolyPoint m n →ₗ[ℝ] ℝ) p := by
      intro p hp
      show 0 ≤ p.1 - p.2.1 ⬝ᵥ a
      linarith [hp.2.1]
    obtain ⟨p, hpext, hpmin⟩ := exists_extreme_min_eq _ _ _ _ (ql - qdot a)
      (PminFeas A a b M N lam') hS hne hline _ hbdd
    refine ⟨p, ⟨extremePoints_subset hpext, ⟨p, extremePoints_subset hpext, rfl⟩, ?_⟩, hpext⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hpmin q hq

theorem br (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) :
    ((PFace A b M N).Nonempty →
      BddAbove ((fun q : PolyPoint m n => q.1) '' PFace A b M N) →
      (BRmaxExtreme A b M N).Nonempty) ∧
    ((PFace A b M N).Nonempty →
      BddBelow ((fun q : PolyPoint m n => q.1) '' PFace A b M N) →
      (BRminExtreme A b M N).Nonempty) := by
  classical
  have hS : PFace A b M N =
      {p | (∀ k, (0 : ℝ) ≤ faceIneq k p) ∧ ∀ k, faceEq A b M N k p = faceEqRhs M N k} := by
    ext p; exact mem_PFace_iff A b M N p
  constructor
  · rintro hne ⟨U, hU⟩
    have hline : ∀ p ∈ PFace A b M N, ∀ d : PolyPoint m n,
        (∀ t : ℝ, p + t • d ∈ PFace A b M N) → d = 0 := by
      intro p _ d hd
      refine face_line hn A b M N p d hd ?_
      refine slope_zero_of_le p.1 d.1 U (fun t => ?_)
      have := hU ⟨_, hd t, rfl⟩
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
      linarith
    have hbdd : ∀ p ∈ PFace A b M N, -U ≤ (-ql : PolyPoint m n →ₗ[ℝ] ℝ) p := by
      intro p hp
      have := hU ⟨p, hp, rfl⟩
      show -U ≤ -p.1
      linarith
    obtain ⟨p, hpext, hpmin⟩ := exists_extreme_min_eq _ _ _ _ (-ql) (PFace A b M N) hS hne
      hline _ hbdd
    refine ⟨p, ⟨extremePoints_subset hpext, ⟨p, extremePoints_subset hpext, rfl⟩, ?_⟩, hpext⟩
    rintro _ ⟨q, hq, rfl⟩
    have := hpmin q hq
    change -p.1 ≤ -q.1 at this
    show q.1 ≤ p.1
    linarith
  · rintro hne ⟨L, hL⟩
    have hline : ∀ p ∈ PFace A b M N, ∀ d : PolyPoint m n,
        (∀ t : ℝ, p + t • d ∈ PFace A b M N) → d = 0 := by
      intro p _ d hd
      refine face_line hn A b M N p d hd ?_
      refine slope_zero_of_nonneg (p.1 - L) d.1 (fun t => ?_)
      have := hL ⟨_, hd t, rfl⟩
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
      linarith
    have hbdd : ∀ p ∈ PFace A b M N, L ≤ (ql : PolyPoint m n →ₗ[ℝ] ℝ) p := by
      intro p hp
      exact hL ⟨p, hp, rfl⟩
    obtain ⟨p, hpext, hpmin⟩ := exists_extreme_min_eq _ _ _ _ ql (PFace A b M N) hS hne
      hline _ hbdd
    refine ⟨p, ⟨extremePoints_subset hpext, ⟨p, extremePoints_subset hpext, rfl⟩, ?_⟩, hpext⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hpmin q hq

end R1BSLP


open RankOneBimatrix.BinSearch in
theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) :
    ((PFace A b M N).Nonempty →
      BddAbove ((fun q : PolyPoint m n => q.1) '' PFace A b M N) →
      (BRmaxExtreme A b M N).Nonempty) ∧
    ((PFace A b M N).Nonempty →
      BddBelow ((fun q : PolyPoint m n => q.1) '' PFace A b M N) →
      (BRminExtreme A b M N).Nonempty) := R1BSLP.br hm hn A b M N
