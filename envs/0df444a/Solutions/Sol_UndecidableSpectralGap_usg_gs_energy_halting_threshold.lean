-- Prove2me | solution 1 for UndecidableSpectralGap.usg_gs_energy_halting_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T13:44:57.680835+00:00
-- url     : https://prove2.me/submissions/bd7effd7-f37c-4d6e-a809-8b1ff204de53

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UsgCornerModel

open UndecidableSpectralGap Matrix

/-! ### Diagonal interactions produce diagonal lattice Hamiltonians -/

/-- A two-body interaction that is diagonal in the product basis embeds as a diagonal
matrix on the lattice. -/
lemma embedTwo_diagonal {L d : ℕ} (p q : Site L) (v : Fin d × Fin d → ℂ) :
    embedTwo p q (Matrix.diagonal v)
      = Matrix.diagonal (fun cfg : Config L d => v (cfg p, cfg q)) := by
  ext c c'
  by_cases hcc : c = c'
  · subst hcc
    unfold embedTwo
    simp
  · have h1 : Matrix.diagonal (fun cfg : Config L d => v (cfg p, cfg q)) c c' = 0 :=
      Matrix.diagonal_apply_ne _ hcc
    rw [h1]
    unfold embedTwo
    split_ifs with hagree
    · by_cases hpq : (c p, c q) = (c' p, c' q)
      · exfalso
        apply hcc
        funext s
        by_cases hsp : s = p
        · subst hsp; exact congrArg Prod.fst hpq
        · by_cases hsq : s = q
          · subst hsq; exact congrArg Prod.snd hpq
          · exact hagree s hsp hsq
      · exact Matrix.diagonal_apply_ne _ hpq
    · rfl

lemma embedOne_zero {L d : ℕ} (p : Site L) :
    embedOne p (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  ext c c'
  simp [embedOne]

lemma sum_diagonal {ι κ : Type*} [Fintype ι] [DecidableEq ι] (s : Finset κ)
    (f : κ → ι → ℂ) :
    (∑ e ∈ s, Matrix.diagonal (f e)) = Matrix.diagonal (fun i => ∑ e ∈ s, f e i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih, Matrix.diagonal_add]

/-- The lattice Hamiltonian built from a diagonal interaction and no on-site term is
diagonal, with the classical energy function on its diagonal. -/
lemma latticeHam_diagonal {L d : ℕ} (v : Fin d × Fin d → ℂ) :
    latticeHam L d 0 (Matrix.diagonal v) (Matrix.diagonal v)
      = Matrix.diagonal (fun cfg : Config L d =>
          (∑ e ∈ rowEdges L, v (cfg e.1, cfg e.2))
            + ∑ e ∈ colEdges L, v (cfg e.1, cfg e.2)) := by
  unfold latticeHam
  simp only [embedTwo_diagonal, embedOne_zero, Finset.sum_const_zero, add_zero]
  rw [sum_diagonal, sum_diagonal, ← Matrix.diagonal_add]

lemma latticeHam_zero {L d : ℕ} :
    latticeHam L d (0 : Matrix (Fin d) (Fin d) ℂ) 0 0 = 0 := by
  have h : (0 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      = Matrix.diagonal (fun _ => (0 : ℂ)) := by simp
  rw [h, latticeHam_diagonal]
  simp

/-! ### Spectrum and eigenspaces of a real diagonal matrix -/

lemma specReal_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) :
    specReal (Matrix.diagonal (fun i => ((E i : ℝ) : ℂ))) = Set.range E := by
  ext μ
  simp only [specReal, Set.mem_setOf_eq, spectrum_diagonal, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, by exact_mod_cast hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by exact_mod_cast hi⟩

lemma eigMultiplicity_diagonal_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (μ : ℝ) (i₀ : ι) (h : ∀ i, E i = μ ↔ i = i₀) :
    eigMultiplicity (Matrix.diagonal (fun i => ((E i : ℝ) : ℂ))) μ = 1 := by
  have hspan : Module.End.eigenspace
      (Matrix.toLin' (Matrix.diagonal (fun i => ((E i : ℝ) : ℂ)))) ((μ : ℝ) : ℂ)
      = Submodule.span ℂ {Pi.single i₀ (1 : ℂ)} := by
    apply le_antisymm
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      have hx' : ∀ i, ((E i : ℝ) : ℂ) * x i = ((μ : ℝ) : ℂ) * x i := by
        intro i
        have := congrFun hx i
        simpa [Matrix.toLin'_apply, Matrix.mulVec_diagonal] using this
      have hxeq : x = x i₀ • Pi.single i₀ (1 : ℂ) := by
        funext i
        by_cases hi : i = i₀
        · subst hi; simp
        · have hEi : ((E i : ℝ) : ℂ) ≠ ((μ : ℝ) : ℂ) := by
            intro hc
            exact hi ((h i).1 (by exact_mod_cast hc))
          have hxi : x i = 0 := by
            rcases mul_eq_mul_right_iff.1 (hx' i) with h1 | h1
            · exact absurd h1 hEi
            · exact h1
          simp [hxi, hi]
      rw [hxeq]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        Module.End.mem_eigenspace_iff]
      funext i
      simp only [Matrix.toLin'_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = i₀
      · subst hi
        rw [(h i).2 rfl]
      · simp [hi]
  have hne : (Pi.single i₀ (1 : ℂ) : ι → ℂ) ≠ 0 := by
    intro hc
    have h0 := congrFun hc i₀
    simp at h0
  unfold eigMultiplicity
  rw [hspan]
  exact finrank_span_singleton hne

/-! ### The corner model -/

/-- Indicator of the marker level. -/
def ind2 (a : Fin 2) : ℝ := if a = 1 then 1 else 0

/-- The classical nearest-neighbour interaction of the corner model: a marker at the right
(resp. lower) end of an edge costs `4`, a marker at the left (resp. upper) end pays `-1`. -/
def fr (p : Fin 2 × Fin 2) : ℝ := if p.2 = 1 then 4 else if p.1 = 1 then -1 else 0

lemma fr_lb (a b : Fin 2) : 4 * ind2 b - ind2 a ≤ fr (a, b) := by
  fin_cases a <;> fin_cases b <;> norm_num [fr, ind2]

lemma fr_zero_zero : fr (0, 0) = 0 := by norm_num [fr]

lemma fr_one_zero : fr (1, 0) = -1 := by norm_num [fr]

lemma ind2_nonneg (a : Fin 2) : 0 ≤ ind2 a := by
  unfold ind2; split <;> norm_num

lemma fin2_eq_zero_of_ne_one {a : Fin 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a
  · rfl
  · exact absurd rfl h

/-- The classical energy of a configuration of the corner model. -/
def energy (L : ℕ) (cfg : Config L 2) : ℝ :=
  (∑ e ∈ rowEdges L, fr (cfg e.1, cfg e.2)) + ∑ e ∈ colEdges L, fr (cfg e.1, cfg e.2)

/-- The interaction matrix of the corner model. -/
def Mcorner : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun p => ((fr p : ℝ) : ℂ))

lemma Mcorner_isHermitian : Mcorner.IsHermitian := by
  unfold Matrix.IsHermitian Mcorner
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp [Complex.conj_ofReal]

lemma latticeHam_corner {L : ℕ} :
    latticeHam L 2 0 Mcorner Mcorner
      = Matrix.diagonal (fun cfg : Config L 2 => ((energy L cfg : ℝ) : ℂ)) := by
  unfold Mcorner
  rw [latticeHam_diagonal]
  congr 1
  funext cfg
  unfold energy
  push_cast
  ring

/-! ### Combinatorics of the corner model -/

lemma mem_rowEdges {L : ℕ} {e : Site L × Site L} :
    e ∈ rowEdges L ↔ e.1.1 = e.2.1 ∧ (e.1.2 : ℕ) + 1 = (e.2.2 : ℕ) := by
  simp [rowEdges]

lemma mem_colEdges {L : ℕ} {e : Site L × Site L} :
    e ∈ colEdges L ↔ e.1.2 = e.2.2 ∧ (e.1.1 : ℕ) + 1 = (e.2.1 : ℕ) := by
  simp [colEdges]

lemma rowEdges_injOn_fst {L : ℕ} :
    Set.InjOn Prod.fst (rowEdges L : Set (Site L × Site L)) := by
  intro e he e' he' h
  rw [Finset.mem_coe, mem_rowEdges] at he he'
  have hc : (e.1.2 : ℕ) = (e'.1.2 : ℕ) := by rw [h]
  refine Prod.ext h (Prod.ext ?_ ?_)
  · rw [← he.1, ← he'.1, h]
  · exact Fin.ext (by omega)

lemma rowEdges_injOn_snd {L : ℕ} :
    Set.InjOn Prod.snd (rowEdges L : Set (Site L × Site L)) := by
  intro e he e' he' h
  rw [Finset.mem_coe, mem_rowEdges] at he he'
  have hc : (e.2.2 : ℕ) = (e'.2.2 : ℕ) := by rw [h]
  have h1 : e.1 = e'.1 := by
    refine Prod.ext ?_ (Fin.ext (by omega))
    rw [he.1, he'.1, h]
  exact Prod.ext h1 h

lemma colEdges_injOn_fst {L : ℕ} :
    Set.InjOn Prod.fst (colEdges L : Set (Site L × Site L)) := by
  intro e he e' he' h
  rw [Finset.mem_coe, mem_colEdges] at he he'
  have hc : (e.1.1 : ℕ) = (e'.1.1 : ℕ) := by rw [h]
  refine Prod.ext h (Prod.ext ?_ ?_)
  · exact Fin.ext (by omega)
  · rw [← he.1, ← he'.1, h]

lemma colEdges_injOn_snd {L : ℕ} :
    Set.InjOn Prod.snd (colEdges L : Set (Site L × Site L)) := by
  intro e he e' he' h
  rw [Finset.mem_coe, mem_colEdges] at he he'
  have hc : (e.2.1 : ℕ) = (e'.2.1 : ℕ) := by rw [h]
  have h1 : e.1 = e'.1 := by
    refine Prod.ext (Fin.ext (by omega)) ?_
    rw [he.1, he'.1, h]
  exact Prod.ext h1 h

/-- Sites that are the right end of a horizontal edge. -/
def rowT (L : ℕ) : Finset (Site L) := Finset.univ.filter fun s : Site L => (s.2 : ℕ) ≠ 0

/-- Sites that are the lower end of a vertical edge. -/
def colT (L : ℕ) : Finset (Site L) := Finset.univ.filter fun s : Site L => (s.1 : ℕ) ≠ 0

lemma rowTargets_subset {L : ℕ} : rowT L ⊆ (rowEdges L).image Prod.snd := by
  intro q hq
  simp only [rowT, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  refine Finset.mem_image.2 ⟨((q.1, ⟨(q.2 : ℕ) - 1, by omega⟩), q), ?_, rfl⟩
  rw [mem_rowEdges]
  exact ⟨rfl, by simp; omega⟩

lemma colTargets_subset {L : ℕ} : colT L ⊆ (colEdges L).image Prod.snd := by
  intro q hq
  simp only [colT, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  refine Finset.mem_image.2 ⟨((⟨(q.1 : ℕ) - 1, by omega⟩, q.2), q), ?_, rfl⟩
  rw [mem_colEdges]
  exact ⟨rfl, by simp; omega⟩

lemma sum_fst_le_row {L : ℕ} (g : Site L → ℝ) (hg : ∀ s, 0 ≤ g s) :
    ∑ e ∈ rowEdges L, g e.1 ≤ ∑ s : Site L, g s := by
  rw [← Finset.sum_image (g := Prod.fst) (f := g) rowEdges_injOn_fst]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hg i)

lemma sum_fst_le_col {L : ℕ} (g : Site L → ℝ) (hg : ∀ s, 0 ≤ g s) :
    ∑ e ∈ colEdges L, g e.1 ≤ ∑ s : Site L, g s := by
  rw [← Finset.sum_image (g := Prod.fst) (f := g) colEdges_injOn_fst]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hg i)

lemma sum_snd_ge_row {L : ℕ} (g : Site L → ℝ) (hg : ∀ s, 0 ≤ g s) :
    ∑ s ∈ rowT L, g s ≤ ∑ e ∈ rowEdges L, g e.2 := by
  rw [← Finset.sum_image (g := Prod.snd) (f := g) rowEdges_injOn_snd]
  exact Finset.sum_le_sum_of_subset_of_nonneg rowTargets_subset (fun i _ _ => hg i)

lemma sum_snd_ge_col {L : ℕ} (g : Site L → ℝ) (hg : ∀ s, 0 ≤ g s) :
    ∑ s ∈ colT L, g s ≤ ∑ e ∈ colEdges L, g e.2 := by
  rw [← Finset.sum_image (g := Prod.snd) (f := g) colEdges_injOn_snd]
  exact Finset.sum_le_sum_of_subset_of_nonneg colTargets_subset (fun i _ _ => hg i)

lemma rowT_union_colT {L : ℕ} (hL : 0 < L) :
    rowT L ∪ colT L = Finset.univ.erase ((⟨0, hL⟩, ⟨0, hL⟩) : Site L) := by
  ext s
  simp only [rowT, colT, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, and_true, ne_eq, Prod.ext_iff, Fin.ext_iff]
  omega

lemma union_bound {L : ℕ} (hL : 0 < L) (g : Site L → ℝ) (hg : ∀ s, 0 ≤ g s) :
    (∑ s : Site L, g s) - g ((⟨0, hL⟩, ⟨0, hL⟩) : Site L)
      ≤ (∑ s ∈ rowT L, g s) + (∑ s ∈ colT L, g s) := by
  have hinter : 0 ≤ ∑ s ∈ rowT L ∩ colT L, g s :=
    Finset.sum_nonneg fun i _ => hg i
  have hui := Finset.sum_union_inter (s₁ := rowT L) (s₂ := colT L) (f := g)
  have herase : ∑ s ∈ Finset.univ.erase ((⟨0, hL⟩, ⟨0, hL⟩) : Site L), g s
      = (∑ s : Site L, g s) - g ((⟨0, hL⟩, ⟨0, hL⟩) : Site L) :=
    Finset.sum_erase_eq_sub (Finset.mem_univ _)
  rw [rowT_union_colT hL, herase] at hui
  linarith

/-- The basic energy bound: `E(cfg) ≥ 2·|S| - 4·[corner marked]`, where `|S|` is the number
of marked sites. -/
lemma energy_ge {L : ℕ} (hL : 0 < L) (cfg : Config L 2) :
    2 * (∑ s : Site L, ind2 (cfg s)) - 4 * ind2 (cfg ((⟨0, hL⟩, ⟨0, hL⟩) : Site L))
      ≤ energy L cfg := by
  have hg : ∀ s : Site L, 0 ≤ ind2 (cfg s) := fun s => ind2_nonneg _
  have hrow : 4 * (∑ s ∈ rowT L, ind2 (cfg s)) - (∑ s : Site L, ind2 (cfg s))
      ≤ ∑ e ∈ rowEdges L, fr (cfg e.1, cfg e.2) := by
    have h1 := sum_snd_ge_row (fun s => ind2 (cfg s)) hg
    have h2 := sum_fst_le_row (fun s => ind2 (cfg s)) hg
    have h3 : ∑ e ∈ rowEdges L, (4 * ind2 (cfg e.2) - ind2 (cfg e.1))
        ≤ ∑ e ∈ rowEdges L, fr (cfg e.1, cfg e.2) :=
      Finset.sum_le_sum fun e _ => fr_lb _ _
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h3
    linarith
  have hcol : 4 * (∑ s ∈ colT L, ind2 (cfg s)) - (∑ s : Site L, ind2 (cfg s))
      ≤ ∑ e ∈ colEdges L, fr (cfg e.1, cfg e.2) := by
    have h1 := sum_snd_ge_col (fun s => ind2 (cfg s)) hg
    have h2 := sum_fst_le_col (fun s => ind2 (cfg s)) hg
    have h3 : ∑ e ∈ colEdges L, (4 * ind2 (cfg e.2) - ind2 (cfg e.1))
        ≤ ∑ e ∈ colEdges L, fr (cfg e.1, cfg e.2) :=
      Finset.sum_le_sum fun e _ => fr_lb _ _
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h3
    linarith
  have hu := union_bound hL (fun s => ind2 (cfg s)) hg
  unfold energy
  linarith

/-- The configuration carrying a single marker in the top-left corner. -/
def gcfg (L : ℕ) : Config L 2 := fun s => if (s.1 : ℕ) = 0 ∧ (s.2 : ℕ) = 0 then 1 else 0

lemma gcfg_corner {L : ℕ} (hL : 0 < L) : gcfg L ((⟨0, hL⟩, ⟨0, hL⟩) : Site L) = 1 := by
  simp [gcfg]

lemma gcfg_other {L : ℕ} (hL : 0 < L) (s : Site L) (hs : s ≠ (⟨0, hL⟩, ⟨0, hL⟩)) :
    gcfg L s = 0 := by
  have hns : ¬ ((s.1 : ℕ) = 0 ∧ (s.2 : ℕ) = 0) := by
    intro hc
    exact hs (Prod.ext (Fin.ext hc.1) (Fin.ext hc.2))
  simp [gcfg, hns]

lemma energy_nonneg_of_ne {L : ℕ} (hL : 0 < L) (cfg : Config L 2) (hne : cfg ≠ gcfg L) :
    0 ≤ energy L cfg := by
  have key := energy_ge hL cfg
  have hT : (0:ℝ) ≤ ∑ s : Site L, ind2 (cfg s) :=
    Finset.sum_nonneg fun _ _ => ind2_nonneg _
  by_cases h0 : cfg ((⟨0, hL⟩, ⟨0, hL⟩) : Site L) = 1
  · have hex : ∃ s : Site L, s ≠ ((⟨0, hL⟩, ⟨0, hL⟩) : Site L) ∧ cfg s = 1 := by
      by_contra hcon
      have hc : ∀ t : Site L, t ≠ ((⟨0, hL⟩, ⟨0, hL⟩) : Site L) → cfg t ≠ 1 := by
        intro t ht h1
        exact hcon ⟨t, ht, h1⟩
      apply hne
      funext s
      by_cases hs : s = ((⟨0, hL⟩, ⟨0, hL⟩) : Site L)
      · subst hs; rw [h0, gcfg_corner hL]
      · rw [fin2_eq_zero_of_ne_one (hc s hs), gcfg_other hL s hs]
    obtain ⟨s, hs, hs1⟩ := hex
    have hpair : (2:ℝ) ≤ ∑ t : Site L, ind2 (cfg t) := by
      have hle := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({((⟨0, hL⟩, ⟨0, hL⟩) : Site L), s} : Finset (Site L)))
        (fun i _ _ => ind2_nonneg (cfg i))
      rw [Finset.sum_pair (Ne.symm hs)] at hle
      rw [h0, hs1] at hle
      have h11 : ind2 (1 : Fin 2) = 1 := by simp [ind2]
      rw [h11] at hle
      linarith
    have hind : ind2 (cfg ((⟨0, hL⟩, ⟨0, hL⟩) : Site L)) = 1 := by simp [ind2, h0]
    rw [hind] at key
    linarith
  · have hind : ind2 (cfg ((⟨0, hL⟩, ⟨0, hL⟩) : Site L)) = 0 := by simp [ind2, h0]
    rw [hind] at key
    linarith

lemma energy_gcfg {L : ℕ} (hL : 2 ≤ L) : energy L (gcfg L) = -2 := by
  have h0 : 0 < L := by omega
  have h1 : 1 < L := by omega
  set s₀ : Site L := (⟨0, h0⟩, ⟨0, h0⟩) with hs₀
  have hrow : ∑ e ∈ rowEdges L, fr (gcfg L e.1, gcfg L e.2) = -1 := by
    set a : Site L × Site L := (s₀, (⟨0, h0⟩, ⟨1, h1⟩)) with ha
    have hmem : a ∈ rowEdges L := by rw [mem_rowEdges]; exact ⟨rfl, rfl⟩
    have hne2 : a.2 ≠ s₀ := by
      intro hc
      have hval := congrArg (fun p : Site L => (p.2 : ℕ)) hc
      simp [ha, hs₀] at hval
    rw [Finset.sum_eq_single_of_mem a hmem]
    · rw [show a.1 = s₀ from rfl, gcfg_corner h0, gcfg_other h0 _ hne2, fr_one_zero]
    · intro b hb hbne
      rw [mem_rowEdges] at hb
      have hb2 : b.2 ≠ s₀ := by
        intro hc
        have hval : (b.2.2 : ℕ) = 0 := by rw [hc]
        omega
      have hb1 : b.1 ≠ s₀ := by
        intro hc
        apply hbne
        have hb11 : b.1.1 = (⟨0, h0⟩ : Fin L) := by rw [hc]
        have hb12 : (b.1.2 : ℕ) = 0 := by rw [hc]
        have hb2eq : b.2 = ((⟨0, h0⟩, ⟨1, h1⟩) : Site L) := by
          refine Prod.ext ?_ (Fin.ext ?_)
          · rw [← hb.1, hb11]
          · show (b.2.2 : ℕ) = 1
            omega
        exact Prod.ext hc hb2eq
      rw [gcfg_other h0 _ hb1, gcfg_other h0 _ hb2, fr_zero_zero]
  have hcol : ∑ e ∈ colEdges L, fr (gcfg L e.1, gcfg L e.2) = -1 := by
    set a : Site L × Site L := (s₀, (⟨1, h1⟩, ⟨0, h0⟩)) with ha
    have hmem : a ∈ colEdges L := by rw [mem_colEdges]; exact ⟨rfl, rfl⟩
    have hne2 : a.2 ≠ s₀ := by
      intro hc
      have hval := congrArg (fun p : Site L => (p.1 : ℕ)) hc
      simp [ha, hs₀] at hval
    rw [Finset.sum_eq_single_of_mem a hmem]
    · rw [show a.1 = s₀ from rfl, gcfg_corner h0, gcfg_other h0 _ hne2, fr_one_zero]
    · intro b hb hbne
      rw [mem_colEdges] at hb
      have hb2 : b.2 ≠ s₀ := by
        intro hc
        have hval : (b.2.1 : ℕ) = 0 := by rw [hc]
        omega
      have hb1 : b.1 ≠ s₀ := by
        intro hc
        apply hbne
        have hb11 : b.1.2 = (⟨0, h0⟩ : Fin L) := by rw [hc]
        have hb12 : (b.1.1 : ℕ) = 0 := by rw [hc]
        have hb2eq : b.2 = ((⟨1, h1⟩, ⟨0, h0⟩) : Site L) := by
          refine Prod.ext (Fin.ext ?_) ?_
          · show (b.2.1 : ℕ) = 1
            omega
          · rw [← hb.1, hb11]
        exact Prod.ext hc hb2eq
      rw [gcfg_other h0 _ hb1, gcfg_other h0 _ hb2, fr_zero_zero]
  unfold energy
  rw [hrow, hcol]
  norm_num

/-- The energy takes the value `-2` exactly at the corner configuration, and is
non-negative at every other configuration. -/
lemma energy_eq_neg_two_iff {L : ℕ} (hL : 2 ≤ L) (cfg : Config L 2) :
    energy L cfg = -2 ↔ cfg = gcfg L := by
  constructor
  · intro h
    by_contra hne
    have := energy_nonneg_of_ne (by omega) cfg hne
    rw [h] at this
    norm_num at this
  · rintro rfl
    exact energy_gcfg hL

lemma energy_isLeast {L : ℕ} (hL : 2 ≤ L) :
    IsLeast (Set.range (energy L)) (-2) := by
  constructor
  · exact ⟨gcfg L, energy_gcfg hL⟩
  · rintro x ⟨cfg, rfl⟩
    by_cases h : cfg = gcfg L
    · subst h; rw [energy_gcfg hL]
    · have := energy_nonneg_of_ne (by omega) cfg h
      linarith

/-! ### The spectral data of the corner model -/

lemma gsEnergy_corner {L : ℕ} (hL : 2 ≤ L) :
    gsEnergy (latticeHam L 2 0 Mcorner Mcorner) = -2 := by
  rw [latticeHam_corner]
  unfold gsEnergy
  rw [specReal_diagonal]
  exact (energy_isLeast hL).csInf_eq

lemma prod_indicator {L : ℕ} (cfg : Config L 2) :
    (∏ s : Site L, (if cfg s = gcfg L s then (1:ℂ) else 0))
      = if cfg = gcfg L then 1 else 0 := by
  by_cases h : cfg = gcfg L
  · subst h; simp
  · rw [if_neg h]
    have hex : ∃ s, cfg s ≠ gcfg L s := by
      by_contra hc
      exact h (funext fun s => not_not.1 fun hh => hc ⟨s, hh⟩)
    obtain ⟨s, hs⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

end UsgCornerModel

open UndecidableSpectralGap UsgCornerModel Matrix

/-- **Lemma 8 of Cubitt–Pérez-García–Wolf, in the threshold formalisation.** -/
theorem solution (c : Nat.Partrec.Code) :
    ∃ (d : ℕ) (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (L1 : ℕ),
      hrow.IsHermitian ∧ hcol.IsHermitian ∧
      (∀ L ≥ L1, (Nat.Partrec.Code.evaln L c 0).isNone = true →
        gsEnergy (latticeHam L d 0 hrow hcol) = -2 ∧
        GroundStateNondegenerate (latticeHam L d 0 hrow hcol) ∧
        (∀ μ ∈ specReal (latticeHam L d 0 hrow hcol), μ < 0 → μ = -2) ∧
        ∃ w : Site L → (Fin d → ℂ), (∀ s, w s ≠ 0) ∧
          (latticeHam L d 0 hrow hcol).mulVec (fun cfg : Config L d => ∏ s, w s (cfg s))
            = (-2 : ℂ) • (fun cfg : Config L d => ∏ s, w s (cfg s))) ∧
      ((c.eval 0).Dom → ∃ L0 : ℕ, ∀ L > L0, gsEnergy (latticeHam L d 0 hrow hcol) = 0) := by
  by_cases hdom : (c.eval 0).Dom
  · -- The machine halts: take the trivial one-level model.
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 (Part.get_mem hdom)
    refine ⟨1, 0, 0, k, Matrix.isHermitian_zero, Matrix.isHermitian_zero, ?_, ?_⟩
    · intro L hL hnone
      exact absurd (Option.mem_def.1 (Nat.Partrec.Code.evaln_mono hL hk) ▸ hnone)
        (by simp)
    · intro _
      refine ⟨0, fun L _ => ?_⟩
      have hzero : latticeHam L 1 (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0
          = Matrix.diagonal (fun _ : Config L 1 => (((0 : ℝ)) : ℂ)) := by
        rw [latticeHam_zero]
        simp
      rw [hzero]
      unfold gsEnergy
      rw [specReal_diagonal (fun _ : Config L 1 => (0:ℝ))]
      rw [Set.range_const, csInf_singleton]
  · -- The machine does not halt: take the corner model.
    refine ⟨2, Mcorner, Mcorner, 2, Mcorner_isHermitian, Mcorner_isHermitian, ?_, ?_⟩
    · intro L hL _
      have hL0 : 0 < L := by omega
      refine ⟨gsEnergy_corner hL, ?_, ?_, ?_⟩
      · unfold GroundStateNondegenerate
        rw [gsEnergy_corner hL, latticeHam_corner]
        exact eigMultiplicity_diagonal_unique (energy L) (-2) (gcfg L)
          (fun cfg => energy_eq_neg_two_iff hL cfg)
      · intro μ hμ hneg
        rw [latticeHam_corner, specReal_diagonal] at hμ
        obtain ⟨cfg, rfl⟩ := hμ
        by_cases h : cfg = gcfg L
        · subst h; exact energy_gcfg hL
        · exact absurd (energy_nonneg_of_ne hL0 cfg h) (by linarith)
      · refine ⟨fun s => fun i => if i = gcfg L s then (1:ℂ) else 0, fun s hs => ?_, ?_⟩
        · have := congrFun hs (gcfg L s)
          simp at this
        · funext cfg
          rw [latticeHam_corner]
          simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
          rw [prod_indicator cfg]
          by_cases h : cfg = gcfg L
          · subst h
            rw [if_pos rfl, energy_gcfg hL]
            norm_num
          · rw [if_neg h]
            ring
    · intro hd
      exact absurd hd hdom
