-- Prove2me | solution 1 for SteurerHDX.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:52:48.968196+00:00
-- url     : https://prove2.me/submissions/2c04fccd-303e-42d2-b47f-c87f667a7bf1

import Mathlib
import Definitions.Def_SteurerHDX_innerMu
import Definitions.Def_SteurerHDX_walk
import Definitions.Def_SteurerHDX_variance
import Definitions.Def_SteurerHDX_lambdaTwo
import Definitions.Def_GibbsCongestion_dirichletForm

section
set_option autoImplicit false
namespace SteurerHDX.Dev.L21
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

lemma dot_mulVec_comm (S : Matrix ι ι ℝ) (hS : ∀ x y, S x y = S y x) (v w : ι → ℝ) :
    v ⬝ᵥ S *ᵥ w = (S *ᵥ v) ⬝ᵥ w := by
  have h : Sᵀ = S := by ext x y; exact hS y x
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h]

/-- Abstract second-eigenvalue Rayleigh bound. -/
lemma abstract_min_max (S : Matrix ι ι ℝ) (hS : ∀ x y, S x y = S y x)
    (b : ι → ι → ℝ) (lam : ι → ℝ)
    (horth : ∀ i j, b i ⬝ᵥ b j = if i = j then 1 else 0)
    (heig : ∀ j, S *ᵥ b j = lam j • b j)
    (hexp : ∀ g, g = ∑ j, (b j ⬝ᵥ g) • b j)
    (p q : ι) (hpq : p ≠ q) (hp : ∀ j, lam j ≤ lam p) (hq : ∀ j, j ≠ p → lam j ≤ lam q)
    (hle : ∀ g, g ⬝ᵥ S *ᵥ g ≤ g ⬝ᵥ g)
    (u : ι → ℝ) (hu0 : u ≠ 0) (hu : S *ᵥ u = u) :
    (∀ g, u ⬝ᵥ g = 0 → g ⬝ᵥ S *ᵥ g ≤ lam q * (g ⬝ᵥ g)) ∧
    (∃ g, g ≠ 0 ∧ u ⬝ᵥ g = 0 ∧ S *ᵥ g = lam q • g) := by
  have hdg : ∀ g, g ⬝ᵥ g = ∑ j, (b j ⬝ᵥ g) ^ 2 := by
    intro g
    calc g ⬝ᵥ g = g ⬝ᵥ ∑ j, (b j ⬝ᵥ g) • b j := by rw [← hexp g]
      _ = ∑ j, (b j ⬝ᵥ g) ^ 2 := by
        rw [dotProduct_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [dotProduct_smul, dotProduct_comm g (b j), smul_eq_mul, sq]
  have hdS : ∀ g, g ⬝ᵥ S *ᵥ g = ∑ j, lam j * (b j ⬝ᵥ g) ^ 2 := by
    intro g
    have h1 : S *ᵥ g = ∑ j, ((b j ⬝ᵥ g) * lam j) • b j := by
      conv_lhs => rw [hexp g]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, heig, smul_smul]
    rw [h1, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_smul, dotProduct_comm g (b j), smul_eq_mul]; ring
  have hnorm : ∀ j, b j ⬝ᵥ b j = 1 := fun j => by simp [horth]
  have hlamp : lam p ≤ 1 := by
    have := hle (b p)
    rw [heig, dotProduct_smul, hnorm, smul_eq_mul] at this
    linarith
  -- u components
  have hucomp : ∀ j, lam j * (b j ⬝ᵥ u) = b j ⬝ᵥ u := by
    intro j
    have := dot_mulVec_comm S hS (b j) u
    rw [hu, heig, smul_dotProduct, smul_eq_mul] at this
    exact this.symm
  have hlamp1 : lam p = 1 ∨ lam q = lam p := by
    by_cases h : lam q = lam p
    · exact Or.inr h
    · left
      -- some component of u is nonzero
      by_contra hne
      have hall : ∀ j, b j ⬝ᵥ u = 0 := by
        intro j
        have := hucomp j
        have hj : lam j ≠ 1 := by
          intro h1
          have hjp : j = p ∨ lam j ≤ lam q := by
            by_cases hjp : j = p
            · exact Or.inl hjp
            · exact Or.inr (hq j hjp)
          rcases hjp with rfl | hjq
          · exact hne h1
          · have := hp q
            have := hlamp
            have hqp : lam q < lam p := lt_of_le_of_ne (hp q) h
            linarith
        have : (lam j - 1) * (b j ⬝ᵥ u) = 0 := by linarith
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd (by linarith) hj
        · exact h0
      apply hu0
      rw [hexp u]
      simp [hall]
  have hcase : lam q = lam p ∨ (lam p = 1 ∧ lam q < 1 ∧ (∀ j, j ≠ p → b j ⬝ᵥ u = 0) ∧ b p ⬝ᵥ u ≠ 0) := by
    by_cases h : lam q = lam p
    · exact Or.inl h
    · right
      have h1 : lam p = 1 := hlamp1.resolve_right h
      have hqp : lam q < lam p := lt_of_le_of_ne (hp q) h
      have hz : ∀ j, j ≠ p → b j ⬝ᵥ u = 0 := by
        intro j hj
        have h2 := hucomp j
        have h3 := hq j hj
        have : (lam j - 1) * (b j ⬝ᵥ u) = 0 := by linarith
        rcases mul_eq_zero.mp this with h0 | h0
        · exfalso; linarith
        · exact h0
      refine ⟨h1, by linarith, hz, ?_⟩
      intro h0
      apply hu0
      rw [hexp u]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = p
      · subst hj; simp [h0]
      · simp [hz j hj]
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [hdS, hdg, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = p
    · subst hj
      rcases hcase with h | ⟨h1, h2, hz, hne⟩
      · rw [h]
      · have : b j ⬝ᵥ g = 0 := by
          have h4 : u ⬝ᵥ g = (b j ⬝ᵥ u) * (b j ⬝ᵥ g) := by
            conv_lhs => rw [hexp u]
            rw [sum_dotProduct, Finset.sum_eq_single j]
            · rw [smul_dotProduct, smul_eq_mul]
            · intro i _ hi; rw [smul_dotProduct, hz i hi]; simp
            · simp
          rw [hg] at h4
          rcases mul_eq_zero.mp h4.symm with h | h
          · exact absurd h hne
          · exact h
        rw [this]; simp
    · exact mul_le_mul_of_nonneg_right (hq j hj) (sq_nonneg _)
  · rcases hcase with h | ⟨h1, h2, hz, hne⟩
    · by_cases hab : b p ⬝ᵥ u = 0 ∧ b q ⬝ᵥ u = 0
      · refine ⟨b p, ?_, ?_, ?_⟩
        · intro h0; have := hnorm p; rw [h0] at this; simp at this
        · rw [dotProduct_comm]; exact hab.1
        · rw [heig, h]
      · refine ⟨(b q ⬝ᵥ u) • b p - (b p ⬝ᵥ u) • b q, ?_, ?_, ?_⟩
        · intro h0
          apply hab
          have e1 : b p ⬝ᵥ ((b q ⬝ᵥ u) • b p - (b p ⬝ᵥ u) • b q) = b q ⬝ᵥ u := by
            rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hnorm, horth p q, if_neg hpq]; simp
          have e2 : b q ⬝ᵥ ((b q ⬝ᵥ u) • b p - (b p ⬝ᵥ u) • b q) = -(b p ⬝ᵥ u) := by
            rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hnorm, horth q p, if_neg hpq.symm]; simp
          rw [h0] at e1 e2
          simp at e1 e2
          exact ⟨by linarith, e1.symm⟩
        · rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm u (b p),
            dotProduct_comm u (b q)]
          simp only [smul_eq_mul]; ring
        · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, heig, heig, smul_sub,
            smul_smul, smul_smul, smul_smul, smul_smul, ← h]
          congr 1 <;> congr 1 <;> ring
    · refine ⟨b q, ?_, ?_, heig q⟩
      · intro h0; have := hnorm q; rw [h0] at this; simp at this
      · rw [dotProduct_comm]; exact hz q (Ne.symm hpq)

lemma second_eig (S : Matrix ι ι ℝ) (hS : ∀ x y, S x y = S y x) (hH : S.IsHermitian)
    (hcard : 2 ≤ Fintype.card ι)
    (hle : ∀ g, g ⬝ᵥ S *ᵥ g ≤ g ⬝ᵥ g)
    (u : ι → ℝ) (hu0 : u ≠ 0) (hu : S *ᵥ u = u) :
    (∀ g, u ⬝ᵥ g = 0 → g ⬝ᵥ S *ᵥ g ≤ hH.eigenvalues₀ ⟨1, hcard⟩ * (g ⬝ᵥ g)) ∧
    (∃ g, g ≠ 0 ∧ u ⬝ᵥ g = 0 ∧ S *ᵥ g = hH.eigenvalues₀ ⟨1, hcard⟩ • g) := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) with he
  have hidx : ∀ k : Fin (Fintype.card ι), hH.eigenvalues (e k) = hH.eigenvalues₀ k := by
    intro k
    show hH.eigenvalues₀ (e.symm (e k)) = _
    rw [Equiv.symm_apply_apply]
  have h0 : 0 < Fintype.card ι := by omega
  have := abstract_min_max S hS (fun j => ⇑(hH.eigenvectorBasis j)) hH.eigenvalues
    (by
      intro i j
      have := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) i j
      rw [EuclideanSpace.inner_eq_star_dotProduct] at this
      simpa [dotProduct_comm] using this)
    (fun j => hH.mulVec_eigenvectorBasis j)
    (by
      intro g
      have := hH.eigenvectorBasis.sum_repr' (WithLp.toLp 2 g)
      have h2 := congrArg (fun x : EuclideanSpace ℝ ι => (x : ι → ℝ)) this
      simp only at h2
      convert h2.symm using 1
      ext k
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm])
    (e ⟨0, h0⟩) (e ⟨1, hcard⟩)
    (by intro h; have := e.injective h; simp [Fin.ext_iff] at this)
    (by
      intro j
      have h1 : hH.eigenvalues j = hH.eigenvalues₀ (e.symm j) := rfl
      rw [h1, hidx]
      exact hH.eigenvalues₀_antitone (Fin.le_def.mpr (Nat.zero_le _)))
    (by
      intro j hj
      have h1 : hH.eigenvalues j = hH.eigenvalues₀ (e.symm j) := rfl
      rw [h1, hidx]
      refine hH.eigenvalues₀_antitone (Fin.le_def.mpr ?_)
      have : e.symm j ≠ ⟨0, h0⟩ := by
        intro h; apply hj; rw [← h]; simp
      have : (e.symm j).val ≠ 0 := fun h => this (Fin.ext h)
      show 1 ≤ (e.symm j).val
      omega)
    hle u hu0 hu
  rwa [hidx] at this

section concrete
variable (W : Matrix ι ι ℝ) (hdeg : ∀ x, 0 < SteurerHDX.vdeg W x)
include hdeg

lemma sqrt_pos' (x : ι) : 0 < Real.sqrt (SteurerHDX.vdeg W x) := Real.sqrt_pos.mpr (hdeg x)

lemma tot_pos (hcard : 2 ≤ Fintype.card ι) : 0 < ∑ y, SteurerHDX.vdeg W y := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  exact Finset.sum_pos (fun x _ => hdeg x) Finset.univ_nonempty

lemma sym_u : SteurerHDX.symWalk W *ᵥ (fun x => Real.sqrt (SteurerHDX.vdeg W x)) =
    fun x => Real.sqrt (SteurerHDX.vdeg W x) := by
  funext x
  have hx := sqrt_pos' W hdeg x
  simp only [Matrix.mulVec, dotProduct, SteurerHDX.symWalk, Matrix.of_apply]
  have : ∀ y, W x y / (Real.sqrt (SteurerHDX.vdeg W x) * Real.sqrt (SteurerHDX.vdeg W y)) *
      Real.sqrt (SteurerHDX.vdeg W y) = W x y / Real.sqrt (SteurerHDX.vdeg W x) := by
    intro y
    have hy := sqrt_pos' W hdeg y
    field_simp
  simp only [this, ← Finset.sum_div]
  show SteurerHDX.vdeg W x / _ = _
  exact Real.div_sqrt

lemma quad_form (f : ι → ℝ) :
    (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
      SteurerHDX.symWalk W *ᵥ (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) =
    ∑ x, ∑ y, W x y * f x * f y := by
  simp only [Matrix.mulVec, dotProduct, SteurerHDX.symWalk, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hx := sqrt_pos' W hdeg x
  have hy := sqrt_pos' W hdeg y
  field_simp

lemma norm_form (f : ι → ℝ) :
    (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
      (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) = ∑ x, SteurerHDX.vdeg W x * f x ^ 2 := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  have := Real.mul_self_sqrt (hdeg x).le
  calc _ = (Real.sqrt (SteurerHDX.vdeg W x) * Real.sqrt (SteurerHDX.vdeg W x)) * f x ^ 2 := by ring
    _ = _ := by rw [this]

lemma dirichlet_eq (hsymm : ∀ x y, W x y = W y x) (hcard : 2 ≤ Fintype.card ι) (f : ι → ℝ) :
    GibbsCongestion.dirichletForm (SteurerHDX.walk W) (SteurerHDX.statDist W) f f =
      (∑ x, SteurerHDX.vdeg W x * f x ^ 2 - ∑ x, ∑ y, W x y * f x * f y) /
        ∑ y, SteurerHDX.vdeg W y := by
  have hT := tot_pos W hdeg hcard
  unfold GibbsCongestion.dirichletForm
  have h1 : ∀ x y, SteurerHDX.statDist W x * SteurerHDX.walk W x y * (f x - f y) * (f x - f y) =
      (W x y * f x ^ 2 + W x y * f y ^ 2 - 2 * (W x y * f x * f y)) /
        ∑ y, SteurerHDX.vdeg W y := by
    intro x y
    have := (hdeg x).ne'
    simp only [SteurerHDX.statDist, SteurerHDX.walk, Matrix.of_apply]
    field_simp
    ring
  simp only [h1, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have h2 : ∑ x, ∑ y, W x y * f x ^ 2 = ∑ x, SteurerHDX.vdeg W x * f x ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul]; rfl
  have h3 : ∑ x, ∑ y, W x y * f y ^ 2 = ∑ x, SteurerHDX.vdeg W x * f x ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul]
    unfold SteurerHDX.vdeg
    congr 1
    exact Finset.sum_congr rfl fun y _ => hsymm _ _
  rw [h2, h3]
  ring

lemma innerMu_eq (f g : ι → ℝ) :
    SteurerHDX.innerMu W f g = (∑ x, SteurerHDX.vdeg W x * f x * g x) / ∑ y, SteurerHDX.vdeg W y := by
  unfold SteurerHDX.innerMu SteurerHDX.statDist
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma u_dot (f : ι → ℝ) :
    (fun x => Real.sqrt (SteurerHDX.vdeg W x)) ⬝ᵥ (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) =
      ∑ x, SteurerHDX.vdeg W x * f x * 1 := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  have := Real.mul_self_sqrt (hdeg x).le
  calc _ = (Real.sqrt (SteurerHDX.vdeg W x) * Real.sqrt (SteurerHDX.vdeg W x)) * f x * 1 := by ring
    _ = _ := by rw [this]

lemma gg_pos (f : ι → ℝ) (hf : f ≠ 0) :
    0 < (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
      (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) := by
  rw [norm_form W hdeg]
  have hnn : ∀ x, 0 ≤ SteurerHDX.vdeg W x * f x ^ 2 := fun x => mul_nonneg (hdeg x).le (sq_nonneg _)
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h; push Not at h; exact hf (funext h)
  exact lt_of_lt_of_le (mul_pos (hdeg x) (by positivity))
    (Finset.single_le_sum (fun y _ => hnn y) (Finset.mem_univ x))

lemma ratio_eq (hsymm : ∀ x y, W x y = W y x) (hcard : 2 ≤ Fintype.card ι) (f : ι → ℝ) (hf : f ≠ 0) :
    GibbsCongestion.dirichletForm (SteurerHDX.walk W) (SteurerHDX.statDist W) f f /
        SteurerHDX.innerMu W f f =
      1 - ((fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
        SteurerHDX.symWalk W *ᵥ (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x)) /
        ((fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
          (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x)) := by
  have hT := tot_pos W hdeg hcard
  have hgg := gg_pos W hdeg f hf
  rw [quad_form W hdeg] 
  rw [norm_form W hdeg] at hgg ⊢
  rw [dirichlet_eq W hdeg hsymm hcard, innerMu_eq W hdeg]
  have : ∀ x, SteurerHDX.vdeg W x * f x * f x = SteurerHDX.vdeg W x * f x ^ 2 := fun x => by ring
  simp only [this]
  field_simp

lemma part1 (hsymm : ∀ x y, W x y = W y x) (hnn : ∀ x y, 0 ≤ W x y) (hcard : 2 ≤ Fintype.card ι) :
    IsLeast {c : ℝ | ∃ f : ι → ℝ, f ≠ 0 ∧ SteurerHDX.innerMu W f (fun _ => 1) = 0 ∧
        c = GibbsCongestion.dirichletForm (SteurerHDX.walk W) (SteurerHDX.statDist W) f f /
          SteurerHDX.innerMu W f f} (1 - SteurerHDX.lambdaTwo W) := by
  have hT := tot_pos W hdeg hcard
  set S := SteurerHDX.symWalk W with hSdef
  have hSsym : ∀ x y, S x y = S y x := by
    intro x y; simp only [hSdef, SteurerHDX.symWalk, Matrix.of_apply]
    rw [hsymm x y, mul_comm]
  have hH : S.IsHermitian := Matrix.IsHermitian.ext fun i j => by simpa using hSsym j i
  have hlam : SteurerHDX.lambdaTwo W = hH.eigenvalues₀ ⟨1, hcard⟩ := by
    unfold SteurerHDX.lambdaTwo
    rw [dif_pos ⟨hH, hcard⟩]
    rfl
  have hgOf : ∀ g : ι → ℝ, (fun x => Real.sqrt (SteurerHDX.vdeg W x) *
      (g x / Real.sqrt (SteurerHDX.vdeg W x))) = g := by
    intro g; funext x
    have := (sqrt_pos' W hdeg x).ne'
    field_simp
  have hle : ∀ g, g ⬝ᵥ S *ᵥ g ≤ g ⬝ᵥ g := by
    intro g
    have h := hgOf g
    set f : ι → ℝ := fun x => g x / Real.sqrt (SteurerHDX.vdeg W x)
    rw [← h, quad_form W hdeg, norm_form W hdeg]
    have hE : 0 ≤ GibbsCongestion.dirichletForm (SteurerHDX.walk W) (SteurerHDX.statDist W) f f := by
      unfold GibbsCongestion.dirichletForm
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
      have h1 : 0 ≤ SteurerHDX.statDist W x := div_nonneg (hdeg x).le hT.le
      have h2 : 0 ≤ SteurerHDX.walk W x y := div_nonneg (hnn x y) (hdeg x).le
      have := mul_nonneg h1 h2
      nlinarith [mul_self_nonneg (f x - f y)]
    rw [dirichlet_eq W hdeg hsymm hcard] at hE
    have := (div_nonneg_iff.mp hE)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  have hx0 : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x0⟩ := hx0
  have hu0 : (fun x => Real.sqrt (SteurerHDX.vdeg W x)) ≠ 0 := by
    intro h; have := congrFun h x0; exact (sqrt_pos' W hdeg x0).ne' this
  obtain ⟨hA, g0, hg0, hug0, hSg0⟩ := second_eig S hSsym hH hcard hle _ hu0 (sym_u W hdeg)
  rw [hlam]
  have hinner : ∀ f : ι → ℝ, SteurerHDX.innerMu W f (fun _ => 1) =
      ((fun x => Real.sqrt (SteurerHDX.vdeg W x)) ⬝ᵥ
        (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x)) / ∑ y, SteurerHDX.vdeg W y := by
    intro f
    rw [innerMu_eq W hdeg, u_dot W hdeg]
  have hfne : (fun x => g0 x / Real.sqrt (SteurerHDX.vdeg W x)) ≠ 0 := by
    intro h
    apply hg0
    funext x
    have h1 := congrFun h x
    have h2 := (sqrt_pos' W hdeg x).ne'
    simp only [Pi.zero_apply, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 h2
  constructor
  · refine ⟨fun x => g0 x / Real.sqrt (SteurerHDX.vdeg W x), ?_, ?_, ?_⟩
    · exact hfne
    · rw [hinner, hgOf, hug0]; simp
    · have hf := hfne
      rw [ratio_eq W hdeg hsymm hcard _ hf, hgOf, hSg0, dotProduct_smul, smul_eq_mul]
      have hpos : 0 < g0 ⬝ᵥ g0 := by
        refine lt_of_le_of_ne (Finset.sum_nonneg fun x _ => mul_self_nonneg _) ?_
        intro h; exact hg0 (dotProduct_self_eq_zero.mp h.symm)
      field_simp
  · rintro c ⟨f, hf, hf1, rfl⟩
    rw [ratio_eq W hdeg hsymm hcard f hf]
    have hg : (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
        (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) > 0 := gg_pos W hdeg f hf
    have hu : (fun x => Real.sqrt (SteurerHDX.vdeg W x)) ⬝ᵥ
        (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) = 0 := by
      rw [hinner] at hf1
      rcases div_eq_zero_iff.mp hf1 with h | h
      · exact h
      · exact absurd h hT.ne'
    have := hA _ hu
    have h2 : ((fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
        S *ᵥ (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x)) /
        ((fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
          (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x)) ≤ hH.eigenvalues₀ ⟨1, hcard⟩ :=
      (div_le_iff₀ hg).mpr this
    linarith

lemma statDist_sum (hcard : 2 ≤ Fintype.card ι) : ∑ x, SteurerHDX.statDist W x = 1 := by
  have hT := tot_pos W hdeg hcard
  unfold SteurerHDX.statDist
  rw [← Finset.sum_div, div_self hT.ne']

lemma var_eq (hcard : 2 ≤ Fintype.card ι) (f : ι → ℝ) :
    SteurerHDX.variance W f =
      SteurerHDX.innerMu W (fun x => f x - SteurerHDX.innerMu W f (fun _ => 1))
        (fun x => f x - SteurerHDX.innerMu W f (fun _ => 1)) := by
  have hs := statDist_sum W hdeg hcard
  set m := SteurerHDX.innerMu W f (fun _ => 1) with hm
  have hm' : m = ∑ x, SteurerHDX.statDist W x * f x := by
    rw [hm]; unfold SteurerHDX.innerMu; simp
  unfold SteurerHDX.variance SteurerHDX.innerMu
  have h1 : ∀ x y, SteurerHDX.statDist W x * SteurerHDX.statDist W y * (f x - f y) ^ 2 =
      (SteurerHDX.statDist W x * f x ^ 2) * SteurerHDX.statDist W y +
      SteurerHDX.statDist W x * (SteurerHDX.statDist W y * f y ^ 2) -
      2 * ((SteurerHDX.statDist W x * f x) * (SteurerHDX.statDist W y * f y)) := by
    intro x y; ring
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hs, ← hm']
  have h2 : ∀ x, SteurerHDX.statDist W x * (f x - m) * (f x - m) =
      SteurerHDX.statDist W x * f x ^ 2 - 2 * m * (SteurerHDX.statDist W x * f x) +
        m ^ 2 * SteurerHDX.statDist W x := by intro x; ring
  simp only [h2, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hs, ← hm']
  ring

lemma mean_zero (hcard : 2 ≤ Fintype.card ι) (f : ι → ℝ) :
    SteurerHDX.innerMu W (fun x => f x - SteurerHDX.innerMu W f (fun _ => 1)) (fun _ => 1) = 0 := by
  have hs := statDist_sum W hdeg hcard
  set m := SteurerHDX.innerMu W f (fun _ => 1) with hm
  have hm' : m = ∑ x, SteurerHDX.statDist W x * f x := by
    rw [hm]; unfold SteurerHDX.innerMu; simp
  unfold SteurerHDX.innerMu
  have h2 : ∀ x, SteurerHDX.statDist W x * (f x - m) * 1 =
      SteurerHDX.statDist W x * f x - m * SteurerHDX.statDist W x := by intro x; ring
  simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, ← hm']
  ring

lemma dirichlet_shift (f : ι → ℝ) (m : ℝ) :
    GibbsCongestion.dirichletForm (SteurerHDX.walk W) (SteurerHDX.statDist W)
      (fun x => f x - m) (fun x => f x - m) =
    GibbsCongestion.dirichletForm (SteurerHDX.walk W) (SteurerHDX.statDist W) f f := by
  unfold GibbsCongestion.dirichletForm
  simp only [sub_sub_sub_cancel_right]

end concrete

end SteurerHDX.Dev.L21

namespace SteurerHDX
open Matrix

theorem chk_lemma_2_1 {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (hcard : 2 ≤ Fintype.card ι)
    (hsymm : ∀ x y, W x y = W y x) (hnn : ∀ x y, 0 ≤ W x y) (hdeg : ∀ x, 0 < vdeg W x) :
    IsLeast {c : ℝ | ∃ f : ι → ℝ, f ≠ 0 ∧ innerMu W f (fun _ => 1) = 0 ∧
        c = GibbsCongestion.dirichletForm (walk W) (statDist W) f f / innerMu W f f} (1 - lambdaTwo W) ∧
      IsLeast {c : ℝ | ∃ f : ι → ℝ, (∃ x y, f x ≠ f y) ∧
        c = GibbsCongestion.dirichletForm (walk W) (statDist W) f f / variance W f} (1 - lambdaTwo W) := by
  classical
  have hp := Dev.L21.part1 W hdeg hsymm hnn hcard
  have hs := Dev.L21.statDist_sum W hdeg hcard
  refine ⟨hp, ?_, ?_⟩
  · obtain ⟨f0, hf0, h1, hc⟩ := hp.1
    have hnc : ∃ x y, f0 x ≠ f0 y := by
      by_contra h
      push Not at h
      apply hf0
      funext z
      have : innerMu W f0 (fun _ => 1) = f0 z := by
        unfold innerMu
        calc ∑ x, statDist W x * f0 x * 1 = ∑ x, statDist W x * f0 z := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [h x z, mul_one]
          _ = f0 z := by rw [← Finset.sum_mul, hs, one_mul]
      rw [h1] at this
      simpa using this.symm
    refine ⟨f0, hnc, ?_⟩
    have hv := Dev.L21.var_eq W hdeg hcard f0
    rw [h1] at hv
    simp only [sub_zero] at hv
    rw [hv]
    exact hc
  · rintro c ⟨f, ⟨x, y, hxy⟩, rfl⟩
    set m := innerMu W f (fun _ => 1) with hm
    have hf' : (fun z => f z - m) ≠ 0 := by
      intro h
      apply hxy
      have h1 := congrFun h x
      have h2 := congrFun h y
      simp only [Pi.zero_apply, sub_eq_zero] at h1 h2
      rw [h1, h2]
    have := hp.2 ⟨fun z => f z - m, hf', Dev.L21.mean_zero W hdeg hcard f, rfl⟩
    rw [Dev.L21.dirichlet_shift W hdeg f m, ← Dev.L21.var_eq W hdeg hcard f] at this
    exact this

end SteurerHDX
end

theorem solution : type_of% @SteurerHDX.chk_lemma_2_1 := @SteurerHDX.chk_lemma_2_1
